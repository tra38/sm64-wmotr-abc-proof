"""Bounded-memory, crash-consistent trial chunks and retained recipe archive.

HEAD is the commit point. Unreferenced writes are quarantined, never counted.
Default resume hashes/scans ALL committed payloads. Explicit 'latest' only
checks the final chunk and its predecessor metadata, trusting older content.
SHA-256 detects accidental corruption; it is not an authenticated signature.
"""
from collections import Counter
import hashlib
import gzip
import io
import json
import os
from pathlib import Path
import time
import uuid

STATUSES = ('accepted-projection', 'rejected', 'rejected-event', 'rejected-a-history', 'incomplete-budget')
MAX_LINE = 65536
MAX_META = 262144
MAX_CHUNK = 4 * 1024 * 1024


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)+'\n').encode('utf-8')


def seal(value):
    return dict(payload=value, sha256=hashlib.sha256(encoded(value)).hexdigest())


def sync_directory(path):
    # Windows has no portable directory fsync. Files are still fsynced and
    # replaced atomically; sudden hardware/power failure is not simulated.
    if os.name != 'nt':
        fd = os.open(str(path), os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)


def replace_with_retry(source, destination):
    """Bounded retry for Windows file sharing; persistent errors still abort."""
    for attempt in range(8):
        try:
            os.replace(str(source),str(destination))
            return
        except PermissionError as exc:
            if os.name!='nt' or getattr(exc,'winerror',None) not in (5,32,33) or attempt==7:
                raise
            time.sleep(min(.025*2**attempt,.2))


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_name(path.name+'.tmp').open('wb') as f:
        f.write(encoded(value))
        f.flush()
        os.fsync(f.fileno())
    replace_with_retry(path.with_name(path.name+'.tmp'),path)
    sync_directory(path.parent)


class ChunkLedger:
    def __init__(self, root, signature, total_cases, validate, *, resume=False,
                 verify='full', chunk_records=1000, fault=None, read_only=False,
                 codec=None, check=None, reduce_aux=None):
        if verify not in ('full', 'latest') or not 1 <= chunk_records <= 4096:
            raise ValueError('Invalid verification or chunk limit')
        self.root = Path(root)
        self.validate = validate
        self.fault = fault or (lambda stage: None)
        self.read_only = read_only
        self.codec = codec
        self.check = check or (lambda: None)
        self.reduce_aux = reduce_aux
        self.io = dict(bytesRead=0, bytesWritten=0, checkpoints=0, checkpointSeconds=0.)
        self.recovered = []
        self.pending = None
        self.poisoned = False
        self.lock = None
        expected = dict(schema=2, signature=signature, totalCases=total_cases,
                        chunkRecords=chunk_records, maxChunkBytes=MAX_CHUNK,
                        maxRecordBytes=MAX_LINE, retainedFormat='accepted-predecessor-recipes-v1')
        if codec is not None:
            expected.update(schema=3, storage=codec.name,
                            retainedFormat='accepted-case-references-v1')
        if not resume:
            self.root.mkdir(parents=True, exist_ok=False)
        elif not self.root.is_dir():
            raise ValueError('Chunk ledger missing; legacy JSONL needs a separate historical audit')
        try:
            self._lock()
            if not resume:
                atomic_json(self.root/'manifest.json', seal(expected))
                self.manifest_sha = seal(expected)['sha256']
                self.manifest = expected
                self.generation, self.commit_sha = -1, None
                self.state = self._blank()
                atomic_json(self.root/'HEAD.json', seal(self._head()))
            else:
                self.manifest, self.manifest_sha = self._read_sealed(self.root/'manifest.json')
                if self.manifest != expected:
                    raise ValueError('Incompatible signature, enumeration, format or chunk configuration')
                head, _ = self._read_sealed(self.root/'HEAD.json')
                if head['schema'] != expected['schema'] or head['manifestSha256'] != self.manifest_sha:
                    raise ValueError('HEAD/manifest mismatch')
                self.generation, self.commit_sha, self.state = head['generation'], head['commitSha256'], head['state']
                if type(self.generation) is not int or self.generation < -1:
                    raise ValueError('Invalid HEAD generation')
                self._validate_state(self.state)
                self.audit(verify)
            self.committed = json.loads(json.dumps(self.state))
            if not read_only:
                self._recover()
        except BaseException:
            self.close()
            raise

    def _lock(self):
        self.lock = (self.root/'writer.lock').open('a+b')
        if not self.lock.seek(0, os.SEEK_END):
            self.lock.write(b'0')
            self.lock.flush()
        self.lock.seek(0)
        try:
            if os.name == 'nt':
                import msvcrt
                msvcrt.locking(self.lock.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(self.lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise ValueError('Ledger is already open by another writer/auditor') from exc

    def _blank(self):
        names = sorted({j['setup'] for j in self.manifest['signature']['jobOrder']})
        return self._state(0, {n:{} for n in names}, 0)

    def _state(self, cursor, counts, retained, aux=None):
        jobs = len(self.manifest['signature']['jobOrder'])
        result = dict(nextCase=cursor, counts=counts, retained=retained,
                    sampling=dict(nextInputOrdinal=cursor//jobs, nextJobId=cursor%jobs,
                                  order=self.manifest['signature']['order']))
        if self.reduce_aux is not None:
            result['aux'] = json.loads(json.dumps(self.manifest['signature']['initialAux'] if aux is None else aux))
            result['sampling'] = dict(order=self.manifest['signature']['order'],
                                      scheduler='aux', committedAttempts=cursor)
        return result

    def _validate_state(self, state):
        cursor, retained = state['nextCase'], state['retained']
        names = {j['setup'] for j in self.manifest['signature']['jobOrder']}
        if (type(cursor) is not int or not 0 <= cursor <= self.manifest['totalCases']
                or type(retained) is not int or retained < 0 or set(state['counts']) != names):
            raise ValueError('Invalid cursor/archive/count state')
        for counts in state['counts'].values():
            if any(s not in STATUSES or type(n) is not int or n <= 0 for s,n in counts.items()):
                raise ValueError('Invalid status count')
        if (sum(sum(c.values()) for c in state['counts'].values()) != cursor
                or sum(c.get('accepted-projection',0) for c in state['counts'].values()) != retained
                or state != self._state(cursor, state['counts'], retained, state.get('aux'))
                or len(encoded(state)) > MAX_META // 2):
            raise ValueError('Cursor/counts/sampling/archive disagree')

    def _head(self):
        return dict(schema=self.manifest['schema'], manifestSha256=self.manifest_sha,
                    generation=self.generation, commitSha256=self.commit_sha, state=self.state)

    def _read_sealed(self, path):
        self.check()
        with path.open('rb') as f:
            raw = f.read(MAX_META+1)
        self.io['bytesRead'] += len(raw)
        if len(raw)>MAX_META:
            raise ValueError('Metadata exceeds bound')
        value = json.loads(raw)
        if set(value) != {'payload','sha256'} or seal(value['payload']) != value:
            raise ValueError('Metadata checksum differs: '+str(path))
        return value['payload'], value['sha256']

    def _chunk(self, generation):
        return self.root/'chunks'/('%06d'%(generation//1000))/('%010d'%generation)

    def _metadata(self, generation, expected_sha):
        value, digest = self._read_sealed(self._chunk(generation)/'commit.json')
        if digest != expected_sha or value['generation'] != generation or value['manifestSha256'] != self.manifest_sha:
            raise ValueError('Chunk commit/chain differs')
        return value

    def _rows(self, path, expected):
        if self.codec is not None:
            yield from self._compressed_rows(path, expected)
            return
        digest, size, rows = hashlib.sha256(), 0, 0
        with path.open('rb') as f:
            while True:
                self.check()
                line = f.readline(MAX_LINE+1)
                if not line:
                    break
                self.io['bytesRead'] += len(line)
                size += len(line)
                if len(line)>MAX_LINE or not line.endswith(b'\n') or size>MAX_CHUNK:
                    raise ValueError('Oversize/partial chunk record')
                digest.update(line)
                rows += 1
                yield json.loads(line)
        if size != expected['bytes'] or rows != expected['records'] or digest.hexdigest()!=expected['sha256']:
            raise ValueError('Payload hash/size/record count differs: '+str(path))

    def _compressed_rows(self, path, expected):
        self.check()
        # One independently compressed chunk, never a growing-history buffer.
        with path.open('rb') as f:
            raw = f.read(MAX_CHUNK + 65537)
        self.io['bytesRead'] += len(raw)
        if (len(raw) > MAX_CHUNK + 65536 or len(raw) != expected['bytes']
                or hashlib.sha256(raw).hexdigest() != expected['sha256']):
            raise ValueError('Compressed payload hash/size differs: '+str(path))
        digest, size, rows = hashlib.sha256(), 0, 0
        try:
            with gzip.GzipFile(fileobj=io.BytesIO(raw)) as source:
                while True:
                    self.check()
                    line = source.readline(MAX_LINE+1)
                    if not line:
                        break
                    size += len(line)
                    if len(line)>MAX_LINE or not line.endswith(b'\n') or size>MAX_CHUNK:
                        raise ValueError('Oversize/partial decoded record')
                    digest.update(line); rows += 1
                    yield json.loads(line)
        except (OSError, EOFError) as exc:
            raise ValueError('Invalid compressed payload') from exc
        if (size!=expected['rawBytes'] or rows!=expected['records']
                or digest.hexdigest()!=expected['rawSha256']):
            raise ValueError('Decoded payload hash/size/count differs')

    def _payload_name(self, name):
        return name+'.jsonl'+('.gz' if self.codec is not None else '')

    def records(self):
        """Compatibility iterator; use only after the requested audit succeeds."""
        for generation in range(self.generation+1):
            meta, _ = self._read_sealed(self._chunk(generation)/'commit.json')
            for row in self._rows(self._chunk(generation)/self._payload_name('trials'),meta['trials']):
                yield self.codec.decode(row) if self.codec is not None else row

    def _verify_chunk(self, meta, previous):
        self._validate_state(meta['state'])
        count = meta['nextCase']-meta['firstCase']
        if (meta['firstCase']!=previous['nextCase'] or count<=0
                or count>self.manifest['chunkRecords'] or meta['trials']['records']!=count):
            raise ValueError('Chunk range skips or double-counts trials')
        path = self._chunk(meta['generation'])
        archive = self._rows(path/self._payload_name('retained'),meta['retained'])
        counts = {n:Counter(c) for n,c in previous['counts'].items()}
        retained, cursor = previous['retained'], meta['firstCase']
        aux = previous.get('aux')
        for row in self._rows(path/self._payload_name('trials'),meta['trials']):
            record = self.codec.decode(row) if self.codec is not None else row
            self.validate(record, cursor)
            counts[record['setup']][record['status']] += 1
            if record['status']=='accepted-projection':
                if next(archive, None) != ([record['case']] if self.codec is not None else record):
                    raise ValueError('Retained archive is not the accepted trial subsequence')
                retained += 1
            cursor += 1
            if self.reduce_aux is not None:
                aux = self.reduce_aux(aux,record)
        if next(archive, None) is not None:
            raise ValueError('Retained archive has extra candidates')
        expected = self._state(cursor,{n:dict(c) for n,c in counts.items()},retained,aux)
        if expected != meta['state'] or cursor != meta['nextCase']:
            raise ValueError('Recomputed counts/sampling/archive differ from commit')
        return expected

    def audit(self, verify='full'):
        self.check()
        if self.generation == -1:
            if self.commit_sha is not None or self.state != self._blank():
                raise ValueError('Empty HEAD is inconsistent')
            return
        if verify == 'latest':
            meta = self._metadata(self.generation, self.commit_sha)
            previous = (self._metadata(self.generation-1,meta['previousCommitSha256'])['state']
                        if self.generation else self._blank())
            result = self._verify_chunk(meta, previous)
        else:
            result, previous_sha = self._blank(), None
            # Read forwards, bounded memory; never list/sort the entire archive.
            for generation in range(self.generation+1):
                meta, digest = self._read_sealed(self._chunk(generation)/'commit.json')
                if (meta['generation']!=generation or meta['manifestSha256']!=self.manifest_sha
                        or meta['previousCommitSha256']!=previous_sha):
                    raise ValueError('Broken committed chunk chain')
                result = self._verify_chunk(meta,result)
                previous_sha = digest
            if previous_sha != self.commit_sha:
                raise ValueError('Committed chain does not end at HEAD')
        if result != self.state:
            raise ValueError('HEAD differs from verified chunk state')

    def _quarantine(self, path):
        if not path.exists():
            return
        destination = self.root/'recovery'/uuid.uuid4().hex
        destination.parent.mkdir(parents=True,exist_ok=True)
        replace_with_retry(path,destination)
        sync_directory(destination.parent)
        self.recovered.append(str(destination.relative_to(self.root)))

    def _recover(self):
        self._quarantine(self.root/'pending')
        self._quarantine(self.root/'HEAD.json.tmp')
        self._quarantine(self.root/'manifest.json.tmp')
        generation = self.generation+1
        while self._chunk(generation).exists():
            self._quarantine(self._chunk(generation))
            generation += 1

    def _begin(self):
        if self.read_only:
            raise ValueError('Read-only audit cannot append')
        path = self.root/'pending'
        path.mkdir()
        self.pending = dict(firstCase=self.state['nextCase'], records=0, bytes=0,
                            retainedRecords=0, retainedBytes=0,
                            trials= (path/'trials.jsonl').open('wb'),
                            retained= (path/'retained.jsonl').open('wb'),
                            trialsHash=hashlib.sha256(), retainedHash=hashlib.sha256())

    def append(self, record):
        if self.poisoned:
            raise ValueError('Failed transaction; close and resume for recovery')
        try:
            self._append(record)
        except BaseException:
            self.poisoned = True
            raise

    def _append(self, record):
        self.validate(record,self.state['nextCase'])
        line = encoded(self.codec.encode(record) if self.codec is not None else record)
        if len(line)>MAX_LINE:
            raise ValueError('Trial record exceeds bound')
        if self.pending and (self.pending['bytes']+len(line)>MAX_CHUNK
                             or self.pending['records']>=self.manifest['chunkRecords']):
            self.commit()
        if not self.pending:
            self._begin()
        p = self.pending
        p['trials'].write(line)
        p['trialsHash'].update(line)
        p['bytes'] += len(line)
        self.io['bytesWritten'] += len(line)
        self.fault('after_trial_write')
        if record['status']=='accepted-projection':
            retained_line = encoded([record['case']]) if self.codec is not None else line
            p['retained'].write(retained_line)
            p['retainedHash'].update(retained_line)
            p['retainedBytes'] += len(retained_line)
            p['retainedRecords'] += 1
            self.io['bytesWritten'] += len(retained_line)
        self.fault('after_retained_write')
        p['records'] += 1
        counts = {n:dict(c) for n,c in self.state['counts'].items()}
        c = counts[record['setup']]
        c[record['status']] = c.get(record['status'],0)+1
        self.state = self._state(self.state['nextCase']+1,counts,
                                self.state['retained']+(record['status']=='accepted-projection'),
                                self.reduce_aux(self.state['aux'],record) if self.reduce_aux is not None else None)

    def ready(self):
        return self.pending and self.pending['records']>=self.manifest['chunkRecords']

    def commit(self, extra=None):
        if self.poisoned:
            raise ValueError('Failed transaction; close and resume for recovery')
        try:
            self._commit(extra)
        except BaseException:
            self.poisoned = True
            raise

    def _commit(self, extra=None):
        if not self.pending:
            return
        started = time.perf_counter()
        p = self.pending
        self.fault('before_payload_sync')
        for name in ('trials','retained'):
            p[name].flush()
            os.fsync(p[name].fileno())
            p[name].close()
        self.fault('after_payload_sync')
        payloads = {}
        for name, prefix in (('trials',''),('retained','retained')):
            size_key = 'bytes' if not prefix else 'retainedBytes'
            records_key = 'records' if not prefix else 'retainedRecords'
            data = dict(bytes=p[size_key],records=p[records_key],sha256=p[name+'Hash'].hexdigest())
            if self.codec is not None:
                source = self.root/'pending'/(name+'.jsonl')
                destination = self.root/'pending'/self._payload_name(name)
                with source.open('rb') as inp, destination.open('wb') as out:
                    with gzip.GzipFile(filename='',fileobj=out,mode='wb',mtime=0,compresslevel=6) as packed:
                        for block in iter(lambda:inp.read(65536),b''):
                            packed.write(block)
                            self.io['bytesRead'] += len(block)
                    out.flush(); os.fsync(out.fileno())
                raw = destination.read_bytes()  # bounded by this single new chunk
                self.io['bytesRead'] += len(raw); self.io['bytesWritten'] += len(raw)
                data.update(rawBytes=data['bytes'],rawSha256=data['sha256'],
                            bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
                source.unlink()
            payloads[name] = data
        generation = self.generation+1
        meta = dict(generation=generation, manifestSha256=self.manifest_sha,
                    previousCommitSha256=self.commit_sha,
                    firstCase=p['firstCase'], nextCase=self.state['nextCase'], state=self.state,
                    trials=payloads['trials'], retained=payloads['retained'],
                    extra=extra or {})
        if len(encoded(seal(meta)))>MAX_META:
            raise ValueError('Commit metadata exceeds bound')
        atomic_json(self.root/'pending'/'commit.json',seal(meta))
        self.fault('after_commit_metadata')
        destination = self._chunk(generation)
        destination.parent.mkdir(parents=True,exist_ok=True)
        replace_with_retry(self.root/'pending',destination)
        sync_directory(destination.parent)
        self.fault('after_chunk_rename')
        head = dict(schema=self.manifest['schema'], manifestSha256=self.manifest_sha, generation=generation,
                    commitSha256=seal(meta)['sha256'], state=self.state)
        # A fault immediately before/after atomic HEAD replacement tests both
        # sides of the sole transaction commit point.
        self.fault('before_head_replace')
        atomic_json(self.root/'HEAD.json',seal(head))
        self.fault('after_head_replace')
        self.generation, self.commit_sha = generation, head['commitSha256']
        self.committed = json.loads(json.dumps(self.state))
        self.pending = None
        self.io['checkpoints'] += 1
        self.io['checkpointSeconds'] += time.perf_counter()-started

    def close(self):
        if self.pending:
            for name in ('trials','retained'):
                if not self.pending[name].closed:
                    self.pending[name].close()
            self.pending = None
        if self.lock:
            self.lock.close()  # Kernel releases the lock even after a crash.
            self.lock = None

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
