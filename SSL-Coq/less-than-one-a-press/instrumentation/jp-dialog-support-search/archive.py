"""Save or verify all finite receipts. Never promote them to a route theorem."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from check import check, records
from search import HERE, cases


def source_digest(path):
    return hashlib.sha256(path.read_text().encode()).hexdigest()


def verify_archive():
    expected = json.loads((HERE/'expected-results.json').read_text())
    for path, digest in expected['sourceSha256'].items():
        if source_digest(HERE.parent/path) != digest:
            raise ValueError(f'{path}: source differs from the archived experiment (LF normalized)')
    traces = json.loads(gzip.decompress((HERE/'expected-traces.json.gz').read_bytes()))
    expected_cases = {f'k{k}-t{t}-p{p}' for k,t,p in cases()}
    if set(traces) != expected_cases:
        raise ValueError('saved archive does not cover the declared finite search')
    answers = []
    for label in sorted(traces):
        # records also accepts a tiny file-like wrapper to avoid temporary files.
        class Text:
            def read_text(self):
                return traces[label]
        answer = check(records(Text()))
        if answer['run'] != label:
            raise ValueError('archive label differs from the observed trial identity')
        digest = hashlib.sha256(traces[label].encode()).hexdigest()
        if expected['trials'][label] != dict(result=answer, traceSha256=digest):
            raise ValueError(f'{label}: saved summary differs from rechecked observations')
        answers.append(answer)
    print(json.dumps(dict(trials=len(answers), updates=sum(int(a['updates']) for a in answers),
                          lowFirstMisses=sum(a['lowFirstMisses'] for a in answers),
                          targetCandidates=sum(int(a['targetCandidates']) for a in answers),
                          earlyMoves=sum(int(a['movesBeforeReset']) for a in answers)), sort_keys=True))


def save_archive(directory):
    raw = json.loads((directory/'results.json').read_text())
    if len(raw) != len(cases()) or any(r['exit'] != 0 for r in raw):
        raise ValueError('cannot archive an incomplete or failed search')
    traces, trials = {}, {}
    for row in raw:
        path = Path(row['output'])/'trace.txt'
        result = check(records(path))
        text = path.read_text()
        traces[result['run']] = text
        trials[result['run']] = dict(result=result, traceSha256=hashlib.sha256(text.encode()).hexdigest())
    metadata = dict(horizonUpdates=90, nominalSeconds=3, romSha256=
                    '9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317',
                    sourceSha256={str(path.relative_to(HERE.parent)): source_digest(path)
                                  for path in (HERE/'probe.c', HERE/'run.sh',
                                               HERE.parent/'jp-lifecycle/jp_lifecycle_probe.c')},
                    scope='conditional diagnostic starts, finite policies; not exhaustive or clean-reachable',
                    trials=trials)
    (HERE/'expected-traces.json.gz').write_bytes(gzip.compress(json.dumps(traces, sort_keys=True).encode(), mtime=0))
    (HERE/'expected-results.json').write_text(json.dumps(metadata, indent=2, sort_keys=True)+'\n')
    verify_archive()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--save-from', type=Path)
    args = parser.parse_args()
    if args.save_from:
        save_archive(args.save_from)
    else:
        verify_archive()
