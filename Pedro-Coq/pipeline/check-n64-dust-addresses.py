#!/usr/bin/env python3
"""Read-only authentication of the three dust scripts in clean US/JP ROMs.

Match every scalar initializer from generated Clight, derive segment placement
from the two Mist child references, and cross-check their common ROM base.
Native callback words are recorded as relocations, not proved code semantics.
No emulator, ROM write, or game-memory operation is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
REVISION = '9921382a68bb0c865e5e45eb594d9c64db59b1af'
ROM_HASHES = {
    'us': '17ce077343c6133f8c9f2d6d6d9a4ab62c8cd2aa57c40aea1f490b4c8bb21d91',
    'jp': '9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317',
}
SCRIPTS = ('bhvMistParticleSpawner', 'bhvWhitePuff1', 'bhvWhitePuff2')
ITEM = re.compile(r'Init_int32\s+\(Int.repr\s+(-?\d+)\)|'
                  r'Init_addrof\s+(_\w+)\s+\(Ptrofs.repr\s+(\d+)\)')


def initializers(source, name):
    match = re.search(rf'Definition v_{name} := \{{\|\s*'
                      r'gvar_info := \(tarray tuint (\d+)\);\s*'
                      r'gvar_init := \((.*?)\);', source, re.S)
    if match is None:
        raise ValueError(f'cannot parse generated script {name}')
    body = match[2]
    residue = ITEM.sub('', body).replace('::', '').replace('nil', '').strip()
    if residue:
        raise ValueError(f'unhandled initializer syntax: {residue}')
    items = []
    for item in ITEM.finditer(body):
        if item[1] is not None:
            items.append(int(item[1]) & 0xffffffff)
        else:
            if int(item[3]) != 0:
                raise ValueError('unexpected nonzero relocation offset')
            items.append(item[2])
    if len(items) != int(match[1]):
        raise ValueError('initializer/array size mismatch')
    return items


def locate(image, items):
    # The leading scalar words provide an anchor; all scalar words, including
    # those after relocations, must then match. Ambiguity is an error.
    prefix = []
    for item in items:
        if isinstance(item, str):
            break
        prefix.append(item)
    anchor = struct.pack(f'>{len(prefix)}I', *prefix)
    matches, start = [], 0
    while True:
        offset = image.find(anchor, start)
        if offset < 0:
            break
        start = offset + 1
        end = offset + len(items) * 4
        if offset % 4 or end > len(image):
            continue
        words = list(struct.unpack(f'>{len(items)}I', image[offset:end]))
        if all(isinstance(item, str) or item == word for item, word in zip(items, words)):
            matches.append((offset, words))
    if len(matches) != 1:
        raise ValueError(f'expected one complete scalar match, got {len(matches)}')
    return matches[0]


def collect(decomp):
    linker = subprocess.check_output(['git', '-c', f'safe.directory={decomp.as_posix()}',
                                      '-C', str(decomp), 'show', f'{REVISION}:sm64.ld'])
    if b'BEGIN_SEG(behavior, 0x13000000)' not in linker:
        raise ValueError('pinned linker does not place behavior segment at 0x13000000')
    result = {'schema': 1, 'source_revision': REVISION,
              'linker_sha256': hashlib.sha256(linker).hexdigest(), 'versions': {}}
    for version, digest in ROM_HASHES.items():
        image = (decomp / f'baserom.{version}.z64').read_bytes()
        if hashlib.sha256(image).hexdigest() != digest:
            raise ValueError(f'{version}: clean retail ROM SHA-256 mismatch')
        ast_bytes = (PROJECT / f'generated/{version}_behavior_data.v').read_bytes()
        source = ast_bytes.decode()
        entries = {}
        for script in SCRIPTS:
            items = initializers(source, script)
            offset, words = locate(image, items)
            entries[script] = {
                'rom_offset': offset, 'size': len(items) * 4, 'words': words,
                'relocations': [{'byte_offset': index * 4, 'symbol': item,
                                 'numeric_word': words[index]}
                                for index, item in enumerate(items) if isinstance(item, str)],
            }
        mist = entries[SCRIPTS[0]]
        bases = []
        for reloc in mist['relocations']:
            target = entries[reloc['symbol'][1:]]
            address = reloc['numeric_word']
            if address >> 24 != 19:
                raise ValueError('Mist child reference does not use behavior segment 19')
            target['segment_offset'] = address & 0xffffff
            bases.append(target['rom_offset'] - target['segment_offset'])
        if len(bases) != 2 or bases[0] != bases[1] or bases[0] < 0:
            raise ValueError('Mist child references disagree on the behavior ROM base')
        mist['segment_offset'] = mist['rom_offset'] - bases[0]
        ranges = sorted((entry['segment_offset'], entry['size']) for entry in entries.values())
        if any(start < 0 or start + size > 0x1000000 for start, size in ranges):
            raise ValueError('script extends outside the behavior segment')
        if any(a + size > b for (a, size), (b, _) in zip(ranges, ranges[1:])):
            raise ValueError('overlapping script ranges')
        result['versions'][f'VERSION_{version.upper()}'] = {
            'rom_sha256': digest, 'generated_sha256': hashlib.sha256(ast_bytes).hexdigest(),
            'behavior_rom_base': bases[0], 'scripts': entries,
        }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--decomp', type=Path,
                        default=PROJECT.parent.parent / 'reference-sm64-decomp')
    parser.add_argument('--write', action='store_true', help='write the finite JSON receipt')
    args = parser.parse_args()
    result = collect(args.decomp.resolve())
    proof = (PROJECT / 'proofs/N64AddressRefinement.v').read_text()
    placement = re.search(r'Definition retail_n64_dust_offset script : Z :=\s*'
                          r'match script with N64Mist => (\d+) \| N64Puff1 => (\d+) '
                          r'\| N64Puff2 => (\d+) end\.', proof)
    if placement is None:
        raise ValueError('cannot parse the bounded Coq placement receipt')
    word_proof = (PROJECT / 'proofs/N64DustImage.v').read_text()
    for version, data in result['versions'].items():
        prefix = version.removeprefix('VERSION_').lower()
        for index, (script, tag) in enumerate(zip(SCRIPTS, ('mist', 'puff1', 'puff2'))):
            entry = data['scripts'][script]
            if int(placement[index + 1]) != entry['segment_offset']:
                raise ValueError(f'{version}/{script}: Coq placement mismatch')
            words = re.search(rf'Definition retail_n64_{prefix}_{tag}_words : list Z :=\s*'
                              r'\[([\d;\s]+)\]\.', word_proof)
            if words is None or [int(word) for word in words[1].split(';')] != entry['words']:
                raise ValueError(f'{version}/{script}: Coq word transcription mismatch')
    receipt = PROJECT / 'inputs/n64-dust-addresses.json'
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    elif json.loads(receipt.read_text()) != result:
        raise ValueError('committed N64 dust address receipt differs from authenticated inputs')
    for version, entry in result['versions'].items():
        print(version, 'behavior ROM base', hex(entry['behavior_rom_base']),
              {script: hex(value['segment_offset']) for script, value in entry['scripts'].items()})
    print('Authenticated all six Coq word lists and placements; every scalar initializer and both Mist child relocations agree (US/JP).')


if __name__ == '__main__':
    main()
