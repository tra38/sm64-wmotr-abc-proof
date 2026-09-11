"""Check finite conditional trials. A negative result is not route exclusion."""
import argparse
import json
import re
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def records(path):
    rows = []
    for line in path.read_text().splitlines():
        tag, _, rest = line.partition(',')
        fields = dict(piece.split('=', 1) for piece in
                      re.split(r',(?=[A-Za-z][A-Za-z0-9_]*=)', rest) if '=' in piece)
        rows.append((tag.removeprefix('SUPPORT_'), fields))
    return rows


def xyz(text):
    return tuple(map(float, text.strip('()').split(',')))


def check(rows):
    def one(tag):
        matches = [row for name, row in rows if name == tag]
        require(len(matches) == 1, f'exactly one {tag} required')
        return matches[0]
    seed, start, last, release, end, result = map(one, (
        'SEED', 'START', 'LAST_DIALOG', 'RELEASE', 'END', 'RESULT'))
    require(seed['run'] == result['run'] == f"k{seed['kind']}-t{seed['phase']}-p{seed['policy']}",
            'trial identity or declared policy differs')
    require(int(seed['horizon']) == 90, 'wrong search depth')
    require(seed['extraAssumption'] == 'dialog-checkpoint', 'missing diagnostic assumption')
    require(xyz(start['pos']) == xyz(start['display']) == xyz(start['raw']), 'initial gap supplied')
    require(start['depth'] == '-0.5', 'wrong supplied depth')
    require(start['action'] == '20001305' and start['state'] == '1', 'wrong supplied action checkpoint')
    require(last['state'] == '24', 'dialog release not observed in real handler')
    require(release['action'] != '20001305', 'dialog did not release')
    require(float(release['depth']) == -0.5, 'negative depth did not survive dialog')
    require(xyz(release['display'])[1] > xyz(start['display'])[1], 'game did not raise display')
    require(abs(xyz(release['display'])[1]-xyz(start['display'])[1]-0.5*int(result['dialogSinks']))<0.002,
            'display rise differs from the observed actual sink calls')
    queries = [row for tag, row in rows if tag == 'QUERY']
    first = next((q for q in queries if q['timer'] == start['timer'] and q['index'] == '1'), None)
    require(first is not None and int(first['floor'], 16) != 0, 'initial live floor missing')
    require(first['owner'] == seed['owner'], 'initial live query selected a different owner')
    if int(seed['proposedFloor'], 16):
        require(first['floor'] == seed['proposedFloor'], 'proposed live face was not actually selected')
    require(xyz(first['xyz']) == xyz(start['pos']), 'initial wall correction changed proposed pose')
    release_timer = int(release['timer'])
    polls = [row for tag, row in rows if tag == 'POLL']
    require([int(p['timer']) for p in polls] == list(range(release_timer, release_timer + 91)),
            'missing, duplicate or reordered game updates')
    require([int(p['step']) for p in polls] == list(range(91)), 'wrong update indexing')
    require(int(end['timer']) == release_timer+90, 'horizon endpoint missing')
    inputs = [row for tag, row in rows if tag == 'INPUT']
    require([int(p['timer']) for p in inputs] == list(range(release_timer, release_timer+90)),
            'missing or repeated controller updates')
    axes = ((0,0),(-127,0),(127,0),(0,-127),(0,127),(-127,-127),(-127,127),(127,-127),(127,127))
    policy = int(seed['policy'])
    for step, row in enumerate(inputs):
        require(int(row['step']) == step and row['a'] == '0', 'A press or wrong input step')
        require((int(row['x']), int(row['y'])) == axes[policy%9], 'wrong stick policy')
        require(int(row['z']) == bool(policy//9 & 1), 'wrong Z policy')
        require(int(row['b']) == bool(policy//9 & 2 and step%8 == 0), 'wrong B policy')
    require(result['completed'] == '1' and result['updates'] == '90', 'incomplete trial')
    for field in ('lateWrites', 'controllerA', 'pressedA', 'downA'):
        require(result[field] == '0', f'{field} is nonzero')
    resets = [row for tag, row in rows if tag == 'RESET']
    require(not resets or int(resets[0]['timer']) >= release_timer,
            'display was refreshed before dialog release')
    require(not resets or int(result['firstReset']) == int(resets[0]['timer']), 'reset receipt mismatch')
    require(int(result['release']) == release_timer, 'release result mismatch')
    before_reset = rows[:next((i for i, (tag, _) in enumerate(rows) if tag == 'RESET'), len(rows))]
    early_moves = [r for tag, r in before_reset if tag == 'MOVED']
    early_queries = [r for tag, r in before_reset if tag == 'QUERY']
    require(int(result['movesBeforeReset']) == len(early_moves), 'early movement count mismatch')
    require(int(result['missesBeforeReset']) == sum(int(r['floor'], 16) == 0 for r in early_queries),
            'early miss count mismatch')
    require(int(result['retriesBeforeReset']) == sum(r['index'] == '2' for r in early_queries),
            'early retry count mismatch')
    require(int(result['misses']) == sum(int(r['floor'], 16) == 0 for r in queries), 'missing miss evidence')
    require(int(result['retries']) == sum(r['index'] == '2' for r in queries), 'missing retry evidence')
    require(any(q['timer'] == release['timer'] and q['index'] == '1' for q in early_queries),
            'first post-dialog query not observed before refresh')
    for movement in early_moves:
        require(xyz(movement['display']) == xyz(release['display']), 'raised display changed during early move')
        require(xyz(movement['pos']) != xyz(release['pos']), 'claimed early move did not change position')
    outcome = dict(result)
    low_misses = [q for q in queries if q['index'] == '1' and int(q['floor'], 16) == 0
                  and sum((a-b)**2 for a, b in zip(xyz(q['xyz']), (-2200,768,-1024))) < 0.25**2]
    require(int(result['targetCandidates']) <= len(low_misses), 'target claim lacks a low first miss')
    outcome.update(kind=int(seed['kind']), phase=int(seed['phase']), policy=int(seed['policy']),
                   scope='finite conditional dialog checkpoint; no reachability claim',
                   releasePlatform=release['platform'],
                   releasePosition=list(xyz(release['pos'])),
                   firstUnrefreshedMove=list(xyz(early_moves[0]['pos'])) if early_moves else None,
                   lowFirstMisses=len(low_misses),
                   resetDelay=int(result['firstReset'])-release_timer if resets else None)
    return outcome


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('trace', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(records(args.trace))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, sort_keys=True))
