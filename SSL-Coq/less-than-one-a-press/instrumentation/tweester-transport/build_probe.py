"""Unchanged stock-C slices and generated Area-1 terrain for a finite diagnostic.

This is not Clight execution or a controller replay. See README.md for grants.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('goomba_extract', HERE.parent / 'western-goomba-rng/build_probe.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    selection = {k: list(v) for k, v in base.FUNCTIONS.items()
                 if k.startswith('src/engine/') and 'behavior_script' not in k or k == 'src/game/object_helpers.c'}
    selection['src/game/object_helpers.c'] += ['cur_obj_lateral_dist_from_mario_to_home',
        'cur_obj_lateral_dist_to_home', 'cur_obj_angle_to_home']
    selection['src/game/behaviors/tweester.inc.c'] = ['tweester_scale_and_move', 'tweester_act_chase']
    selection['src/game/object_collision.c'] = ['detect_object_hitbox_overlap']
    bodies, manifest = [], []
    for rel, names in selection.items():
        source = (args.source / rel).read_text()
        source_repo = ROOT.parents[2] / 'reference-sm64-decomp'
        pinned = subprocess.check_output(['git', '-c', 'safe.directory=' + str(source_repo),
            '-C', str(source_repo), 'show', base.REVISION + ':' + rel], text=True)
        for name in names:
            body = base.extract(source, name)
            assert body == base.extract(pinned, name)
            bodies.append(body)
            manifest.append({'file': rel, 'function': name, 'sha256': hashlib.sha256(body.encode()).hexdigest()})
    (args.output / 'source_functions.inc').write_text('\n'.join(b[:b.index('{')].strip() + ';' for b in bodies)
        + '\n\n' + '\n\n'.join(bodies) + '\n')
    meshes = []
    for version in ('us', 'jp'):
        text = (ROOT / f'generated/{version}_ssl_collision.v').read_text()
        begin = text.index('Definition v_ssl_seg7_area_1_collision :=')
        end = text.index('\nDefinition ', begin + 1)
        meshes.append([int(a or b) for a, b in re.findall(
            r'Init_int16 \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)', text[begin:end])])
    assert meshes[0] == meshes[1] and meshes[0][0] == 64
    (args.output / 'source_mesh.inc').write_text('static TerrainData source_mesh[] = {\n'
        + ','.join(map(str, meshes[0])) + '\n};\n')
    ast_hashes = {}
    for version in ('us', 'jp'):
        text = (ROOT / f'generated/{version}_behavior_actions.v').read_text()
        for name in ('tweester_act_chase', 'tweester_scale_and_move'):
            begin = text.index('Definition f_' + name + ' :=')
            end = text.index('\nDefinition ', begin + 1)
            ast_hashes[version + ':' + name] = hashlib.sha256(text[begin:end].encode()).hexdigest()
    script = (args.source / 'levels/ssl/script.c').read_text()
    tweesters = [line for line in script.splitlines() if '/*bhv*/ bhvTweester' in line]
    assert len(tweesters) == 3
    for line, xyz, param in zip(tweesters, [(-3600,-200,2940),(1017,-200,3832),(3066,-200,400)], ['0x12','0x19','0x19']):
        assert tuple(map(int, re.search(r'/\*pos\*/\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)', line).groups())) == xyz
        assert 'BPARAM2(' + param + ')' in line
    assert all('ACT_4 | ACT_5 | ACT_6' in line for line in tweesters[1:])
    (args.output / 'source-manifest.json').write_text(json.dumps({
        'revision': base.REVISION, 'functions': manifest, 'mesh_words': len(meshes[0]),
        'generated_behavior_slice_sha256': ast_hashes,
        'scope': 'Unchanged source slices; native finite diagnostic, not a gameplay witness.'}, indent=2) + '\n')
    print(f'Extracted {len(bodies)} stock functions; US/JP Area-1 mesh agrees.')

if __name__ == '__main__':
    main()
