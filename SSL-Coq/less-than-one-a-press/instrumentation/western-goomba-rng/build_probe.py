"""Extract unchanged C functions for a bounded native mechanics diagnostic.

This is not the generated Clight program or a retail/controller witness.
The driver declares its omitted callers/world effects. Function text is copied
verbatim from the source tree; the manifest records every extracted slice.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
REVISION = '9921382a68bb0c865e5e45eb594d9c64db59b1af'
FUNCTIONS = {
    'src/engine/math_util.c': ['atan2_lookup', 'atan2s'],
    'src/engine/behavior_script.c': ['random_u16', 'random_float', 'random_sign'],
    'src/engine/surface_load.c': ['alloc_surface_node', 'alloc_surface',
        'add_surface_to_cell', 'min_3', 'max_3', 'lower_cell_index',
        'upper_cell_index', 'add_surface', 'read_surface_data',
        'surface_has_force', 'surf_has_no_cam_collision', 'load_static_surfaces'],
    'src/engine/surface_collision.c': ['find_wall_collisions_from_list',
        'find_wall_collisions', 'find_floor_from_list', 'find_floor',
        'find_water_level'],
    'src/game/object_helpers.c': ['abs_angle_diff', 'approach_s16_symmetric', 'clear_move_flag',
        'cur_obj_rotate_yaw_toward', 'cur_obj_reflect_move_angle_off_wall',
        'apply_drag_to_value', 'cur_obj_apply_drag_xz', 'cur_obj_move_xz',
        'cur_obj_move_update_underwater_flags', 'cur_obj_move_update_ground_air_flags',
        'cur_obj_move_y_and_get_water_level', 'cur_obj_move_y',
        'cur_obj_compute_vel_xz', 'cur_obj_update_floor_height_and_get_floor',
        'cur_obj_detect_steep_floor', 'cur_obj_resolve_wall_collisions',
        'cur_obj_update_floor', 'cur_obj_update_floor_and_resolve_wall_collisions',
        'cur_obj_update_floor_and_walls', 'cur_obj_move_standard'],
    'src/game/obj_behaviors_2.c': ['approach_f32_ptr',
        'obj_forward_vel_approach', 'random_linear_offset', 'obj_random_fixed_turn',
        'obj_update_blinking', 'obj_resolve_object_collisions',
        'obj_bounce_off_walls_edges_objects', 'obj_resolve_collisions_and_turn',
        'treat_far_home_as_mario'],
    'src/game/behaviors/goomba.inc.c': ['goomba_begin_jump', 'goomba_act_walk',
        'goomba_act_jump'],
}


def extract(text, name):
    # Blank comments and literals without changing offsets before balancing.
    masked = re.sub(r'/\*[\s\S]*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"',
                    lambda m: ' ' * len(m[0]), text)
    match = re.search(r'^\w[^;{}\n]*\b' + re.escape(name) +
                      r'\s*\([^;{}]*\)\s*\{', masked, re.M)
    if not match:
        raise ValueError(f'Cannot locate function {name}')
    start = match.start()
    depth = 1
    end = match.end()
    while depth:
        depth += (masked[end] == '{') - (masked[end] == '}')
        end += 1
    return text[start:end]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    pieces, manifest, declarations = [], [], []
    for relative, names in FUNCTIONS.items():
        text = (source / relative).read_text()
        pinned = subprocess.check_output(['git', '-c', f'safe.directory={source}',
            '-C', str(source), 'show', f'{REVISION}:{relative}'], text=True)
        for name in names:
            body = extract(text, name)
            assert body == extract(pinned, name), f'Source differs from pinned revision: {name}'
            if name == 'random_u16':
                (args.output / 'source_rng.inc').write_text(body + '\n')
            else:
                pieces.append(body)
                declarations.append(body[:body.index('{')].strip() + ';')
            manifest.append(dict(file=relative, function=name,
                sha256=hashlib.sha256(body.encode()).hexdigest()))
    (args.output / 'source_functions.inc').write_text(
        '\n'.join(declarations) + '\n\n' + '\n\n'.join(pieces) + '\n')
    # Decode exactly the generated US collision initializer, not a substitute mesh.
    meshes = []
    for version in ('us', 'jp'):
        text = (PROJECT / f'generated/{version}_ssl_collision.v').read_text()
        start = text.index('Definition v_ssl_seg7_area_2_collision :=')
        end = text.index('\nDefinition ', start + 1)
        words = [int(a or b) for a,b in re.findall(
            r'Init_int16 \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)', text[start:end])]
        meshes.append(words)
    assert meshes[0] == meshes[1]
    assert meshes[0][:2] == [64,1080]
    (args.output / 'source_mesh.inc').write_text(
        'static TerrainData source_mesh[] = {\n' +
        ','.join(map(str,meshes[0])) + '\n};\n')
    (args.output / 'source-manifest.json').write_text(json.dumps(dict(
        scope='unchanged source slices; native diagnostic, not Clight execution',
        revision=REVISION, functions=manifest, meshWords=len(meshes[0])), indent=2) + '\n')
    print(f'Extracted {len(manifest)} source functions; generated US/JP mesh agrees')


if __name__ == '__main__':
    main()
