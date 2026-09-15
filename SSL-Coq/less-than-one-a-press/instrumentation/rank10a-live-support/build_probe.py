"""Copy pinned C unchanged; decode both actual generated collision initializers.

Native diagnostic only: not a Clight execution or a controller-reachable state.
"""
import argparse
import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
spec = importlib.util.spec_from_file_location('extractor', HERE.parent / 'western-goomba-rng/build_probe.py')
extractor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extractor)
FUNCTIONS = {
    'src/engine/math_util.c': ['atan2_lookup', 'atan2s', 'vec3f_set', 'vec3f_copy',
        'mtxf_rotate_zxy_and_translate'],
    'src/engine/surface_load.c': ['alloc_surface_node', 'alloc_surface',
        'clear_spatial_partition', 'clear_dynamic_surfaces', 'add_surface_to_cell',
        'min_3', 'max_3', 'lower_cell_index', 'upper_cell_index', 'add_surface',
        'read_surface_data', 'surface_has_force', 'surf_has_no_cam_collision',
        'load_static_surfaces', 'transform_object_vertices', 'load_object_surfaces',
        'load_object_collision_model'],
    'src/engine/surface_collision.c': ['find_wall_collisions_from_list',
        'find_wall_collisions', 'find_floor_from_list', 'find_floor',
        'find_ceil_from_list', 'find_ceil', 'find_water_level'],
    'src/game/object_helpers.c': ['obj_apply_scale_to_matrix',
        'obj_build_transform_from_pos_and_angle', 'dist_between_objects'],
    'src/game/mario.c': ['resolve_and_return_wall_collisions', 'vec3f_find_ceil'],
    'src/game/mario_step.c': ['perform_ground_quarter_step'],
    'src/game/mario_actions_moving.c': ['check_ledge_climb_down'],
    'src/game/object_list_processor.c': ['update_objects_during_time_stop'],
    'src/game/obj_behaviors.c': ['is_point_within_radius_of_mario'],
    'src/game/behaviors/pyramid_elevator.inc.c': ['bhv_pyramid_elevator_loop'],
}

def words(version, name):
    text = (PROJECT / f'generated/{version}_ssl_collision.v').read_text()
    begin = text.index(f'Definition v_{name} :=')
    end = text.index('gvar_readonly', begin)
    return [int(a or b) for a, b in re.findall(
        r'Init_int16 \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)', text[begin:end])]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    pieces, declarations, manifest = [], [], []
    for relative, names in FUNCTIONS.items():
        text = (source / relative).read_text()
        pinned = subprocess.check_output(['git', '-c', f'safe.directory={source}',
            '-C', str(source), 'show', f'{extractor.REVISION}:{relative}'], text=True)
        for name in names:
            body = extractor.extract(text, name)
            assert body == extractor.extract(pinned, name), name
            pieces.append(body)
            declarations.append(body[:body.index('{')].strip() + ';')
            manifest.append(dict(file=relative, function=name,
                sha256=hashlib.sha256(body.encode()).hexdigest()))
    (args.output / 'source_functions.inc').write_text(
        '\n'.join(declarations) + '\n\n' + '\n\n'.join(pieces) + '\n')
    arrays = []
    for name in ['ssl_seg7_area_2_collision', 'ssl_seg7_collision_pyramid_elevator',
                 'ssl_seg7_collision_grindel', 'ssl_seg7_collision_spindel',
                 'ssl_seg7_collision_0702808C']:
        us, jp = words('us', name), words('jp', name)
        assert us == jp and us[0] == 64
        arrays.append('static TerrainData ' + name + '[] = {' + ','.join(map(str, us)) + '};')
    (args.output / 'source_mesh.inc').write_text('\n'.join(arrays) + '\n')
    actors = []
    for version in ('us', 'jp'):
        text = (PROJECT / f'generated/{version}_ssl_script.v').read_text()
        begin = text.index('Definition v_script_func_local_4 :=')
        text = text[begin:text.index('gvar_readonly', begin)]
        tokens = re.findall(r'Init_int32 \(Int.repr (?:\((-?\d+)\)|(-?\d+))\)|'
                            r'Init_addrof _(\w+) \(Ptrofs.repr 0\)', text)
        tokens = [name or int(a or b) for a, b, name in tokens]
        found = []
        for i, token in enumerate(tokens):
            if token in ('bhvGrindel','bhvHorizontalGrindel','bhvSpindel','bhvSSLMovingPyramidWall'):
                cmd = tokens[i-5:i]
                assert cmd[0] >> 24 == 0x24
                def s16(n): return (n+32768)%65536-32768
                found.append((token,[s16(cmd[1]>>16),s16(cmd[1]),s16(cmd[2]>>16)]))
        actors.append(found)
    assert actors[0] == actors[1]
    assert [a[0] for a in actors[0]] == ['bhvGrindel','bhvHorizontalGrindel',
        'bhvHorizontalGrindel','bhvSpindel'] + ['bhvSSLMovingPyramidWall']*4
    (args.output / 'source_actors.inc').write_text('static const s16 actor_positions[][3] = {' +
        ','.join('{'+','.join(map(str,p))+'}' for _,p in actors[0]) + '};\n')
    (args.output / 'source-manifest.json').write_text(json.dumps(dict(
        scope='native unchanged-C diagnostic; explicit fixtures; no controller coverage',
        revision=extractor.REVISION, functions=manifest), indent=2) + '\n')
    print(f'Extracted {len(manifest)} unchanged C functions; US/JP meshes agree', flush=True)

if __name__ == '__main__':
    main()
