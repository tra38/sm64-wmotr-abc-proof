"""Extract stock shell/copy code; the driver supplies helper outcomes, not gameplay."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('extractor', HERE.parent/'western-goomba-rng/build_probe.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
selection = {
    'src/game/mario_step.c': ['perform_ground_step', 'perform_air_step'],
    'src/game/mario_actions_moving.c': ['tilt_body_ground_shell', 'act_riding_shell_ground'],
    'src/game/mario_actions_airborne.c': ['act_riding_shell_air'],
    'src/engine/math_util.c': ['vec3f_copy', 'vec3s_set', 'approach_s32'],
}
out = Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)
repo = ROOT.parents[2]/'reference-sm64-decomp'
bodies, manifest = [], []
for path, names in selection.items():
    pinned = subprocess.check_output(['git', '-c', 'safe.directory='+str(repo), '-C', str(repo),
                                      'show', base.REVISION+':'+path], text=True)
    local = (ROOT/'build/pinned-sm64'/path).read_text()
    for name in names:
        body = base.extract(pinned, name)
        assert body == base.extract(local, name)
        bodies.append(body)
        manifest.append(dict(file=path, function=name, sha256=hashlib.sha256(body.encode()).hexdigest()))
(out/'source_functions.inc').write_text('\n'.join(b[:b.index('{')].strip()+';' for b in bodies)
    +'\n'+'\n\n'.join(bodies)+'\n')
(out/'manifest.json').write_text(json.dumps(dict(revision=base.REVISION, functions=manifest,
    scope='Native helper-outcome diagnostic, not Clight execution or controller reachability'), indent=2)+'\n')
