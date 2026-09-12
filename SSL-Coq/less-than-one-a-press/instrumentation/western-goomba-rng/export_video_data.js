'use strict';
// Export existing evidence for presentation. No movement is simulated here.
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const {mesh} = require('../rank10a-ground-pound/check_support.js');
const root = path.resolve(__dirname, '../..');
const a = mesh('us', 'v_ssl_seg7_area_2_collision');
assert.deepEqual(a, mesh('jp', 'v_ssl_seg7_area_2_collision'));
const csv = fs.readFileSync(path.join(root, 'build/instrumentation/western-goomba-rng/west-replay-us.csv'));
assert(csv.equals(fs.readFileSync(path.join(root, 'build/instrumentation/western-goomba-rng/west-replay-jp.csv'))));
const rows = csv.toString().trim().split(/\r?\n/).slice(1).map(line => line.split(',').map(Number));
rows.forEach(r => [1,2,3,8].forEach(i => { r[i] = Math.fround(r[i]); }));
assert.equal(rows.length, 901);
assert(rows.every((r, i) => r[0] === i + 1));
assert.deepEqual(rows[846].slice(0, 4), [847, -3196.341552734375, -0, 2895.0380859375]);
const out = path.join(root, 'build/instrumentation/western-goomba-rng/video');
fs.mkdirSync(out, {recursive: true});
const result = {
  scope: 'Reconstruction from the existing native diagnostic; not emulator footage.',
  csvSha256: crypto.createHash('sha256').update(csv).digest('hex'),
  frames: rows, mesh: a,
  stockContext: [
    {name:'Southern Goomba', pos:[-2100,0,3316]},
    {name:'Western Grindel', pos:[-3362,0,-1385]}
  ],
  contextScope:'Stock starting positions only. These actors are absent from this diagnostic.',
  waypoint: {frame:847, position:[-3196.341552734375,0,2895.0380859375]},
  originalRimTarget: [-3071,113,1928],
  grantedMario: [-410,128,700]
};
fs.writeFileSync(path.join(out,'data.json'), JSON.stringify(result));
console.log(JSON.stringify({frames:rows.length, waypoint:result.waypoint, csvSha256:result.csvSha256, out}));
