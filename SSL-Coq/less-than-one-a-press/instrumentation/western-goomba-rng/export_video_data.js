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
// Read the displayed threshold from the actual generated US/JP walk calls.
for (const version of ['us','jp']) {
  const text = fs.readFileSync(path.join(root, `generated/${version}_obj_behaviors_2.v`),'utf8');
  const walk = text.split('Definition f_goomba_act_walk :=')[1].split('\nDefinition ')[0];
  const firstCall = walk.slice(walk.indexOf('fn_body :='), walk.indexOf('fn_body :=')+400);
  assert(firstCall.includes('Evar _treat_far_home_as_mario'));
  assert(firstCall.includes('Float32.of_bits (Int.repr 1148846080)'));
  const home = text.split('Definition f_treat_far_home_as_mario :=')[1].split('\nDefinition ')[0];
  assert(/Ogt \(Etempvar _distance tfloat\)\s*\(Etempvar _threshold tfloat\)/.test(home));
  assert(['_dx','_dy','_dz'].every(n => home.includes(`Omul (Etempvar ${n} tfloat) (Etempvar ${n} tfloat)`)));
}
const bits = Buffer.alloc(4); bits.writeUInt32LE(1148846080);
const homeRadius = bits.readFloatLE(); assert.equal(homeRadius,1000);
const homeCenter = [-3638,0,1928];
const homeDistances = rows.map(r => Math.hypot(...homeCenter.map((v,i) => r[i+1]-v)));
const firstOutside = homeDistances.findIndex(d => d>homeRadius);
const maxHomeIndex = homeDistances.indexOf(Math.max(...homeDistances));
assert.equal(firstOutside+1,757); assert.equal(maxHomeIndex+1,833);
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
  grantedMario: [-410,128,700],
  home: {center:homeCenter,radius:homeRadius,
    scope:'Euclidean distance in all three coordinates; shown circle is the Y=0 slice, not a hard movement boundary.',
    distances:homeDistances,firstOutsideFrame:firstOutside+1,
    maxDistanceFrame:maxHomeIndex+1,maxDistance:homeDistances[maxHomeIndex],
    targetHorizontalDistance:567,targetDistance:Math.hypot(567,113)},
  searchTargetXZ: [-3200,2925]
};
fs.writeFileSync(path.join(out,'data.json'), JSON.stringify(result));
console.log(JSON.stringify({frames:rows.length, waypoint:result.waypoint, csvSha256:result.csvSha256,home:{radius:homeRadius,targetDistance:result.home.targetDistance,firstOutsideFrame:firstOutside+1,maxDistanceFrame:maxHomeIndex+1,maxDistance:homeDistances[maxHomeIndex]},out}));
