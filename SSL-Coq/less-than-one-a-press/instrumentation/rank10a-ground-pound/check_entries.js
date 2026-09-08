/* Rank 10A entry exclusions. Reads generated game data; no emulator or
 * game-memory modification. The motion is conditional on stock scheduling,
 * home/pose/table persistence and selection of the same elevator base. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const root = path.resolve(__dirname, '../..');
const f = Math.fround;
const add = (a, b) => f(f(a) + f(b));
const mul = (a, b) => f(f(a) * f(b));
function definition(version, unit, name) {
  const text = fs.readFileSync(path.join(root, `generated/${version}_${unit}.v`), 'utf8');
  const start = text.indexOf(`Definition ${name} :=`);
  assert(start >= 0, name);
  const end = text.indexOf('\nDefinition ', start + 1);
  return text.slice(start, end < 0 ? text.length : end);
}
function words(version, name) {
  return [...definition(version, 'ssl_collision', name)
    .matchAll(/Init_int16 \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)/g)]
    .map(m => Number(m[1] ?? m[2]));
}
function mesh(data) {
  assert.equal(data[0], 64);
  const vertices = Array.from({length: data[1]}, (_, i) => data.slice(2+3*i, 5+3*i));
  let cursor = 2 + 3*data[1];
  const groups = [], hangable = [];
  while (data[cursor] < 64 || data[cursor] >= 101) {
    const type = data[cursor++], count = data[cursor++];
    const stride = [4, 14, 36, 37, 39, 44, 45].includes(type) ? 4 : 3;
    groups.push([type, count]);
    for (let i = 0; i < count; ++i, cursor += stride) {
      const indices = data.slice(cursor, cursor+3);
      assert(indices.every(x => x >= 0 && x < vertices.length));
      if (type === 5) hangable.push({indices, vertices: indices.map(x => vertices[x])});
    }
  }
  assert.equal(data[cursor], 65, JSON.stringify({cursor, groups, tail: data.slice(cursor, cursor+8)}));
  return {groups, hangable};
}
const dynamicNames = ['grindel', 'spindel', '0702808C', 'pyramid_elevator'];
let reference;
for (const version of ['us', 'jp']) {
  const staticMesh = mesh(words(version, 'v_ssl_seg7_area_2_collision'));
  assert.equal(staticMesh.hangable.length, 6);
  const boxes = staticMesh.hangable.map(({vertices}) => {
    const x = vertices.map(p => p[0]), z = vertices.map(p => p[2]);
    const box = {minX: Math.min(...x), maxX: Math.max(...x),
      minZ: Math.min(...z), maxZ: Math.max(...z)};
    // Use the full OUTER bucket footprint, larger than its usable interior.
    assert(box.minX > 512 || box.maxX < -511 || box.minZ > 768 || box.maxZ < -255);
    return box;
  });
  for (const name of dynamicNames) {
    assert.equal(mesh(words(version, `v_ssl_seg7_collision_${name}`)).hangable.length, 0);
  }
  const trig = [...definition(version, 'math_util', 'v_gSineTable')
    .matchAll(/Init_float32 \(Float32\.of_bits \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)\)/g)]
    .map(m => { const b = Buffer.alloc(4); b.writeUInt32LE(Number(m[1] ?? m[2]) >>> 0); return b.readFloatLE(); });
  assert.equal(trig.length, 5120);
  const samples = [{phase: 'idle', timer: 0, y: 4966}];
  for (let timer = 0; timer <= 8; ++timer)
    samples.push({phase: 'start', timer, y: f(4966 - mul(trig[timer*256], 10))});
  let y = samples.at(-1).y, timer = 0;
  do {
    y = Math.max(128, add(y, -10));
    samples.push({phase: 'descent', timer: timer++, y});
  } while (y > 128);
  for (let timer = 0; timer <= 8; ++timer)
    samples.push({phase: 'stop', timer, y: timer >= 8 ? 128 : add(mul(trig[timer*256], 10), 128)});
  samples.push({phase: 'parked', timer: 9, y: 128});
  let maxDrop = 0, maxQuantizedDrop = 0;
  for (let i = 1; i < samples.length; ++i) {
    const before = samples[i-1].y, after = samples[i].y;
    maxDrop = Math.max(maxDrop, before - after);
    maxQuantizedDrop = Math.max(maxQuantizedDrop, Math.trunc(before) - Math.trunc(after));
    assert(before < add(after, 100));
    assert(Math.trunc(before) < add(Math.trunc(after), 100));
    // Stronger than the nominal integer-base trace: allow one unit of
    // error at BOTH samples. This allowance is a condition, not a derived
    // bound on every possible transformed floor calculation.
    assert(add(before, 1) < add(add(after, -1), 100));
  }
  const result = {hangableBoxes: boxes, noHangableDynamicMeshes: dynamicNames.length,
    samples: samples.length, startY: samples.filter(p => p.phase === 'start').map(p => p.y),
    stopY: samples.filter(p => p.phase === 'stop').map(p => p.y), maxDrop, maxQuantizedDrop};
  if (reference) assert.deepEqual(result, reference); else reference = result;
}
console.log(JSON.stringify({scope: 'source-data and stock-motion diagnostic, not a live route proof',
  versions: ['US', 'JP'], ...reference}, null, 2));
