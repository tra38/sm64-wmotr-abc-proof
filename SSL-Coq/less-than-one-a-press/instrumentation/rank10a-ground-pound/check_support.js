/* Reproduce the Rank-10A source-mesh support census. No game execution or
 * controller reachability is inferred from these geometric certificates. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const root = path.resolve(__dirname, '../..');

function mesh(version, name) {
  const text = fs.readFileSync(path.join(root, `generated/${version}_ssl_collision.v`), 'utf8');
  const marker = `Definition ${name} :=`;
  const start = text.indexOf(marker);
  assert(start >= 0, marker);
  const next = text.indexOf('\nDefinition ', start + marker.length);
  const words = [...text.slice(start, next < 0 ? text.length : next)
    .matchAll(/Init_int16 \(Int\.repr (?:\((-?\d+)\)|(-?\d+))\)/g)]
    .map(m => Number(m[1] ?? m[2]));
  assert.equal(words[0], 64);
  const vertices = Array.from({length: words[1]}, (_, i) => words.slice(2+3*i, 5+3*i));
  let cursor = 2 + 3*vertices.length;
  const faces = [];
  while (words[cursor] < 64 || words[cursor] >= 101) {
    const type = words[cursor++], count = words[cursor++];
    const stride = [4,14,36,37,39,44,45].includes(type) ? 4 : 3;
    assert(Number.isInteger(count) && count >= 0);
    for (let i = 0; i < count; i++, cursor += stride) {
      const indices = words.slice(cursor, cursor+3);
      assert.equal(indices.length, 3);
      assert(indices.every(n => Number.isInteger(n) && n >= 0 && n < vertices.length));
      faces.push({ordinal: faces.length, type, indices, vertices: indices.map(n => vertices[n])});
    }
  }
  assert.equal(words[cursor], 65, 'Must reach the real triangle-end marker');
  return {vertices, faces};
}
function positiveY({vertices: [a,b,c]}) {
  return (b[2]-a[2])*(c[0]-b[0]) - (b[0]-a[0])*(c[2]-b[2]) > 0;
}
function overlaps(face, box) {
  return [0,2].every((axis, i) =>
    Math.max(...face.vertices.map(p => p[axis])) >= box[2*i] &&
    Math.min(...face.vertices.map(p => p[axis])) <= box[2*i+1]);
}
module.exports = {mesh, positiveY, overlaps};
if (require.main === module) {
const expected = [1267,1268,1269,1270,1271,1274,1275,1276,1277,1278,
  1303,1304,1305,1306,1307,1311,1312,1314,1339,1340,1341,1342,1343,
  1346,1347,1348,1349,1350,1381,1382,1383,1384,1385,1387];
const worldBox = [-459,460,-203,716], localBox = [-459,460,-459,460];
let reference;
for (const version of ['us','jp']) {
  const level = mesh(version, 'v_ssl_seg7_area_2_collision');
  const elevator = mesh(version, 'v_ssl_seg7_collision_pyramid_elevator');
  assert.equal(level.vertices.length, 1080);
  assert.equal(level.faces.length, 1558);
  assert.equal(elevator.vertices.length, 20);
  assert.equal(elevator.faces.length, 36);
  const candidates = level.faces.filter(f => positiveY(f) && overlaps(f, worldBox));
  assert.deepEqual(candidates.map(f => f.ordinal), expected);
  assert(candidates.every(f => f.vertices.every(p => p[1] <= -101)));
  const bases = elevator.faces.filter(f => positiveY(f) && overlaps(f, localBox));
  assert.deepEqual(bases.map(f => f.ordinal), [10,11]);
  assert.deepEqual(bases.map(f => f.vertices), [
    [[-511,0,512],[512,0,512],[512,0,-511]],
    [[-511,0,512],[512,0,-511],[-511,0,-511]]]);
  const result = {worldBox, staticTriangles: level.faces.length,
    positiveYTriangles: level.faces.filter(positiveY).length,
    staticCandidates: candidates.map(f => f.ordinal),
    highestCandidateVertex: Math.max(...candidates.flatMap(f => f.vertices.map(p => p[1]))),
    elevatorInteriorFloors: bases.map(f => f.ordinal)};
  if (reference) assert.deepEqual(result, reference); else reference = result;
}
console.log(JSON.stringify({scope: 'finite source geometry; no live-list or controller claim',
  versions: ['US','JP'], ...reference}, null, 2));
}
