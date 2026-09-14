/* Source-mesh and binary32 checks for the Rank-10A early-return question.
 * No live surface list, Mario run, or controller coverage is inferred. */
'use strict';
const assert = require('node:assert/strict');
const {mesh, overlaps} = require('./check_support.js');
const f = Math.fround;
const add = (a,b) => f(f(a)+f(b));
const sub = (a,b) => f(f(a)-f(b));
const mul = (a,b) => f(f(a)*f(b));
const div = (a,b) => f(f(a)/f(b));
function normal({vertices: [a,b,c]}) {
  return [(b[1]-a[1])*(c[2]-b[2])-(b[2]-a[2])*(c[1]-b[1]),
    (b[2]-a[2])*(c[0]-b[0])-(b[0]-a[0])*(c[2]-b[2]),
    (b[0]-a[0])*(c[1]-b[1])-(b[1]-a[1])*(c[0]-b[0])];
}
function plane(face) {
  const raw = normal(face).map(n=>f(n|0));
  const magnitude = f(Math.sqrt(add(add(mul(raw[0],raw[0]),mul(raw[1],raw[1])),mul(raw[2],raw[2]))));
  const n = raw.map(x=>mul(x,f(1/magnitude)));
  const p = face.vertices[0];
  return [...n, f(-add(add(mul(n[0],p[0]),mul(n[1],p[1])),mul(n[2],p[2])))];
}
function height([nx,ny,nz,oo],x,z) {
  return div(f(-add(add(mul(x,nx),mul(nz,z)),oo)),ny);
}
const ordinals=[83,84,85,86,87,91,92,93,94,95,96,98,99,100,101,102,1066,1067];
let reference;
for (const version of ['us','jp']) {
  const level=mesh(version,'v_ssl_seg7_area_2_collision');
  const elevator=mesh(version,'v_ssl_seg7_collision_pyramid_elevator');
  const ceilings=level.faces.filter(face=>normal(face)[1]<0 && overlaps(face,[-459,460,-203,716]));
  assert.deepEqual(ceilings.map(face=>face.ordinal),ordinals);
  assert(ceilings.every(face=>face.vertices.every(p=>p[1]===face.vertices[0][1] && p[1]>=5222)));
  // Zero X/Z normals make these computed planes independent of query X/Z.
  assert(ceilings.every(face=>plane(face)[0]===0 && plane(face)[2]===0));
  const staticHeights=[...new Set(ceilings.map(face=>height(plane(face),0,0)))].sort((a,b)=>a-b);
  assert.deepEqual(staticHeights,[5222,5734,6144]);
  const under=elevator.faces.filter(face=>normal(face)[1]<0 && overlaps(face,[-459,460,-459,460]));
  assert.deepEqual(under.map(face=>face.ordinal),[4,6]);
  assert(under.every(face=>face.vertices.every(p=>p[1]===-50)));
  let minimumRejection=Infinity;
  for(let base=128;base<=4966;base++) {
    assert(add(base,160)<5222);
    for(const face of under) {
      const moved={...face,vertices:face.vertices.map(([x,y,z])=>[x,y+base,z+256])};
      const h=height(plane(moved),0,256);
      const queryY=Math.trunc(add(base,80));
      const difference=sub(queryY,sub(h,-78));
      assert(difference>0);
      minimumRejection=Math.min(minimumRejection,difference);
    }
  }
  // Numerical consequence of a GRANTED stall, not a produced blocked run.
  const stalledGaps=Array.from({length:12},(_,n)=>sub(4000,sub(4000,10*n)));
  assert(stalledGaps.slice(0,11).every(gap=>gap<=100));
  assert(stalledGaps[11]>100);
  const result={staticTriangles:level.faces.length,ceilingCandidates:ceilings.length,
    staticHeights,undersideFaces:under.map(face=>face.ordinal),
    integerBaseHeightsChecked:4966-128+1,minimumRejection,
    highestBase:4966,minimumStaticHeadroom:5222-4966,
    grantedStallFirstHighGapUpdate:11};
  if(reference) assert.deepEqual(result,reference); else reference=result;
}
console.log(JSON.stringify({scope:'finite source geometry and arithmetic; no live-list or controller claim',
  versions:['US','JP'],...reference},null,2));
