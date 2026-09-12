/* Generated-mesh backward search for a Goomba/elevator contact.
 * Geometry and isolated vertical arithmetic, not an emulator/controller run.
 * In particular, a hard landing beside the bucket is NOT granted reachable. */
'use strict';
const assert = require('node:assert/strict');
const {mesh, positiveY, overlaps} = require('./check_support.js');
const f = Math.fround;
const contactBox = [-656,657,-400,913]; // FULL base + 108+37, wider than Mario's interior
const budget = 55*30 + 216;
const expanded = [contactBox[0]-budget,contactBox[1]+budget,
  contactBox[2]-budget,contactBox[3]+budget];
const flat = (face,y) => face.vertices.every(v => v[1] === y);
const highIds = [1025,1037,1062,1064];
const ledgeIds = [905,908,909,912,913,914,920,923,927,928,929,930,931,933];
let reference;
for (const version of ['us','jp']) {
  const all = mesh(version, 'v_ssl_seg7_area_2_collision').faces;
  const near = all.filter(a => positiveY(a) && overlaps(a,contactBox));
  assert.equal(all.length,1558);
  assert.equal(near.length,53);
  const high = near.filter(a => !a.vertices.every(v => v[1] <= -101));
  assert.deepEqual(high.map(a => a.ordinal),highIds);
  assert(high.every(a => flat(a,384) || flat(a,896)));
  const ledges = all.filter(a => positiveY(a) && flat(a,640));
  assert.deepEqual(ledges.map(a=>a.ordinal),ledgeIds);
  assert(ledges.every(a=>!overlaps(a,expanded)));
  const side = all[1314];
  assert.deepEqual(side.indices,[50,137,126]);
  assert.deepEqual(side.vertices,[[-511,-101,-357],[-767,-153,528],[-383,-153,-136]]);
  const result = {staticFaces:all.length,nearbyFloorCandidates:near.length,
    highApproaches:high.map(a=>({ordinal:a.ordinal,vertices:a.vertices})),
    level640Faces:ledges.length,displacementBudget:budget};
  if (reference) assert.deepEqual(result,reference); else reference=result;
}
function arc(y,v,count) {
  const result=[];
  for(let i=0;i<count;i++) {
    v=f(Math.max(-78,f(v-4))); y=f(y+v); result.push({y,v});
  }
  return result;
}
const jump=arc(-101,25,7), hardBounce=arc(-101,f(-76*-.5),10);
// Isolated flat-floor arithmetic, used with source review of the distinct
// LANDED / ON_GROUND tests. No full action or wall execution is simulated.
const ordinaryLanding = arc(0,25,12).at(-1);
assert.deepEqual(ordinaryLanding,{y:-12,v:-23});
const ordinaryRebound = f(ordinaryLanding.v * -.5);
assert.equal(ordinaryRebound,11.5);
const resumedWalkRise = arc(0,ordinaryRebound,2);
assert.deepEqual(resumedWalkRise,[{y:7.5,v:7.5},{y:11,v:3.5}]);
assert.equal(Math.max(...jump.map(p=>p.y)),-35);
assert.equal(Math.max(...hardBounce.map(p=>p.y)),61);
assert.equal(Math.max(...hardBounce.map(p=>p.y))+75,136);
const upperFall=arc(1145,39,38);
assert.deepEqual(upperFall.slice(-4),[{y:68,v:-78},{y:-10,v:-78},
  {y:-88,v:-78},{y:-166,v:-78}]);
const upperBounce=arc(0,39,18);
assert.equal(upperBounce[16].y,51);
assert.equal(upperBounce[17].y,18);
// This displayed height is ideal plane arithmetic. Coq separately checks
// the loaded Float32 height and rebound/contact inequalities at this point.
const sideVertices=[[-511,-101,-357],[-767,-153,528],[-383,-153,-136]];
const edge=(a,b)=>(a[2]+187)*(b[0]-a[0])-(a[0]+551)*(b[2]-a[2]);
assert(sideVertices.every((a,i)=>edge(a,sideVertices[(i+1)%3])>=0));
const [a,b,c]=sideVertices, u=b.map((x,i)=>x-a[i]), v=c.map((x,i)=>x-b[i]);
const normal=[u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0]];
const sideHeight=a[1]-(normal[0]*(-551-a[0])+normal[2]*(-187-a[2]))/normal[1];
assert(sideHeight>-113 && sideHeight<-112);
assert(141*141+33*33 < 145*145);
console.log(JSON.stringify({scope:'finite geometry and vertical arithmetic; no live reachability',
  versions:['US','JP'],contactBox,...reference,
  normalJump:{feet:-35,head:40,lowestNominalMario:118},
  normalLanding:{unclamped:ordinaryLanding,rebound:ordinaryRebound,
    nextTwoIsolatedUpdates:resumedWalkRise,
    scope:'arithmetic only; source action can resume WALK on LANDED before ON_GROUND is set'},
  hardLandingCandidate:{impact:-76,rebound:38,landingFloor:-101,
    peakFeet:61,peakHead:136,baseLookupThreshold:50},
  budgetScope:'55 movements of at most 30 per axis plus total extra displacement at most 216 per axis; not an all-history bound',
  upperFlightSamples:upperFall.slice(-4),
  upperBounceSamples:upperBounce.slice(-2),
  exteriorContactCandidate:{mario:[-410,128,-154],goombaXZ:[-551,-187],
    face:1314,idealPlaneHeight:sideHeight,impact:-78,rebound:39,
    idealPeakFeet:sideHeight+171,idealPeakHead:sideHeight+171+75,
    horizontalDistanceSquared:20970,radiusSquared:21025,
    scope:'conditional geometry; no reached fall, collision record, attack or coin drop'}},null,2));
