#!/usr/bin/env node
'use strict';
// Ordinary-gameplay vertical diagnostic. No controller movie, state editing,
// emulator access, live floor selection, or clean installation is asserted.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const root = path.resolve(__dirname, '../..');
const f = Math.fround;
const storage = new DataView(new ArrayBuffer(4));
function bits(word) {
  storage.setUint32(0, word >>> 0);
  return storage.getFloat32(0);
}
function definition(version, unit, name) {
  const text = fs.readFileSync(path.join(root, 'generated', `${version}_${unit}.v`), 'utf8');
  const start = text.indexOf(`Definition ${name} :=`);
  assert(start >= 0, name);
  return text.slice(start, text.indexOf('|}.', start) + 3);
}
for (const version of ['us', 'jp']) {
  const hop = definition(version, 'obj_behaviors_2', 'f_goomba_begin_jump');
  assert.match(hop, /Ebinop Omul\s*\(Ebinop Odiv/);
  for (const value of [1112014848, 1077936128]) assert(hop.includes(`Int.repr ${value}`));
  const property = definition(version, 'obj_behaviors_2', 'v_sGoombaProperties');
  assert.match(property, /gvar_init := \(Init_float32 \(Float32.of_bits \(Int.repr 1069547520\)/);
  const order = definition(version, 'object_list_processor', 'v_sObjectListUpdateOrder');
  const orderWords = [...order.matchAll(/Init_int8 \(Int.repr (?:\((-?\d+)\)|(-?\d+))\)/g)]
    .map(m => Number(m[1] ?? m[2]));
  assert.deepEqual(orderWords, [11, 9, 10, 0, 5, 4, 2, 6, 8, 12, -1]);
  const star = definition(version, 'behavior_data', 'v_bhvSpawnedStarNoLevelExit');
  const words = [...star.matchAll(/Init_int32 \(Int.repr (\d+)\)/g)].map(m => Number(m[1]));
  assert.deepEqual(words, [393216, 285278209, 754974720, 201326592, 134217728, 201326592, 150994944]);
  assert.deepEqual([...star.matchAll(/Init_addrof (_\w+)/g)].map(m => m[1]),
    ['_bhv_spawned_star_init', '_bhv_spawned_star_loop']);
}
const jumpVelocity = f(f(bits(1112014848) / bits(1077936128)) * bits(1069547520));
assert.equal(jumpVelocity, 25);
function advance(y, v) {
  v = Math.max(-78, f(v - 4));
  return [f(y + v), v];
}
const peakCache = new Map();
function coinPeak(seed) {
  if (peakCache.has(seed)) return peakCache.get(seed);
  let peak = seed;
  // All ordinary RNG return words. These are possible values, not a claim
  // that a controller can choose their history or arrange the other samples.
  for (let word = 0; word < 65536; ++word) {
    let y = seed, v = f(f(f(f(word / 65536) * 10) + 30) + 20);
    for (let tick = 0; tick < 16; ++tick) {
      v = f(v - 4); y = f(y + v);
      peak = Math.max(peak, y);
    }
  }
  peakCache.set(seed, peak);
  return peak;
}
const cases = [];
let attackCases = 0;
for (const origin of [640, 1145, 2517]) {
  let y = origin, v = jumpVelocity, best;
  for (let releaseTick = 0; releaseTick <= 20; ++releaseTick) {
    for (const attackVelocity of [30, 50]) {
      let enemyY = y, enemyV = attackVelocity, enemyPeak = y;
      // Grant an unrestricted finishing-attack apex, even though a real
      // contact or the death timer can end this flight earlier.
      for (let tick = 0; tick < 20; ++tick) {
        [enemyY, enemyV] = advance(enemyY, enemyV);
        enemyPeak = Math.max(enemyPeak, enemyY);
      }
      const seed = f(enemyPeak + 78); // separately granted favorable loot floor
      const peak = coinPeak(seed); // even intangible heights count favorably
      const contact = f(peak + 64);
      const firstStartup = f(contact + 20);
      ++attackCases;
      assert(firstStartup <= origin + 978); // conservative Coq composition
      assert(firstStartup < 3505);
      if (!best || firstStartup > best.firstStartup) {
        best = {origin, releaseTick, attackVelocity, attackHeight: y,
          enemyPeak, seed, coinPeak: peak, contact, firstStartup,
          missingRise: 3505 - firstStartup};
      }
    }
    [y, v] = advance(y, v);
  }
  cases.push(best);
}
assert.equal(cases[2].attackHeight, 2583);
assert.equal(cases[2].firstStartup, 3452.99658203125);
assert.equal(cases[2].missingRise, 52.00341796875);
// Timing control: wrongly crediting ALL future startup lifts looks positive.
// They happen after the ordinary first home sample, so are NOT its position.
let wronglyDelayed = cases[2].contact;
for (let timer = 0; timer < 10; ++timer) wronglyDelayed = f(wronglyDelayed + 20 - 2 * timer);
assert(wronglyDelayed >= 3505);
console.log(JSON.stringify({
  scope: 'conditional vertical test; no clean producer or live scheduling claim',
  generatedVersions: ['us', 'jp'], jumpVelocity, attackCases,
  releaseMovementCounts: '0..20', randomReturnWordsPerSeed: 65536,
  distinctCoinSeeds: peakCache.size, cases,
  deliberatelyWrongDelayedHomeControl: wronglyDelayed,
  conservativeCoqCeilings: {releasedEnemy: 2601, defeatedEnemy: 2913,
    coinSeed: 2991, coin: 3411, contact: 3475, firstStartup: 3495, shortfall: 10},
}, null, 2));
