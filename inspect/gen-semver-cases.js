// gen-semver-cases.js — generate shuttle's semver expectation corpus from the REFERENCE
// implementation, which is the `semver` package npm itself resolves with.
//
// This is the only JavaScript in shuttle, and it is here for the same reason loom drives real
// Chrome: an oracle written in the language of the thing it grades is not an oracle.  It runs
// ONCE, at corpus-generation time; inspect/semver-gate.lisp then grades offline against the
// committed .tsv, so neither the suite nor the build needs node.
//
//   node inspect/gen-semver-cases.js > inspect/semver-cases.tsv
//
// Cases are drawn from two places on purpose: hand-picked adversarial shapes (prerelease
// precedence, build metadata, ^0.x, wildcard and hyphen ranges) AND the real dependency ranges of
// widely-used packages, so the corpus covers both the edges and what we will actually meet.

const semver = require('/usr/lib/node_modules/npm/node_modules/semver');

const versions = [
  '0.0.0', '0.0.1', '0.1.0', '0.1.2', '1.0.0', '1.0.1', '1.2.3', '1.2.4', '1.3.0', '1.9.9',
  '2.0.0', '2.0.1', '2.1.0', '10.0.0', '1.0.0-alpha', '1.0.0-alpha.1', '1.0.0-alpha.beta',
  '1.0.0-beta', '1.0.0-beta.2', '1.0.0-beta.11', '1.0.0-rc.1', '1.0.0-0', '1.0.0-1', '1.0.0-1.0',
  '1.2.3-alpha.7', '1.2.4-rc.0', '2.0.0-rc.1', '1.0.0+build', '1.0.0+build.2', '1.0.0-a+b',
  '0.0.0-0', '3.0.0-next.0', '1.2.3-0.3.7', '1.2.3-x.7.z.92',
];

const ranges = [
  '*', '', 'x', '1.x', '1.2.x', '1', '1.2', '=1.2.3', '>1.2.3', '>=1.2.3', '<1.2.3', '<=1.2.3',
  '~1.2.3', '~1.2', '~1', '~0.2.3', '~0.2', '~0', '^1.2.3', '^0.2.3', '^0.0.3', '^0.0.x', '^0.x',
  '^1.2.3-beta.2', '1.2.3 - 2.3.4', '1.2 - 2.3.4', '1.2.3 - 2.3', '>=1.2.3 <2.0.0',
  '1.2.3 || >=2.0.0', '<1.0.0 || >=2.0.0', '>=1.0.0-rc.1 <2.0.0', '^1.0.0-alpha',
  '>1.0.0-alpha', '~1.0.0-beta.2', '>=1.2.3-alpha.7 <1.2.3', '^10.0.0', '>=0.0.0',
  '>=1.0.0 <1.0.0', '1.0.0 - 1.0.0', '^0.0.0', '~0.0.0', '>=1.2.3-0',
];

// REAL ranges and REAL versions, because a hand-written list only ever covers the shapes I
// happened to think of.  Every dependency range in npm's own installed tree, plus every version
// those packages publish, gives the corpus the distribution it will actually meet.
const fs = require('fs'), path = require('path');
const realRanges = new Set(), realVersions = new Set();
const root = '/usr/lib/node_modules/npm/node_modules';
try {
  for (const d of fs.readdirSync(root)) {
    const dirs = d.startsWith('@')
      ? fs.readdirSync(path.join(root, d)).map(x => path.join(d, x))
      : [d];
    for (const dir of dirs) {
      try {
        const pj = JSON.parse(fs.readFileSync(path.join(root, dir, 'package.json'), 'utf8'));
        if (pj.version && semver.valid(pj.version)) realVersions.add(pj.version);
        for (const field of ['dependencies', 'peerDependencies', 'devDependencies']) {
          for (const r of Object.values(pj[field] || {})) {
            if (typeof r === 'string' && semver.validRange(r) !== null) realRanges.add(r);
          }
        }
      } catch (e) { /* not a package dir */ }
    }
  }
} catch (e) { /* tree absent: the hand-picked cases still stand */ }
for (const r of realRanges) if (!ranges.includes(r)) ranges.push(r);
for (const v of realVersions) if (!versions.includes(v)) versions.push(v);

const out = [];
const emit = (...f) => out.push(f.join('\t'));

// VALID: does this parse as a version at all?
for (const v of versions.concat(
  ['1', '1.2', '1.2.3.4', 'v1.2.3', ' 1.2.3 ', '1.2.3-', '1.2.3+', '01.2.3', '1.02.3',
   '1.2.3-01', '1.2.3-a.01', 'a.b.c', '', '1.2.3-alpha_1', '=1.2.3'])) {
  emit('VALID', v, String(semver.valid(v) !== null));
}

// CMP: total ordering, including prerelease precedence and build-metadata indifference.
for (const a of versions) for (const b of versions) {
  if (semver.valid(a) && semver.valid(b)) emit('CMP', a, b, String(semver.compare(a, b)));
}

// SAT: the cross product, which is what `satisfies` has to get right.
for (const r of ranges) for (const v of versions) {
  if (!semver.valid(v)) continue;
  let ok;
  try { ok = semver.satisfies(v, r); } catch (e) { continue; }   // an invalid range is its own test
  emit('SAT', r, v, String(ok));
}

// VALIDRANGE: a range that does not parse must be REFUSED, not silently treated as '*'.
for (const r of ranges.concat(['not-a-range', '>=', '^^1.0.0', '1.2.3 -', '>1.2.3 <', '||'])) {
  let v = null;
  try { v = semver.validRange(r); } catch (e) { v = null; }
  emit('VALIDRANGE', r, String(v !== null));
}

// The candidate set MAXSAT is resolved against, emitted so the gate cannot drift out of step with
// the generator -- it did, the moment real versions were added here and the gate kept its own
// hardcoded copy, and every MAXSAT row then "failed" against a list it was never scored on.
emit('VERSIONS', versions.filter(v => semver.valid(v)).join(','));

// MAXSAT: what a RESOLVER actually calls -- pick the best published version for a range.
for (const r of ranges) {
  let m = null;
  try { m = semver.maxSatisfying(versions.filter(v => semver.valid(v)), r); } catch (e) { m = null; }
  emit('MAXSAT', r, String(m === null ? '-' : m));
}

process.stdout.write(out.join('\n') + '\n');
