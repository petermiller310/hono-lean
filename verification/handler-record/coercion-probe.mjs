// Finite engine observations OUTSIDE the primitive-string method contract.
// Keep the standard/model boundary visible when native engines disagree.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const runtime = process.versions.bun ? `Bun ${process.versions.bun}` : `Node ${process.versions.node}`;
if (process.versions.bun) assert.equal(process.versions.bun, '1.4.0');
else assert.equal(process.versions.node, '22.22.2');
const checkout = resolve(process.argv[2]);
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52';
const git = (...args) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } });
assert.equal(git('rev-parse', 'HEAD').trim(), pin);
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '');
let checkedPinnedBlobs = 0;
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2];
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)));
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob);
  checkedPinnedBlobs++;
}
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url), 'utf8'));
const file = readFileSync(resolve(checkout, metadata.sourcePath));
const source = readFileSync(new URL('./source.ts.txt', import.meta.url), 'utf8');
assert.equal(createHash('sha256').update(file).digest('hex'), metadata.sourceSha256);
assert.equal(file.subarray(metadata.fragment.startByte, metadata.fragment.endByteExclusive).toString('ascii'), source);
assert.equal(createHash('sha256').update(source).digest('hex'), metadata.fragment.sha256);

const minimal = [];
const key = { [Symbol.toPrimitive]() { minimal.push('key'); return 'x'; } };
const value = () => { minimal.push('value'); return 1; };
const result = { [key]: value() };
assert.equal(result.x, 1);
const events = [];
const method = { [Symbol.toPrimitive]() { events.push('key'); return 'GET'; } };
const possibleKeys = { *[Symbol.iterator]() { events.push('iterate'); yield 'id'; } };
const argument = new Function('method', 'handler', 'possibleKeys', `let order = 0; const result = (${source}); return { result, order };`)
  (method, 'handler', possibleKeys);
assert.equal(argument.result.GET.score, 1);
const callEvents = [];
const called = new Function('method', 'handler', 'possibleKeys', 'events', `let order = 0;
  const receiver = { get push() { events.push('lookup'); return () => events.push('push'); } };
  receiver.push(${source}); return order;`)
  ({ [Symbol.toPrimitive]() { callEvents.push('key'); return 'GET'; } }, 'handler',
    { *[Symbol.iterator]() { callEvents.push('iterate'); yield 'id'; } }, callEvents);
assert.equal(called, 1);
process.stdout.write(JSON.stringify({ runtime, revision: pin, checkedPinnedBlobs,
  domain: 'object-valued computed key and custom iterator; outside the proved primitive-string domain',
  minimal, objectArgument: events, call: callEvents }) + '\n');
