# Sparse queue scheduling: a hole is an absent own index

Hono can schedule a group of nodes several path components ahead. The actual
source at `node.ts`177–178 creates or reuses that group's queue:

```js
const targetCurNodes = (curNodesQueue[componentCount] ||= [])
targetCurNodes.push(child)
```

This milestone proves those statements in a sparse indexed-array model and
connects their output to the previously verified queue-consumption statements
at 209–210. The target remains Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`.

![A truthy slot reuses its array without a write. A falsy or missing slot receives a fresh array, leaving intervening holes. The child is pushed to the current target. Actual queue consumption preserves holes, while a separate read-value bridge observes them as undefined.](../diagrams/queue-schedule.png)

[Editable Excalidraw source](../diagrams/queue-schedule.excalidraw) ·
[Live scene](https://app.excalidraw.com/s/8wot9n3ajqf/5UeEkXopWDR) ·
[Proof and evidence audit](queue-schedule-audit.md)

## Why a normal list was not enough

Start with an empty queue and schedule at index 3. After these two statements:

```text
length:    4
own bits:  0     0     0     1
contents:  hole  hole  hole  [child]
```

A hole is an index the array does not own. It is different from an own property
whose value is `undefined`. Reading either gives `undefined` under the declared
clean-prototype conditions, but checking ownership distinguishes them.

The new model retains both the array length and an optional own value at each
index. Writing index 3 changes that slot and length; it does not fill indices 0–2
with artificial own `undefined` properties.

## What `||=` must guarantee

The base and primitive numeric index expressions are evaluated once, and the
selected slot is read. If its value is truthy, Hono reuses it: no RHS allocation
and no slot write occur. If it is falsy or absent, `[]` creates a fresh array and
that reference is written to the saved slot. The assignment's value supplies
`targetCurNodes`, which receives the subsequent push.

The normal domain requires a truthy slot to hold an allocated array with push
capacity. An empty array is truthy, so an existing empty group is reused. Repeating the
registration appends to the same group, and earlier references see the new item.

The proof also admits a slot that points back to the outer queue itself. In
that case, pushing the child changes the queue's current length. The contract
does not incorrectly promise that the outer queue always keeps its length or
that every selected group is a separate object.

## How this connects to consumption

The sparse interpreter also executes the actual 209–210 shift/concat/rebind
fragment. Shift moves or deletes own numeric properties; concat preserves
missing own positions in its copied result. Neither operation secretly converts
the authoritative sparse heap into dense lists.

A separate observer reads each in-range position. It maps a hole to an observed
`undefined` value. Lean proves that this read-value observation agrees with the
earlier dense consumer contract for the admitted arrays. The original own bits
remain available and distinct. The bridge accepts an explicit ambient caller
frame rather than manufacturing a Node/private/object context from nothing.

A universal composition starts before scheduling with an empty queue and a
positive index. The producer creates the gap; the actual consumer then removes
the first hole and reuses the temporary queue. All readiness facts come from
the initial state and the producer's contract. Separate theorems cover the
consumer's truthy-array and scalar cases, and examples run repeated scheduling
and several consumptions in one shared heap.

## What remains open

The two source windows are selected fragments. We have not proved execution of
the enclosing `for-in`, the private params write at 175, production of
`componentCount` by the regexp code at 176, all intervening control flow, or the
whole search loop. The numeric index and relevant array cells are explicit
initial inputs, with native array-index/length and method assumptions.

Native-only probes preserve a Node22/Bun1.4 difference for object-valued indices
with conversion side effects. Those inputs are outside this primitive numeric
index proof. Getters, inherited numeric properties, custom push methods, general
coercion, native resource/error traces and complete language adequacy remain
separate obligations. See the audit and committed boundary reproducer.

The [full-Hono goal](hono-verification-goal.md) stays active, including the
remaining pattern body, complete loop composition, final sorting/map and the
entire fixed runtime catalog.
