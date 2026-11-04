# Queue advance: contents, identity and the order of mutation

This milestone verifies the actual two statements at pinned Hono `node.ts`209–210
in the declared source model. They select the nodes for the next path component:

```js
const shifted = curNodesQueue.shift()
curNodes = shifted ? tempNodes.concat(shifted) : tempNodes
```

![The scheduled queue is shifted before testing the head. A falsy head reuses temp; a truthy head concatenates current cells into a fresh shallow array. The first curNodes binding is updated, including shared-array cases. Sparse producers and the full loop remain open.](../diagrams/queue-advance.png)

[Editable Excalidraw source](../diagrams/queue-advance.excalidraw) ·
[Live scene](https://app.excalidraw.com/s/8wot9n3ajqf/9WTPJvyGlnu) ·
[Proof and evidence audit](queue-advance-audit.md)

## What the two lines do

The pending queue contains groups scheduled by earlier pattern processing.
`shift` removes its first item, stores the remaining tail in the same queue,
and returns the old first item. An empty queue returns `undefined`.

| Shifted value | Result in the supported model |
| --- | --- |
| Falsy, such as `undefined` | Reuse the exact `tempNodes` array; allocate nothing. |
| An array, including `[]` | Allocate a new array containing temporary nodes followed by the shifted array's items. |
| A truthy nonarray | Allocate a new array containing temporary nodes followed by that one value. |

The scalar case describes this source fragment's default concat behavior. It
does not assert that Hono's normal pattern producer schedules arbitrary scalars.
An empty array is truthy, so equal contents do not imply reused identity.

Finally, `curNodes` points at the selected array. Rebinding that variable is
different from modifying every array that an older `curNodes` reference names.
The previous variable value can be anything: these lines do not read it.

## Why the order matters

Suppose the pending queue and temporary queue are the same array `q`, and its
first item points back to `q`:

```text
before: q = [q, nodeA], tempNodes = q
shift:  shifted = q, q = [nodeA]
concat: new array = [nodeA, nodeA]
```

The second line reads the arrays after the first line mutates them. It must not
copy the old `[q, nodeA]` snapshot. The proof handles these aliases by splitting
on reference identity and deriving the current contents from the initial heap.
It does not assume a future post-shift array or concat result.

Concat is shallow. The new array has a fresh identity, but its entries retain
their original node/object/array references. Copying a list of nodes does not
clone the nodes themselves.

## What is proved independently

The contract states that the scheduled queue becomes its tail, the saved local
holds the old head, and `curNodes` selects either the existing temporary array
or one fresh result. The new result has the right length and every copied index
contains the corresponding original value. All other old array cells and the
ordinary-object, private, function, Set and `this` state stay unchanged.

The lexical contract changes exactly the first existing `curNodes` binding.
Earlier unrelated entries and older shadowed bindings remain intact. A new
`shifted` local is retained for source composition. The new parser entry only
permits explicitly supplied mutable outer names; a newly declared `const` or
`let` does not become writable through that allowlist.

The original source parses to its original AST, including `concat` and the bare
assignment. A separate generic entry supports those operations without widening
the earlier fragment parsers. The public theorem executes that parsed source
and proves the independent endpoint contract for arbitrary admitted dense
initial cells, not just the displayed examples.

## What this does not finish

This is a selected source-fragment proof. It does not establish that the
remaining pattern body reaches these lines with every required invariant.
Source 177 can create holes in the outer pending queue. Those holes can be
distinguished from dense `undefined` cells by own-property observations, so
future integration needs a sparse-array model or an appropriate refinement.

Native concat also supports species constructors and spreadability overrides;
getters, inherited indices and failures can introduce additional effects. The
current model assumes dense ordinary arrays, fixed standard operations, legal
native array lengths and successful resources. Executable witnesses expose
these boundaries; they do not prove native-engine adequacy.

The remaining pattern body, full loop invariants, final sorting/map and complete
runtime catalog stay open in the [full-Hono goal](hono-verification-goal.md).
