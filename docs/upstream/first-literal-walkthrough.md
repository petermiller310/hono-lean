# From initial state to the complete first literal branch

The earlier proofs established startup, first loop entry and the literal-child
branch separately. This milestone joins them for arbitrary admitted initial
states. Its public theorems begin before startup, execute the actual selected
source through the complete first literal branch, and establish an independent
result contract. The target remains Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`.

![Initial registered rows and key arrays feed actual startup and first loop entry, then missing/nonfinal/direct/wildcard cases. The independent contract records the actual selected child, raw order and live aliases. Remaining traversal and native adequacy stay open.](../diagrams/first-literal.png)

[Editable Excalidraw source](../diagrams/first-literal.excalidraw) ·
[Live scene](https://app.excalidraw.com/s/8wot9n3ajqf/9ZfC0TB5T2n) ·
[Proof and evidence audit](first-literal-audit.md)

## What comes from the initial state

The initial facts describe existing nodes, private DATA/METHOD kinds, child-map
reads, actual registered method rows, handler records, key snapshots, prototype
chains and captured helper imports. They contain no search collector, generated
parts/node array, chosen index, completed startup or future helper execution.

Actual startup 87–97 creates the collector and arrays and resets the receiver's
params. Headers99/104 produce the first indices and guards. Source 105 reads the
receiver from the generated singleton node array;106 reads the actual first
child. The independent contract explicitly connects that child to its original
child-map lookup, rather than allowing an arbitrary chosen target.

The empty-path case stops after the false outer guard. The diagram's nonempty
arrow then separates the other four cases:

| First literal case | Guaranteed behavior in the source model |
| --- | --- |
| Falsy child | Bind the actual lookup result and skip the branch. |
| Real child, nonfinal part | Propagate reset params and enqueue the child once. |
| Final part, no truthy wildcard child | Propagate params and call the direct helper. |
| Final part, truthy wildcard child | Call the wildcard helper before the direct helper. |

The helper contracts preserve actual method/ALL selection, raw handler
occurrences and captures. This is the intermediate collection order before the
later source sorting and result mapping.

## Why the collector no longer needs to be assumed

The capture-loop proof needs a collector plus structural conditions on records
and key arrays. Previously, its complete `Layout` included a collector that
already existed. We now separate the initial facts from that allocated cell.

`Uncollected` describes only existing records, their immutable keys, protected
reads and captured imports. After source allocates the actual empty collector,
the proof constructs the helper Layout. Existing key and method-array lookups
show that their identities are older than the fresh collector, so the required
separation follows from allocation. It is not an extra future-state premise.

For two terminal calls, one initial union describes both targets' actual rows.
The first call's effects establish the second call's readiness through the
earlier sequential branch argument. Repeated references and shared targets are
allowed; the proof does not silently replace either row list with an empty one.

Helper imports come from the method closure's captured environment. An unrelated
caller binding with the same name does not supply that capture.

## The child can be the receiver itself

Suppose the receiver initially holds stale params A and its child map points
back to itself. Startup first changes the receiver's private params to the
shared reset object. That same write has already changed the child, because
they are one node. The later propagation must therefore begin with the reset
value as its old value.

The proof derives this with an identity case split. It does not assume the
child differs from the receiver or reuse the stale initial value. It also
preserves the private method's METHOD tag while changing the params DATA slot.

The source-prepared examples exercise all four paths, the empty case, self
children, and a shared wildcard/direct handler. Their initial arrays come from
parsed class installation and registration; a separately parsed source 202 write
provides stale params before search startup. Child maps remain ordinary fixture
inputs, so this does not prove the surrounding `Node.insert` traversal.

## What stays stable

Every array that existed before startup keeps its contents through this prefix.
The newly produced current-node, parts and pending queues also keep their
contents through the literal branch. The temporary queue changes only for the
nonfinal enqueue, while terminal calls append to the fresh collector.

Ordinary handler records deliberately change: each selected record receives a
new capture object. If two collector entries refer to the same handler record,
both observe its latest params field. These are raw collector aliases, not a
claim that previously returned Hono response/match objects change; the later
result mapping is outside this source window.

## The exact source connection and its limit

The new source artifact contains every character of contiguous `node.ts`87–119.
Lean proves that it equals the already checked startup/header/declaration/branch
pieces with exactly the two source blank lines between them. The first entry
AST's tail is also proved equal to the separately parsed literal branch, so
source 105 executes once before 106–119.

This remains an explicit segmented source-prefix interpreter with reviewed
language assumptions. It is not a full TypeScript frontend or a native-engine
adequacy theorem. The prefix ends inside the first inner loop body. Patterns,
later loop iterations, queue progression, sorting/map, native completion and the
rest of the pinned package remain open in the [full goal](hono-verification-goal.md).
