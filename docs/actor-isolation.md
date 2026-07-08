# Running shuttle under modus: actors, per-actor GC, and the hardware-attack posture

**Status: design.** This is a forward contract — it names the seams shuttle
exposes and the guarantees it needs from the host, so that when modus's actor
API lands the integration is mechanical. It changes no engine behavior today.

## Why this document exists

shuttle runs untrusted JavaScript. The attacks that matter here are *not* bugs
in shuttle — they are **Rowhammer** (DRAM bit-flips), **Spectre-family transient
execution** (speculative out-of-bounds reads exfiltrated through a cache side
channel), and **cache / GC side channels**. There is no line of shuttle to patch
that closes them: the vulnerable substrate is the DRAM cell and the speculating
CPU. The only workable strategy is:

1. **Remove the amplifiers** the JS layer hands an attacker (a JIT, a
   high-resolution clock, huge contiguous buffers, real shared-memory threads,
   GC-liveness oracles), and
2. **Contain the residue** so a successful read or flip only reaches data the
   attacker already owns (same-origin).

Browsers spent years retrofitting (2) as *Site Isolation* — one OS process per
origin, at hundreds of MB and a large IPC-surgery cost. **modus provides
containment as a first-class primitive**: an actor is a heap + a mailbox + a
scheduler slot. You can afford one per origin, per realm, per worker. This
document is the contract that lets shuttle be a well-behaved actor.

shuttle already withholds most of the amplifiers *by construction* — see
[the engine posture](#appendix-what-shuttle-already-denies) at the end. The work
below is about wiring the engine to the isolation and scheduling primitives modus
adds on top.

## The core mapping: one realm ⇄ one actor

```
origin / document / worker   →   modus actor   →   one shuttle realm
        (trust unit)              (heap + mailbox)     (object graph)
```

A shuttle realm is already a self-contained object graph with no shared globals
(`make-realm` builds fresh intrinsics each time; nothing is `defvar`'d across
realms). That maps onto a **share-nothing actor** with zero friction. The
invariant shuttle must hold:

> **No shuttle object is ever reachable from two actors.** A realm's entire
> reachable graph lives in exactly one actor's heap.

Everything else follows from making that invariant line up with the actor
boundary and — for the strong version — with a *hardware address-space*
boundary.

## Division of responsibility

### What shuttle provides

- **Share-nothing realms.** One `make-realm` per actor; no cross-realm state.
- **A capability profile** at realm creation (below) — the single surface through
  which modus dials the engine's posture from an origin's trust label.
- **Enforcement points**: the timer source, the buffer allocator, SAB threading,
  the WeakRef/FinalizationRegistry gate, index masking, and the host-object seam
  — each already a chokepoint the profile can govern.
- **A structured-clone boundary** (below) so a message crosses between actors as
  *self-contained data*, never as a shared object reference.
- **The microtask half of the event loop** (`shuttle:drain-microtasks`); the
  actor's mailbox is the macrotask half.

### What shuttle needs from modus

1. **Per-actor address space for untrusted actors — the determinant.**
   Speculation respects *page tables*, not language semantics. Actor isolation
   only stops Spectre-in-JS if the other origin's memory is *not mapped* while
   this actor runs. Untrusted-content actors must therefore get their own MMU
   context (distinct page tables, switched on scheduling across a trust
   boundary). A Lisp OS can do this far cheaper than a Unix process — no ELF,
   no libc, a shared runtime image, just a page-table + heap region per actor.
   *If actors are green threads sharing one address space, the language boundary
   does not stop transient-execution reads and shuttle falls back to
   [index masking + timer denial](#appendix-what-shuttle-already-denies) as the
   only line.* This one decision determines whether the rest is real or
   cosmetic.

2. **Moving, physically-scattered per-actor GC.** Per-actor collection that
   *moves* objects (copying/compacting, Erlang-shaped) denies Rowhammer the
   stable physical adjacency it requires — the aggressor rows relocate out from
   under the attacker between collections. Backing each actor heap from a
   randomized/scattered set of physical frames, and refusing contiguous or
   huge-page backing for JS `ArrayBuffer`s, denies the "spray a giant typed
   array to own physical rows" primitive entirely. shuttle will keep large
   buffers chunked (below) to stay inside this regime rather than in a pinned
   large-object space.

3. **Scheduler policy** (a Lisp OS can do what a browser cannot):
   - **µarch flush at trust-boundary context switches** — IBPB / branch-predictor
     flush / cache eviction when scheduling from an untrusted actor to another.
   - **No SMT co-scheduling** of mutually-distrusting actors on sibling threads
     (the L1/predictor sharing behind cross-thread Spectre/MDS) — core-scheduling
     as first-class actor placement.
   - **Per-actor memory-activation / allocation-rate quota** — Rowhammer is
     millions of activations/sec; that anomalous rate is throttleable or fatal.
     shuttle's per-realm instruction budget (`*max-steps*`) is the existing hook;
     modus extends it to a memory-rate budget.

4. **The clock and the trust label as capabilities.** The actor's clock is
   whatever modus grants; untrusted actors get a coarse/jittered virtual clock.
   Combined with no SAB timing thread and scheduler-controlled preemption
   granularity, there is genuinely no fine timer to build.

## The capability profile

A profile is a plain struct threaded through realm creation. The engine reads it
at `install-intrinsics` time and at each enforcement point; modus constructs it
from the origin's trust label.

```lisp
;; sketch — the shape, not the final field list
(defstruct security-profile
  (timer-resolution-ns 1000000)   ; Date.now / any clock quantized to this (1 ms)
  (timer-jitter-ns      500000)   ; + uniform jitter, so successive reads don't subtract cleanly
  (max-buffer-bytes  (* 16 1024 1024))  ; hard cap per ArrayBuffer/SAB (untrusted: tens of MB, not 1 GiB)
  (buffer-chunk-bytes (* 64 1024))      ; large buffers backed by scattered chunks, never one contiguous block
  (sab-threading   nil)           ; SharedArrayBuffer is a plain buffer, never a timing-thread primitive
  (weakrefs        nil)           ; WeakRef/FinalizationRegistry gated off (GC-liveness oracle)
  (index-masking   t)             ; Spectre-v1 array/TA index masking on the element fast path
  (finalization-jitter t))        ; if weakrefs on, finalization is deliberately coarse/non-deterministic

(defparameter *profile-untrusted* (make-security-profile))
(defparameter *profile-trusted*
  (make-security-profile :timer-resolution-ns 1 :timer-jitter-ns 0
                         :max-buffer-bytes (* 1024 1024 1024)
                         :sab-threading t :weakrefs t :index-masking nil))
```

```lisp
;; make-realm grows one optional argument; default stays untrusted-safe.
(shuttle:make-realm :profile *profile-untrusted*)
```

The point: the ad-hoc engine mitigations become *one governed policy object* set
per actor, not scattered flags. A trusted host context (e.g. weft's own
privileged UI script) can opt into the fast/full set; web content cannot.

## Message passing: `postMessage` = send, structured clone = copy-on-send

Cross-origin JS interaction (`postMessage`, `MessageChannel`, worker messaging)
becomes **actor message passing**. The HTML *structured clone* algorithm and
actor copy-on-send are the same operation — and that coincidence is the
isolation boundary:

- The message crosses between actors as **self-contained data**, never as a
  shared object reference. With per-actor address spaces this is mandatory (the
  sender's objects aren't mapped in the receiver), and it is exactly `postMessage`
  semantics — a win, not a tax.
- shuttle provides the two halves:

  ```lisp
  (shuttle:structured-clone-serialize value)          ; JS graph -> flat, self-contained wire form
  (shuttle:structured-clone-materialize wire realm)   ; wire form -> fresh JS graph in TARGET realm
  ```

  Serialize walks the source graph (objects, arrays, Maps/Sets, typed arrays,
  Dates, BigInts, cycles via a ref table) into a representation with no host
  pointers; modus transports the bytes to the receiving actor; materialize
  rebuilds a fresh graph in the receiver's realm/heap. Cross-realm object
  identity never exists.
- **Transferables** (`ArrayBuffer` transfer) are the *move* case: the buffer's
  backing store is handed to the receiver and the sender's buffer is **detached**
  (shuttle already implements detach + the `[[ArrayBufferData]]` = NIL state).
  A transfer moves the region between actor heaps without a copy and without
  leaving the sender a live alias.

### The actor run loop

The actor's mailbox is the macrotask queue; shuttle owns microtasks:

```
loop:
  msg     = mailbox.receive()                       ; modus: blocks the actor
  value   = structured-clone-materialize(msg, realm) ; rebuild in this heap
  invoke(realm, onmessage-handler, value)            ; run JS  (shuttle:invoke)
  drain-microtasks(realm)                             ; run the promise jobs it queued
  ;; yield; scheduler may flush µarch state before the next distrusting actor runs
```

Timers and DOM events are macrotasks too — they enter as messages, so the same
loop covers `setTimeout`, event dispatch, and cross-origin `postMessage`
uniformly. `shuttle:drain-microtasks` is already exported for exactly this split.

## Enforcement points (where the profile bites, in engine terms)

| channel | chokepoint | profile control |
|---|---|---|
| cache/DRAM timing readout | `Date.now` / any host clock | `timer-resolution-ns` + `timer-jitter-ns` |
| Spectre timing thread | `SharedArrayBuffer` construction / no worker | `sab-threading = nil` (already single-agent) |
| Spectre-v1 gadget | numeric-index get/set in `value.lisp` / `typedarray.lisp` | `index-masking` (mask index with bounds-derived mask post-check) |
| Rowhammer spray | `ArrayBuffer`/`SAB` allocator (`arraybuffer.lisp`) | `max-buffer-bytes` + `buffer-chunk-bytes` |
| GC-liveness oracle | WeakRef/FinalizationRegistry install gate | `weakrefs` / `finalization-jitter` |
| cross-origin reach | the host-object seam (`make-host-object` closures) | per-actor capability checks + the reflow hook |

Note the seam is doubly useful: weft's DOM for one document lives in one actor,
and every `[[Get]]`/`[[Set]]` already routes through a CL closure — so per-actor
capability enforcement and the layout reflow hook sit at the same point.

## The honest boundary

Actors + per-actor GC deliver the containment and oracle-closing that no
in-engine trick can — **conditional on the actor boundary also being a hardware
boundary**: per-actor address space for untrusted content, moving + scattered
heaps, and no-SMT-co-schedule + boundary flush in the scheduler. What remains
irreducible is the physical substrate: DRAM cells and the shared last-level
cache / memory bus still require ECC + TRR/refresh-managed DRAM and up-to-date
MDS/Spectre microcode underneath. Actors do not make the hardware safe; they
shrink every successful read or flip to **same-origin** — which is the whole
game won.

The determining decision, restated: **do untrusted-content actors get their own
MMU context.** If yes, shuttle-per-actor is stronger than Site Isolation at a
fraction of the cost. If they are green threads in one address space, shuttle is
back to masking + timer denial as its only line, and this document's containment
guarantees do not hold.

## Appendix: what shuttle already denies

Independently of modus, the engine is a deliberately *poor tool* for these
attacks:

- **No JIT.** A bytecode interpreter removes the "craft precise native access
  patterns / JIT-spray" primitive that nearly every practical browser Rowhammer
  and Spectre PoC relies on, and its dispatch indirection blurs the speculation
  window. *Do not add a JIT tier for untrusted origins.*
- **Single-agent `SharedArrayBuffer`.** SAB is a plain buffer; there is no second
  agent to spin a nanosecond timing counter (`$262.agent` is unimplemented).
- **No `WeakRef`/`FinalizationRegistry`** (out of scope today) — no GC-liveness
  oracle.
- **Managed CL arrays, checked bounds, no `addressof`** — JS cannot learn or pin
  a virtual or physical address, and a moving host GC keeps it that way.

modus's job is to contain the residue; shuttle's job is to keep handing the
attacker as little leverage as possible. This document is the join between the
two.
