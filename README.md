# shuttle

**A Lisp-native JavaScript engine.** Clean-room — no FFI, no embedded V8/QuickJS.
A loom's shuttle is the one moving part that drives the weft thread across the
warp; a JS engine is exactly that — the active force that pushes changes through
the page.

shuttle is the JavaScript engine for [`weft`](https://github.com/modus-lisp) (a
pure-CL web engine), built the way `scribe`'s `open-font`/`shape-run` seam was —
**consumable up front**. The pipeline is `source → bytecode → stack VM`; the
oracle is **test262**, the official ECMAScript conformance suite (the WPT/
html5lib pattern).

## Conformance

**9,395 / 10,800 (87.0%) — nothing skipped, and negative tests checked against the
error they declare.**

Measured with `inspect/test262-slice.lisp` over a stratified sample: nine 1,200-test
slices spread evenly across the deterministically-sorted 53,404-file corpus. A sample
rather than a full sweep because a full sweep does not fit the machine this is
developed on; the slices are fixed offsets, so the number is reproducible and moves
only when the engine does.

Read that number against the one it replaces. The previous headline was **41,404 /
47,058 (88.0%)** with **6,346 tests skipped** — ES modules and everything flagged
`async`. Against the whole corpus that was 77.5%. Those 6,346 now run:

| | then | now |
|---|---|---|
| ES modules (`language/module-code`) | skipped | **570 / 599** |
| `for await` (`for-await-of`) | skipped | **1,227 / 1,234** |
| Promises | skipped | **626 / 729** |
| async functions | skipped | **84 / 93** |
| async generators | skipped | **517 / 623** |

A negative test used to pass on ANY throw. It does not any more: it must throw the
error `type:` it names, in the `phase:` it names. That correction alone removed
about 360 passes from the sample — tests that wanted a `SyntaxError` and were
being credited for an unrelated `TypeError`. Nearly 400 of them were dynamic-import
syntax tests "passing" because `import()` threw *no module host is installed* at
every single one. The number went down and became true; a suite scored on
"something went wrong" is not measuring the engine.

A skipped test is not a passing test either, and a suite that hides its hardest
sixth flatters itself. Unskipping those two categories found real bugs in both — the
module work is its own story, and the async work found a microtask queue that was
`let`-bound and therefore THREAD-LOCAL, so a job enqueued from inside a coroutine
went onto a queue nobody drained. `await` worked; awaiting an async function that
itself awaited never resumed.

That includes the full **Temporal** proposal (~96% of its 4,603 tests),
**Intl/ECMA-402** with an `en` locale (NumberFormat, DateTimeFormat, Collator,
Segmenter, PluralRules, ListFormat, RelativeTimeFormat, DisplayNames,
DurationFormat, Locale), **BigInt** (a CL integer *is* a BigInt — exact bignum
arithmetic for free), **UTF-16 code-unit strings** (astral scalars are surrogate
pairs), a clean-room **RegExp** engine with `\p{…}` Unicode property escapes
(via SBCL's `sb-unicode` tables), Proxy/Reflect, TypedArrays +
resizable/SharedArrayBuffer + Atomics, WeakRef and FinalizationRegistry,
generators and `async`/`await` (VM-frame suspension), Promises + a microtask
queue, classes with private members, **ES modules** — link, evaluate, live
bindings, cycles, namespaces, dynamic `import()`, `import.meta`, top-level await,
import attributes and JSON modules — and the rest of the modern language.

`inspect/module262.lisp` scores any one directory on its own, which is how the
per-area numbers above were taken. The longitudinal record is
`inspect/test262-history.tsv`.

Known gaps: `intl402/Temporal` (needs real calendars + IANA time zones),
multi-threaded Atomics (`$262.agent`), non-`en` locale data, tail calls, and the
proposals this deliberately does not implement — `import-defer`,
`source-phase-imports`, `import-text`, `import-bytes`, `uint8array-base64`.

## The seam (the reason it's built this way)

In ECMAScript every object *is* its internal methods — `[[Get]]`, `[[Set]]`,
`[[Has]]`, `[[Call]]`… Ordinary objects get defaults; Proxies and exotics
override them. shuttle's object model is built around **dispatchable internal
methods** from the start — which is both spec-correct *and* the exact seam a host
hangs bindings on. The engine owns the language; **weft owns the bindings** (it
knows its own DOM) and the reflow hook:

```lisp
(let ((realm (shuttle:make-realm)))
  ;; weft backs document/element/style with host objects; a [[Set]] trap is
  ;; where the language engine meets layout — mutate the DOM, relayout here:
  (shuttle:define-global realm "el"
    (shuttle:make-host-object realm
      :get (lambda (o key &optional r) ... )
      :set (lambda (o key v &optional r) (weft-set-and-relayout o key v) shuttle:*true*)))
  (shuttle:eval-script realm "el.textContent = 'hi ' + (1 + 2)"))   ; => fires the trap
```

Consumer API: `make-realm` (one per document) · `eval-script` · `define-global`
· `make-host-object` (the binding primitive) · `native-function` · `invoke`
(call a JS function from a host event/timer). Event-loop split: **shuttle owns
the microtask queue; weft owns macrotasks** (timers, DOM events).

## Architecture

`src/`: `value` (the value model + internal-method protocol — the seam) ·
`lex` · `parse` (Pratt) · `compile` (AST → bytecode) · `vm` (stack VM +
environments + closures + generator/async suspension) · `realm` (the consumer
API + the intrinsics kernel) · `regex` (backtracking RegExp engine) ·
`unicode-props` (Unicode property tables for `\p{…}`) · `builtins/` (the
standard library, one file per built-in group, each self-registering via
`register-builtin-installer`).

**Bytecode, not tree-walking** — deliberately. Generators and `async`/`await`
need to *suspend mid-evaluation*; an explicit VM stack makes save/resume natural
where a tree-walker would need a CPS rewrite. **GC is the host's** — JS objects
are CL objects; only `WeakMap`/`WeakRef` need weak references.

## Running the tests

```sh
sbcl --script inspect/self-test.lisp            # quick smoke (26 cases + the seam)
git clone --depth 1 https://github.com/tc39/test262 test262-full
inspect/run262.sh                               # full suite, batched + crash-isolated
SHUTTLE_TEST262=$PWD/test262-full SHUTTLE_SUB=built-ins/Temporal \
  sbcl --control-stack-size 256 --dynamic-space-size 4096 \
  --script inspect/test262-sub.lisp             # one subtree, prints each FAIL
```

## Security posture

Untrusted JavaScript is a tool for hardware attacks (Rowhammer, Spectre, cache
side channels) more than a source of engine bugs. shuttle is built to be a poor
tool for them — **no JIT**, single-agent `SharedArrayBuffer` (no timing thread),
no `WeakRef`/`FinalizationRegistry` oracle, checked bounds and no address
disclosure — and to slot into host-level containment. See
[`docs/actor-isolation.md`](docs/actor-isolation.md) for the contract with
[`modus`](https://github.com/modus-lisp) (a Lisp OS with actor isolation +
per-actor GC): one realm per actor, `postMessage` as copy-on-send message
passing, and a per-realm capability profile.

## Status

Working engine at 88% test262. Next: weft DOM bindings → Acid3.
MIT. Research / educational; not audited.
