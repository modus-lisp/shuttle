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

**41,404 / 47,058 runnable test262 tests (88.0%)** — measured with
`inspect/run262.sh` against a full checkout (modules and async-flagged tests are
skipped; 6,346 total). Per area:

| area | pass rate |
|---|---|
| `built-ins` | 94.8% |
| `language`  | 90.3% |
| `annexB`    | 89.4% |
| `harness`   | 98.0% |

That includes the full **Temporal** proposal (~96% of its 4,603 tests),
**Intl/ECMA-402** with an `en` locale (NumberFormat, DateTimeFormat, Collator,
Segmenter, PluralRules, ListFormat, RelativeTimeFormat, DisplayNames,
DurationFormat, Locale), **BigInt** (a CL integer *is* a BigInt — exact bignum
arithmetic for free), **UTF-16 code-unit strings** (astral scalars are surrogate
pairs), a clean-room **RegExp** engine with `\p{…}` Unicode property escapes
(via SBCL's `sb-unicode` tables), Proxy/Reflect, TypedArrays +
resizable/SharedArrayBuffer + Atomics, generators and `async`/`await` (VM-frame
suspension), Promises + a microtask queue, classes with private members, and
the rest of the modern language. The longitudinal record is
`inspect/test262-history.tsv` — every row a measured, committed state, from
12.4% to 88.0%.

Known gaps: `intl402/Temporal` (needs real calendars + IANA time zones),
multi-threaded Atomics (`$262.agent`), non-`en` locale data, ES modules, tail
calls.

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

## Status

Working engine at 88% test262. Next: weft DOM bindings → Acid3.
MIT. Research / educational; not audited.
