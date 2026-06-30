# shuttle

**A Lisp-native JavaScript engine.** Clean-room — no FFI, no embedded V8/QuickJS.
A loom's shuttle is the one moving part that drives the weft thread across the
warp; a JS engine is exactly that — the active force that pushes changes through
the page.

shuttle is the JavaScript engine for [`weft`](https://github.com/modus-lisp) (a
pure-CL web engine), built the way `scribe`'s `open-font`/`shape-run` seam was —
**consumable up front**. The pipeline is `source → bytecode → stack VM`; the
oracle is **test262**, the official ECMAScript conformance suite (the WPT/
html5lib pattern). Running it is what finally lets weft run Acid3.

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

## What works (the v0 slice — `inspect/self-test.lisp`, 26/26)

Numbers (IEEE-754 doubles, full coercion + the `+` string/number duality),
strings, `var`/assignment/compound assignment, `if`/`while`/ternary/`&&`/`||`
(short-circuit), `typeof`, `===`/`==`, **functions + closures + recursion**,
arrow functions, **methods with `this`**, `new` + prototypes, object & array
literals, member/computed access, a few intrinsics (`Math`, `console`,
`Array.prototype.push`/`join`), and the **host-object seam** end to end.

## Architecture

`src/`: `value` (the value model + internal-method protocol — the seam) ·
`lex` · `parse` (Pratt) · `compile` (AST → bytecode) · `vm` (stack VM +
environments + closures) · `realm` (the consumer API + minimal intrinsics).

**Bytecode, not tree-walking** — deliberately. Generators and `async`/`await`
need to *suspend mid-evaluation*; an explicit VM stack makes save/resume natural
where a tree-walker would need a CPS rewrite. **GC is the host's** — JS objects
are CL objects; only `WeakMap`/`WeakRef` need weak references.

## The carve (how this gets built out)

- **Wide library surface** — the built-in library (`Array.prototype.*`,
  `String.prototype.*`, `Math.*`, `Date`, `JSON`, `Map`/`Set`…), each method a
  test262-pinned unit. This is most of the code and embarrassingly parallel.
- **Coupled strong-tier core** — the lexer, parser, bytecode compiler + VM, and
  the runtime semantics (descriptors, prototype chain, completion records,
  exceptions, hoisting/TDZ, strict mode).
- **Standalone sub-repos** — a **RegExp** engine and **`dtoa`** (shortest
  round-trip number↔string), each gnarly, self-contained, heavily test262'd.

## Ladder ahead

`for`/`switch`/`try`-`catch`/`throw` → the built-in library →
RegExp + dtoa → generators/`async`/Promises + the job queue → modules → **weft
DOM bindings → Acid3**. Known v0 gaps: UTF-16 code-unit strings, shortest-
round-trip number formatting, full ASI, `let`/`const` block scoping.

## Status

Skeleton — the seam, the VM, and a working slice stand; the language and library
grow from here against test262. Published to `modus-lisp/shuttle` when it's woven.
MIT. Research / educational; not audited.
