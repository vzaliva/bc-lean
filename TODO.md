# bc-lean — open TODOs

Cleanliness / quality items not directly on the big-step ↔ small-step
equivalence critical path. (The equivalence theorem itself is tracked in
`REPORT.md` Step 13; its one remaining `sorry` is
`Bc/BigSmall/Backward.lean : termination_transfer`.)

These were surfaced by an earlier code review and are recorded here so they are
not lost.

---

## #6 — Dead `SmallStep.evalBody` / `runBodyConfig`

`Bc/SmallStep.lean:345-355` defines `runBodyConfig` (a fuel-driven loop running a
body to completion) and `evalBody` on top of it. Nothing outside `SmallStep`
references them — `step`'s `.activeCall` case uses `stepBody` inline instead.
Besides being dead, it reintroduces a fuel-bounded big-step-style driver *inside*
the module framed as "fuel-free structural" semantics, which muddies that story.

**Action:** remove `runBodyConfig` + `evalBody`, or, if kept for testing, move
them out of the structural module and document why. First re-grep for any
`Main.lean` / test / proof use before deleting.

## #7 — Quit handling is split and partially redundant

`TopItemTerm.ofTopItem` (`Bc/SmallStep.lean:314`) already collapses a
quit-containing statement list to `[.stmt .quit]`, yet `step`
(`Bc/SmallStep.lean:332`) *also* recomputes `TopItemTerm.containsQuit` on the
head item on **every** step. The per-step rescan only does real work for
`funDef` items; for statement items it is redundant.

**Action:** consolidate the quit policy in one place (decide it once at
conversion time, or once per top-item rather than per-step). Note: the
equivalence proof's `containsQuit`-alignment lemmas (`Bc/BigSmall.lean`) lean on
the current shape, so re-check those if this is changed.

## #8 — Small-step stepping is quadratic

Every `step` re-traverses the entire head term to locate the redex (and re-runs
the quit scan), so a run is ~O(term-size² · steps). This is why the Makefile
needs `SMALL_STEP_FUEL ?= 100000000` vs `BIG_STEP_FUEL ?= 200000`
(`Makefile:5-6`) — a ~500× gap. Fine as a *definition*, but not a usable
interpreter at scale, and the huge constant is a smell.

**Action (larger):** if the small-step semantics should also be runnable at
scale, switch the residual representation to a focus / zipper / continuation
stack so stepping is O(1)–O(depth). This is a semantics-shape change; weigh
against the equivalence proof, which is written over the current residual terms.

## #9 — Truncation-aware `Num` metatheory (remaining part)

Foundation done: `Bc/Num.lean` has `Num.value : Rat`, `Num.equiv`, the relop
characterisation, and exact-arithmetic homomorphisms (`value_neg/add/sub`).
**Missing:** truncation-aware lemmas for the lossy, scale-dependent operations
`mulWithScale`, `div?`, `modulo?`, `pow?` (`Bc/Num.lean:281-313`). These are *not*
plain ℚ homomorphisms — bc truncates to a target `scale` — so they need
statements relating `value (op a b s)` to the truncation of the exact rational
result at scale `s`.

**Action:** add the truncation lemmas to `Bc/Num.lean`, giving a canonical-form /
denotational story for the lossy ops.
