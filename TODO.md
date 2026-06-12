# bc-lean — open TODOs

Cleanliness / quality items not directly on the big-step ↔ small-step
equivalence critical path. The equivalence theorem itself is tracked in
`REPORT.md` Step 13 and is now fully proved.

These were surfaced by an earlier code review and are recorded here so they are
not lost.

---

## #8 — Small-step stepping is quadratic

Every `step` re-traverses the current residual term to locate the next redex, so
a run is ~O(term-size² · steps). This is why the Makefile needs
`SMALL_STEP_FUEL ?= 100000000` vs `BIG_STEP_FUEL ?= 200000` (`Makefile:5-6`) —
a ~500× gap. Fine as a *definition*, but not a usable interpreter at scale, and
the huge constant is a smell.

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
