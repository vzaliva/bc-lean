/-
  Mirror: the residual interpreter agrees with the source big-step evaluator
  on source-shaped terms.

  `evalExprTerm` over `ExprTerm.ofExpr e` computes the same final results as
  `Bc.evalExpr` over `e` (with possibly different fuel).  Loops require extra
  statements because the small-step semantics unfolds `while`/`for` into
  `loopBody`/`forCheck`/`forUpdate` residual terms.
-/

import Bc.BigSmall.AntiEval
import Bc.BigSmall.SourceMono
import Bc.BigSmall.Bridge

namespace Bc

namespace BigSmall

open SmallStep

set_option maxHeartbeats 1600000

/-! ### Source-side continuations for loop and call shapes -/

/-- Source continuation of a while-loop body result. -/
def whileCont (m : Nat) (st : RuntimeState) (c : Expr) (b : Stmt) : Result Control :=
  match evalStmt m st b with
  | .ok st .normal => evalStmt m st (.while c b)
  | .ok st .break => .ok st .normal
  | .ok st ctl => .ok st ctl
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

/-- Source continuation of a for-loop update position. -/
def forUpdCont (m : Nat) (st : RuntimeState) (c u : Expr) (b : Stmt) : Result Control :=
  match evalExpr m st u with
  | .ok st _ => evalFor m st c u b
  | .control st ctl => .ok st ctl
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

/-- Source continuation of a for-loop body result. -/
def forBodyCont (m : Nat) (st : RuntimeState) (c u : Expr) (b : Stmt) : Result Control :=
  match evalStmt m st b with
  | .ok st .normal => forUpdCont m st c u b
  | .ok st .break => .ok st .normal
  | .ok st ctl => .ok st ctl
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

/-- Source continuation of an active function-call body. -/
def callBodyCont (m : Nat) (st : RuntimeState) (items : List BodyItem) : EvalResult Num :=
  match evalBody m st items with
  | .ok st .normal => .ok (popFrame st) Num.zero
  | .ok st (.return v?) => .ok (popFrame st) (returnValue v?)
  | .ok st .break => .runtimeError (popFrame st) "Break outside a loop"
  | .ok st .quit => .control (popFrame st) .quit
  | .outOfFuel st => .outOfFuel (popFrame st)
  | .runtimeError st msg => .runtimeError (popFrame st) msg

/-- Source evaluation of a statement group followed by remaining body items. -/
def stmtsThen (m : Nat) (st : RuntimeState) (ss : List Stmt) (items : List BodyItem) :
    Result Control :=
  match evalStmts m st ss with
  | .ok st .normal => evalBody m st items
  | .ok st c => .ok st c
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

/-! ### The mirror, by induction on residual fuel -/

structure MirrorProps (n : Nat) : Prop where
  expr : ∀ {st e r}, evalExprTerm n st (ExprTerm.ofExpr e) = r → EvalResultNotFuel r →
    ∃ m, evalExpr m st e = r
  rel : ∀ {st left rest r}, evalRelChainTerm n st left (ExprTerm.ofRelRest rest) = r →
    EvalResultNotFuel r → ∃ m, evalRelChain m st left rest = r
  lval : ∀ {st lv r}, evalLValTerm n st (LValTerm.ofLVal lv) = r → EvalResultNotFuel r →
    ∃ m, evalLValueTarget m st lv = r
  args : ∀ {st as r}, evalArgTerms n st (ArgTerm.ofArgs as) = r → EvalResultNotFuel r →
    ∃ m, evalArgValues m st as = r
  activeCall : ∀ {st items r},
    evalExprTerm n st (.activeCall (BodyTerm.ofBody items)) = r →
    EvalResultNotFuel r → ∃ m, callBodyCont m st items = r
  stmt : ∀ {st s r}, evalStmtTerm n st (StmtTerm.ofStmt s) = r → ResultNotFuel r →
    ∃ m, evalStmt m st s = r
  forCheck : ∀ {st c u b r},
    evalStmtTerm n st (.forCheck c (ExprTerm.ofExpr c) u (StmtTerm.ofStmt b)) = r →
    ResultNotFuel r → ∃ m, evalFor m st c u b = r
  forUpdate : ∀ {st c u b r},
    evalStmtTerm n st (.forUpdate c u (ExprTerm.ofExpr u) (StmtTerm.ofStmt b)) = r →
    ResultNotFuel r → ∃ m, forUpdCont m st c u b = r
  loopWhile : ∀ {st c b r},
    evalStmtTerm n st (.loopBody (StmtTerm.ofStmt b)
      (.while c (ExprTerm.ofExpr c) (StmtTerm.ofStmt b))) = r →
    ResultNotFuel r → ∃ m, whileCont m st c b = r
  loopFor : ∀ {st c u b r},
    evalStmtTerm n st (.loopBody (StmtTerm.ofStmt b)
      (.forUpdate c u (ExprTerm.ofExpr u) (StmtTerm.ofStmt b))) = r →
    ResultNotFuel r → ∃ m, forBodyCont m st c u b = r
  stmtsApp : ∀ {st ss items r},
    evalBodyTerm n st (.stmts (StmtTerm.ofStmts ss ++ BodyTerm.ofBodyItems items)) = r →
    ResultNotFuel r → ∃ m, stmtsThen m st ss items = r

private theorem ofExpr_bump_preIncr (arg : Expr) :
    ExprTerm.ofExpr (.unary .preIncr arg) =
      (match LValTerm.ofExpr? arg with
       | some target => ExprTerm.bump .preIncr target
       | none => ExprTerm.badBump .preIncr (ExprTerm.ofExpr arg)) := by
  rw [ExprTerm.ofExpr.eq_def]; rfl

private theorem ofExpr_bump_preDecr (arg : Expr) :
    ExprTerm.ofExpr (.unary .preDecr arg) =
      (match LValTerm.ofExpr? arg with
       | some target => ExprTerm.bump .preDecr target
       | none => ExprTerm.badBump .preDecr (ExprTerm.ofExpr arg)) := by
  rw [ExprTerm.ofExpr.eq_def]; rfl

private theorem ofExpr_bump_postIncr (arg : Expr) :
    ExprTerm.ofExpr (.unary .postIncr arg) =
      (match LValTerm.ofExpr? arg with
       | some target => ExprTerm.bump .postIncr target
       | none => ExprTerm.badBump .postIncr (ExprTerm.ofExpr arg)) := by
  rw [ExprTerm.ofExpr.eq_def]; rfl

private theorem ofExpr_bump_postDecr (arg : Expr) :
    ExprTerm.ofExpr (.unary .postDecr arg) =
      (match LValTerm.ofExpr? arg with
       | some target => ExprTerm.bump .postDecr target
       | none => ExprTerm.badBump .postDecr (ExprTerm.ofExpr arg)) := by
  rw [ExprTerm.ofExpr.eq_def]; rfl

/-- Shared handling of the four increment/decrement operators. The
`hof` hypothesis identifies the residual translation of the bump expression. -/
private theorem mirror_bump {k : Nat} {ih : MirrorProps k} {st : RuntimeState}
    {op : UnOp} {arg : Expr} {r : EvalResult Num}
    (hof : ExprTerm.ofExpr (.unary op arg) =
      (match LValTerm.ofExpr? arg with
       | some target => ExprTerm.bump op target
       | none => ExprTerm.badBump op (ExprTerm.ofExpr arg)))
    (h : evalExprTerm (k + 1) st (ExprTerm.ofExpr (.unary op arg)) = r)
    (hnf : EvalResultNotFuel r) :
    ∃ m, evalExpr m st (.unary op arg) = r := by
  rw [hof, LValTerm.ofExpr?_eq] at h
  cases op
  case neg =>
      rw [LValTerm.ofExpr?_eq] at hof
      cases hlv : lvalOfExpr? arg <;> simp [hlv, ExprTerm.ofExpr] at hof
  all_goals
    cases hlv : lvalOfExpr? arg with
    | none =>
        simp only [hlv, Option.map] at h
        rw [evalExprTerm] at h
        refine ⟨2, ?_⟩
        rw [evalExpr]; rw [evalUnary]
        simp only [hlv]
        exact h
    | some lv =>
        simp only [hlv, Option.map] at h
        rw [evalExprTerm] at h
        cases hsub : evalLValTerm k st (LValTerm.ofLVal lv) with
        | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
        | control stx c => exact absurd hsub evalLValTerm_no_control
        | ok st₂ t =>
            obtain ⟨m₁, hm₁⟩ := ih.lval hsub (by simp [EvalResultNotFuel])
            simp only [hsub] at h
            refine ⟨m₁ + 2, ?_⟩
            rw [evalExpr]; rw [evalUnary]
            simp only [hlv, hm₁]
            exact h
        | runtimeError st₂ msg =>
            obtain ⟨m₁, hm₁⟩ := ih.lval hsub (by simp [EvalResultNotFuel])
            simp only [hsub] at h
            refine ⟨m₁ + 2, ?_⟩
            rw [evalExpr]; rw [evalUnary]
            simp only [hlv, hm₁]
            exact h

private theorem forUpdCont_mono {n m st c u b r} (hnm : n ≤ m)
    (h : forUpdCont n st c u b = r) (hr : ResultNotFuel r) :
    forUpdCont m st c u b = r := by
  unfold forUpdCont at h ⊢
  cases hu : evalExpr n st u with
  | outOfFuel stx => simp only [hu] at h; exact notFuelR h hr
  | ok stU v =>
      rw [evalExpr_mono hnm hu (by simp [EvalResultNotFuel])]
      simp only [hu] at h
      exact evalFor_mono hnm h hr
  | control stU c' =>
      rw [evalExpr_mono hnm hu (by simp [EvalResultNotFuel])]
      simpa [hu] using h
  | runtimeError stU msg =>
      rw [evalExpr_mono hnm hu (by simp [EvalResultNotFuel])]
      simpa [hu] using h

/-- The `stmtsApp` field at level `k + 1`. -/
private theorem mirror_stmtsApp_field {k : Nat} (ih : MirrorProps k)
    {st : RuntimeState} {ss : List Stmt} {items : List BodyItem} {r : Result Control}
    (h : evalBodyTerm (k + 1) st
      (.stmts (StmtTerm.ofStmts ss ++ BodyTerm.ofBodyItems items)) = r)
    (hnf : ResultNotFuel r) : ∃ m, stmtsThen m st ss items = r := by
  induction items generalizing st ss r with
  | nil =>
      cases ss with
      | nil =>
          simp only [StmtTerm.ofStmts, BodyTerm.ofBodyItems, List.nil_append] at h
          rw [evalBodyTerm] at h
          refine ⟨1, ?_⟩
          unfold stmtsThen
          rw [evalStmts]
          simp only []
          rw [evalBody]
          exact h
      | cons s ss' =>
          simp only [StmtTerm.ofStmts, List.cons_append] at h
          rw [evalBodyTerm] at h
          cases hsub : evalStmtTerm k st (StmtTerm.ofStmt s) with
          | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
          | ok stB c =>
              obtain ⟨m₁, hm₁⟩ := ih.stmt hsub (by simp [ResultNotFuel])
              simp only [hsub] at h
              cases c with
              | normal =>
                  obtain ⟨m₂, hm₂⟩ := ih.stmtsApp h hnf
                  unfold stmtsThen at hm₂ ⊢
                  cases hss : evalStmts m₂ stB ss' with
                  | outOfFuel stx => simp only [hss] at hm₂; exact notFuelR hm₂ hnf
                  | ok stC c' =>
                      simp only [hss] at hm₂
                      refine ⟨max m₁ m₂ + 1, ?_⟩
                      rw [evalStmts]
                      simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                          (by simp [ResultNotFuel]),
                        evalStmts_mono (show m₂ ≤ max m₁ m₂ by omega) hss
                          (by simp [ResultNotFuel])]
                      cases c' with
                      | normal =>
                          exact evalBody_mono (show m₂ ≤ max m₁ m₂ + 1 by omega) hm₂ hnf
                      | «break» => exact hm₂
                      | «return» v? => exact hm₂
                      | quit => exact hm₂
                  | runtimeError stC msg =>
                      simp only [hss] at hm₂
                      refine ⟨max m₁ m₂ + 1, ?_⟩
                      rw [evalStmts]
                      simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                          (by simp [ResultNotFuel]),
                        evalStmts_mono (show m₂ ≤ max m₁ m₂ by omega) hss
                          (by simp [ResultNotFuel])]
                      exact hm₂
              | «break» =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
              | «return» v? =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
              | quit =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
          | runtimeError stB msg =>
              obtain ⟨m₁, hm₁⟩ := ih.stmt hsub (by simp [ResultNotFuel])
              simp only [hsub] at h
              refine ⟨m₁ + 1, ?_⟩
              unfold stmtsThen
              rw [evalStmts]
              simp only [hm₁]
              exact h
  | cons item rest ihItems =>
      cases ss with
      | cons s ss' =>
          simp only [StmtTerm.ofStmts, List.cons_append] at h
          rw [evalBodyTerm] at h
          cases hsub : evalStmtTerm k st (StmtTerm.ofStmt s) with
          | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
          | ok stB c =>
              obtain ⟨m₁, hm₁⟩ := ih.stmt hsub (by simp [ResultNotFuel])
              simp only [hsub] at h
              cases c with
              | normal =>
                  obtain ⟨m₂, hm₂⟩ := ih.stmtsApp h hnf
                  unfold stmtsThen at hm₂ ⊢
                  cases hss : evalStmts m₂ stB ss' with
                  | outOfFuel stx => simp only [hss] at hm₂; exact notFuelR hm₂ hnf
                  | ok stC c' =>
                      simp only [hss] at hm₂
                      refine ⟨max m₁ m₂ + 1, ?_⟩
                      rw [evalStmts]
                      simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                          (by simp [ResultNotFuel]),
                        evalStmts_mono (show m₂ ≤ max m₁ m₂ by omega) hss
                          (by simp [ResultNotFuel])]
                      cases c' with
                      | normal =>
                          exact evalBody_mono (show m₂ ≤ max m₁ m₂ + 1 by omega) hm₂ hnf
                      | «break» => exact hm₂
                      | «return» v? => exact hm₂
                      | quit => exact hm₂
                  | runtimeError stC msg =>
                      simp only [hss] at hm₂
                      refine ⟨max m₁ m₂ + 1, ?_⟩
                      rw [evalStmts]
                      simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                          (by simp [ResultNotFuel]),
                        evalStmts_mono (show m₂ ≤ max m₁ m₂ by omega) hss
                          (by simp [ResultNotFuel])]
                      exact hm₂
              | «break» =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
              | «return» v? =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
              | quit =>
                  refine ⟨m₁ + 1, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only [hm₁]
                  exact h
          | runtimeError stB msg =>
              obtain ⟨m₁, hm₁⟩ := ih.stmt hsub (by simp [ResultNotFuel])
              simp only [hsub] at h
              refine ⟨m₁ + 1, ?_⟩
              unfold stmtsThen
              rw [evalStmts]
              simp only [hm₁]
              exact h
      | nil =>
          cases item with
          | newline =>
              simp only [StmtTerm.ofStmts, BodyTerm.ofBodyItems, List.nil_append] at h
              obtain ⟨m, hm⟩ := ihItems (ss := []) (by
                simpa [StmtTerm.ofStmts, List.nil_append] using h) hnf
              unfold stmtsThen at hm
              cases m with
              | zero =>
                  simp only [evalStmts] at hm
                  exact notFuelR hm hnf
              | succ m' =>
                  rw [evalStmts] at hm
                  simp only [] at hm
                  refine ⟨m' + 2, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only []
                  rw [evalBody]
                  exact hm
          | stmts ssx =>
              simp only [StmtTerm.ofStmts, BodyTerm.ofBodyItems, List.nil_append] at h
              obtain ⟨m, hm⟩ := ihItems (ss := ssx) h hnf
              unfold stmtsThen at hm
              cases hss : evalStmts m st ssx with
              | outOfFuel stx => simp only [hss] at hm; exact notFuelR hm hnf
              | ok stC c =>
                  simp only [hss] at hm
                  refine ⟨m + 2, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only []
                  rw [evalBody]
                  simp only [evalStmts_mono (show m ≤ m + 1 by omega) hss
                    (by simp [ResultNotFuel])]
                  cases c with
                  | normal => exact evalBody_mono (show m ≤ m + 1 by omega) hm hnf
                  | «break» => exact hm
                  | «return» v? => exact hm
                  | quit => exact hm
              | runtimeError stC msg =>
                  simp only [hss] at hm
                  refine ⟨m + 2, ?_⟩
                  unfold stmtsThen
                  rw [evalStmts]
                  simp only []
                  rw [evalBody]
                  simp only [evalStmts_mono (show m ≤ m + 1 by omega) hss
                    (by simp [ResultNotFuel])]
                  exact hm

/-- The `loopWhile` field at level `k + 1`. -/
private theorem mirror_loopWhile_field {k : Nat} (ih : MirrorProps k)
    {st : RuntimeState} {c : Expr} {b : Stmt} {r : Result Control}
    (h : evalStmtTerm (k + 1) st (.loopBody (StmtTerm.ofStmt b)
      (.while c (ExprTerm.ofExpr c) (StmtTerm.ofStmt b))) = r)
    (hnf : ResultNotFuel r) : ∃ m, whileCont m st c b = r := by
  rw [evalStmtTerm] at h
  cases hb : evalStmtTerm k st (StmtTerm.ofStmt b) with
  | outOfFuel stx => simp only [hb] at h; exact notFuelR h hnf
  | ok stB c' =>
      obtain ⟨m₁, hm₁⟩ := ih.stmt hb (by simp [ResultNotFuel])
      simp only [hb] at h
      cases c' with
      | normal =>
          have h' : evalStmtTerm k stB (StmtTerm.ofStmt (.while c b)) = r := by
            simpa [StmtTerm.ofStmt] using h
          obtain ⟨m₂, hm₂⟩ := ih.stmt h' hnf
          refine ⟨max m₁ m₂, ?_⟩
          unfold whileCont
          simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
            (by simp [ResultNotFuel])]
          exact evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
      | «break» =>
          refine ⟨m₁, ?_⟩
          unfold whileCont
          simp only [hm₁]
          exact h
      | «return» v? =>
          refine ⟨m₁, ?_⟩
          unfold whileCont
          simp only [hm₁]
          exact h
      | quit =>
          refine ⟨m₁, ?_⟩
          unfold whileCont
          simp only [hm₁]
          exact h
  | runtimeError stB msg =>
      obtain ⟨m₁, hm₁⟩ := ih.stmt hb (by simp [ResultNotFuel])
      simp only [hb] at h
      refine ⟨m₁, ?_⟩
      unfold whileCont
      simp only [hm₁]
      exact h

/-- The `loopFor` field at level `k + 1`. -/
private theorem mirror_loopFor_field {k : Nat} (ih : MirrorProps k)
    {st : RuntimeState} {c u : Expr} {b : Stmt} {r : Result Control}
    (h : evalStmtTerm (k + 1) st (.loopBody (StmtTerm.ofStmt b)
      (.forUpdate c u (ExprTerm.ofExpr u) (StmtTerm.ofStmt b))) = r)
    (hnf : ResultNotFuel r) : ∃ m, forBodyCont m st c u b = r := by
  rw [evalStmtTerm] at h
  cases hb : evalStmtTerm k st (StmtTerm.ofStmt b) with
  | outOfFuel stx => simp only [hb] at h; exact notFuelR h hnf
  | ok stB c' =>
      obtain ⟨m₁, hm₁⟩ := ih.stmt hb (by simp [ResultNotFuel])
      simp only [hb] at h
      cases c' with
      | normal =>
          obtain ⟨m₂, hm₂⟩ := ih.forUpdate h hnf
          refine ⟨max m₁ m₂, ?_⟩
          unfold forBodyCont
          simp only [evalStmt_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
            (by simp [ResultNotFuel])]
          exact forUpdCont_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
      | «break» =>
          refine ⟨m₁, ?_⟩
          unfold forBodyCont
          simp only [hm₁]
          exact h
      | «return» v? =>
          refine ⟨m₁, ?_⟩
          unfold forBodyCont
          simp only [hm₁]
          exact h
      | quit =>
          refine ⟨m₁, ?_⟩
          unfold forBodyCont
          simp only [hm₁]
          exact h
  | runtimeError stB msg =>
      obtain ⟨m₁, hm₁⟩ := ih.stmt hb (by simp [ResultNotFuel])
      simp only [hb] at h
      refine ⟨m₁, ?_⟩
      unfold forBodyCont
      simp only [hm₁]
      exact h

/-- The `forUpdate` field at level `k + 1`. -/
private theorem mirror_forUpdate_field {k : Nat} (ih : MirrorProps k)
    {st : RuntimeState} {c u : Expr} {b : Stmt} {r : Result Control}
    (h : evalStmtTerm (k + 1) st
      (.forUpdate c u (ExprTerm.ofExpr u) (StmtTerm.ofStmt b)) = r)
    (hnf : ResultNotFuel r) : ∃ m, forUpdCont m st c u b = r := by
  rw [evalStmtTerm] at h
  cases hsub : evalExprTerm k st (ExprTerm.ofExpr u) with
  | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
  | ok st₂ v =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      obtain ⟨m₂, hm₂⟩ := ih.forCheck h hnf
      refine ⟨max m₁ m₂, ?_⟩
      unfold forUpdCont
      simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
        (by simp [EvalResultNotFuel])]
      exact evalFor_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
  | control st₂ c' =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      refine ⟨m₁, ?_⟩
      unfold forUpdCont
      simp only [hm₁]
      exact h
  | runtimeError st₂ msg =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      refine ⟨m₁, ?_⟩
      unfold forUpdCont
      simp only [hm₁]
      exact h

/-- The `forCheck` field at level `k + 1`. -/
private theorem mirror_forCheck_field {k : Nat} (ih : MirrorProps k)
    {st : RuntimeState} {c u : Expr} {b : Stmt} {r : Result Control}
    (h : evalStmtTerm (k + 1) st
      (.forCheck c (ExprTerm.ofExpr c) u (StmtTerm.ofStmt b)) = r)
    (hnf : ResultNotFuel r) : ∃ m, evalFor m st c u b = r := by
  rw [evalStmtTerm] at h
  cases hsub : evalExprTerm k st (ExprTerm.ofExpr c) with
  | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
  | ok st₂ v =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      cases hz : v.isZero with
      | true =>
          simp only [hz, if_true] at h
          refine ⟨m₁ + 1, ?_⟩
          rw [evalFor]
          simp only [hm₁, hz]
          simp
          exact h
      | false =>
          simp only [hz, Bool.false_eq_true, if_false] at h
          obtain ⟨m₂, hm₂⟩ := ih.loopFor h hnf
          refine ⟨max m₁ m₂ + 1, ?_⟩
          rw [evalFor]
          simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
            (by simp [EvalResultNotFuel]), hz]
          simp only [Bool.false_eq_true, if_false]
          unfold forBodyCont at hm₂
          cases hb : evalStmt m₂ st₂ b with
          | outOfFuel stx => simp only [hb] at hm₂; exact notFuelR hm₂ hnf
          | ok stB c' =>
              simp only [hb] at hm₂
              simp only [evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                (by simp [ResultNotFuel])]
              cases c' with
              | normal =>
                  unfold forUpdCont at hm₂
                  cases hu : evalExpr m₂ stB u with
                  | outOfFuel stx => simp only [hu] at hm₂; exact notFuelR hm₂ hnf
                  | ok stU vu =>
                      simp only [hu] at hm₂
                      simp only [evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hu
                        (by simp [EvalResultNotFuel])]
                      exact evalFor_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
                  | control stU cu =>
                      simp only [hu] at hm₂
                      simp only [evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hu
                        (by simp [EvalResultNotFuel])]
                      exact hm₂
                  | runtimeError stU msg =>
                      simp only [hu] at hm₂
                      simp only [evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hu
                        (by simp [EvalResultNotFuel])]
                      exact hm₂
              | «break» => exact hm₂
              | «return» v? => exact hm₂
              | quit => exact hm₂
          | runtimeError stB msg =>
              simp only [hb] at hm₂
              simp only [evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                (by simp [ResultNotFuel])]
              exact hm₂
  | control st₂ c' =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      exact ⟨m₁ + 1, by rw [evalFor]; simp only [hm₁]; exact h⟩
  | runtimeError st₂ msg =>
      obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
      simp only [hsub] at h
      exact ⟨m₁ + 1, by rw [evalFor]; simp only [hm₁]; exact h⟩

/-- The `stmt` field at level `k + 1`. -/
private theorem mirror_stmt_field {k : Nat} (ih : MirrorProps k) :
    ∀ {st : RuntimeState} {s : Stmt} {r : Result Control},
    evalStmtTerm (k + 1) st (StmtTerm.ofStmt s) = r → ResultNotFuel r →
    ∃ m, evalStmt m st s = r := by
  intro st s r h hnf
  cases s with
  | expr e =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      cases hsub : evalExprTerm k st (ExprTerm.ofExpr e) with
      | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
      | ok st₂ v =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
      | control st₂ c =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
      | runtimeError st₂ msg =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
  | str sv =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      exact ⟨1, by rw [evalStmt]; exact h⟩
  | auto params =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      exact ⟨1, by rw [evalStmt]; exact h⟩
  | «if» cond thenB =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      cases hsub : evalExprTerm k st (ExprTerm.ofExpr cond) with
      | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
      | ok st₂ v =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          cases hz : v.isZero with
          | true =>
              simp only [hz, if_true] at h
              refine ⟨m₁ + 1, ?_⟩
              rw [evalStmt]
              simp only [hm₁, hz]
              simp
              exact h
          | false =>
              simp only [hz, Bool.false_eq_true, if_false] at h
              obtain ⟨m₂, hm₂⟩ := ih.stmt h hnf
              refine ⟨max m₁ m₂ + 1, ?_⟩
              rw [evalStmt]
              simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                (by simp [EvalResultNotFuel]), hz]
              simp only [Bool.false_eq_true, if_false]
              exact evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
      | control st₂ c =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
      | runtimeError st₂ msg =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
  | «while» c b =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      cases hsub : evalExprTerm k st (ExprTerm.ofExpr c) with
      | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
      | ok st₂ v =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          cases hz : v.isZero with
          | true =>
              simp only [hz, if_true] at h
              refine ⟨m₁ + 1, ?_⟩
              rw [evalStmt]
              simp only [hm₁, hz]
              simp
              exact h
          | false =>
              simp only [hz, Bool.false_eq_true, if_false] at h
              obtain ⟨m₂, hm₂⟩ := ih.loopWhile h hnf
              refine ⟨max m₁ m₂ + 1, ?_⟩
              rw [evalStmt]
              simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                (by simp [EvalResultNotFuel]), hz]
              simp only [Bool.false_eq_true, if_false]
              unfold whileCont at hm₂
              cases hb : evalStmt m₂ st₂ b with
              | outOfFuel stx => simp only [hb] at hm₂; exact notFuelR hm₂ hnf
              | ok stB c' =>
                  simp only [hb] at hm₂
                  simp only [evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                    (by simp [ResultNotFuel])]
                  cases c' with
                  | normal => exact evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
                  | «break» => exact hm₂
                  | «return» v? => exact hm₂
                  | quit => exact hm₂
              | runtimeError stB msg =>
                  simp only [hb] at hm₂
                  simp only [evalStmt_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                    (by simp [ResultNotFuel])]
                  exact hm₂
      | control st₂ c' =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
      | runtimeError st₂ msg =>
          obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
          simp only [hsub] at h
          exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
  | «for» init c u b =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      cases k with
      | zero =>
          simp only [evalStmtTerm] at h
          exact notFuelR h hnf
      | succ k' =>
          rw [evalStmtTerm] at h
          cases hsub : evalExprTerm k' st (ExprTerm.ofExpr init) with
          | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
          | ok stI v =>
              have hsub' := evalExprTerm_mono (Nat.le_succ k') hsub
                (by simp [EvalResultNotFuel])
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub' (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              obtain ⟨m₂, hm₂⟩ := ih.forCheck h hnf
              refine ⟨max m₁ m₂ + 1, ?_⟩
              rw [evalStmt]
              simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                (by simp [EvalResultNotFuel])]
              exact evalFor_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂ hnf
          | control stI c' =>
              have hc' : c' ≠ .normal := evalExprTerm_control_ne_normal hsub
              have hsub' := evalExprTerm_mono (Nat.le_succ k') hsub
                (by simp [EvalResultNotFuel])
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub' (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              refine ⟨m₁ + 1, ?_⟩
              rw [evalStmt]
              simp only [hm₁]
              cases c' with
              | normal => exact absurd rfl hc'
              | «break» => exact h
              | «return» v? => exact h
              | quit => exact h
          | runtimeError stI msg =>
              have hsub' := evalExprTerm_mono (Nat.le_succ k') hsub
                (by simp [EvalResultNotFuel])
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub' (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
  | «break» =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      exact ⟨1, by rw [evalStmt]; exact h⟩
  | «return» e? =>
      cases e? with
      | none =>
          simp only [StmtTerm.ofStmt] at h
          rw [evalStmtTerm] at h
          exact ⟨1, by rw [evalStmt]; exact h⟩
      | some e =>
          simp only [StmtTerm.ofStmt] at h
          rw [evalStmtTerm] at h
          cases hsub : evalExprTerm k st (ExprTerm.ofExpr e) with
          | outOfFuel stx => simp only [hsub] at h; exact notFuelR h hnf
          | ok st₂ v =>
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
          | control st₂ c =>
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
          | runtimeError st₂ msg =>
              obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
              simp only [hsub] at h
              exact ⟨m₁ + 1, by rw [evalStmt]; simp only [hm₁]; exact h⟩
  | quit =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      exact ⟨1, by rw [evalStmt]; exact h⟩
  | block body =>
      simp only [StmtTerm.ofStmt] at h
      rw [evalStmtTerm] at h
      have h' : evalBodyTerm k st
          (.stmts (StmtTerm.ofStmts [] ++ BodyTerm.ofBodyItems body)) = r := by
        simpa [StmtTerm.ofStmts] using h
      obtain ⟨m₂, hm₂⟩ := ih.stmtsApp h' hnf
      unfold stmtsThen at hm₂
      cases m₂ with
      | zero =>
          simp only [evalStmts] at hm₂
          exact notFuelR hm₂ hnf
      | succ m' =>
          rw [evalStmts] at hm₂
          simp only [] at hm₂
          exact ⟨m' + 2, by rw [evalStmt]; exact hm₂⟩


private theorem mirrorProps : ∀ n, MirrorProps n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (intros; rename_i h hr; simp [evalExprTerm, evalRelChainTerm, evalLValTerm,
          evalArgTerms, evalStmtTerm, evalBodyTerm] at h; subst h;
         first
         | exact absurd hr (by simp [EvalResultNotFuel])
         | exact absurd hr (by simp [ResultNotFuel]))
  | succ k ih =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- expr
      · intro st e r h hnf
        cases e with
        | num raw =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            exact ⟨1, by rw [evalExpr]; exact h⟩
        | var name =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            exact ⟨1, by rw [evalExpr]; exact h⟩
        | special v =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            exact ⟨1, by rw [evalExpr]; exact h⟩
        | arrayAccess name idx =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            cases hsub : evalExprTerm k st (ExprTerm.ofExpr idx) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | ok st₂ v =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
            | control st₂ c =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
        | assign lhs op rhs =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            cases hsub : evalLValTerm k st (LValTerm.ofLVal lhs) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | control stx c => exact absurd hsub evalLValTerm_no_control
            | ok st₂ t =>
                obtain ⟨m₁, hm₁⟩ := ih.lval hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                cases hsub2 : evalExprTerm k st₂ (ExprTerm.ofExpr rhs) with
                | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                | ok st₃ v =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 2, ?_⟩
                    rw [evalExpr]
                    rw [evalAssign]
                    simp only [evalLValueTarget_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | control st₃ c =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 2, ?_⟩
                    rw [evalExpr]
                    rw [evalAssign]
                    simp only [evalLValueTarget_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | runtimeError st₃ msg =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 2, ?_⟩
                    rw [evalExpr]
                    rw [evalAssign]
                    simp only [evalLValueTarget_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.lval hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                refine ⟨m₁ + 2, ?_⟩
                rw [evalExpr]
                rw [evalAssign]
                simp only [hm₁]
                exact h
        | rel first rest =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            cases hsub : evalExprTerm k st (ExprTerm.ofExpr first) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | ok st₂ left =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                cases hsub2 : evalRelChainTerm k st₂ left (ExprTerm.ofRelRest rest) with
                | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                | ok stx vx =>
                    obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | control stx c =>
                    obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | runtimeError stx msg =>
                    obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
            | control st₂ c =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
        | bin op lhs rhs =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            cases hsub : evalExprTerm k st (ExprTerm.ofExpr lhs) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | ok st₂ a =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                cases hsub2 : evalExprTerm k st₂ (ExprTerm.ofExpr rhs) with
                | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                | ok st₃ b =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | control st₃ c =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
                | runtimeError st₃ msg =>
                    obtain ⟨m₂, hm₂⟩ := ih.expr hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    refine ⟨max m₁ m₂ + 1, ?_⟩
                    rw [evalExpr]
                    simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                        (by simp [EvalResultNotFuel]),
                      evalExpr_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                        (by simp [EvalResultNotFuel])]
                    exact h
            | control st₂ c =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalExpr]; simp only [hm₁]; exact h⟩
        | unary op arg =>
            cases op with
            | neg =>
                simp only [ExprTerm.ofExpr] at h
                rw [evalExprTerm] at h
                cases hsub : evalExprTerm k st (ExprTerm.ofExpr arg) with
                | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
                | ok st₂ v =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalUnary]; simp only [hm₁]; exact h⟩
                | control st₂ c =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalUnary]; simp only [hm₁]; exact h⟩
                | runtimeError st₂ msg =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalUnary]; simp only [hm₁]; exact h⟩
            | preIncr => exact mirror_bump (ih := ih) (ofExpr_bump_preIncr arg) h hnf
            | preDecr => exact mirror_bump (ih := ih) (ofExpr_bump_preDecr arg) h hnf
            | postIncr => exact mirror_bump (ih := ih) (ofExpr_bump_postIncr arg) h hnf
            | postDecr => exact mirror_bump (ih := ih) (ofExpr_bump_postDecr arg) h hnf
        | call name args =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            cases hlk : lookupFunction st name with
            | none =>
                simp only [hlk] at h
                exact ⟨2, by rw [evalExpr]; rw [evalCall]; simp only [hlk]; exact h⟩
            | some defn =>
                simp only [hlk] at h
                cases hsub : evalArgTerms k st (ArgTerm.ofArgs args) with
                | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
                | ok stA av =>
                    obtain ⟨m₁, hm₁⟩ := ih.args hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    cases hbind : bindParams
                        { stA with frames := { constBase := stA.ibase } :: stA.frames }
                        defn.params av with
                    | error msg =>
                        simp only [hbind] at h
                        refine ⟨m₁ + 2, ?_⟩
                        rw [evalExpr]; rw [evalCall]
                        simp only [hlk, hm₁, hbind]
                        exact h
                    | ok stB =>
                        simp only [hbind] at h
                        obtain ⟨m₂, hm₂⟩ := ih.activeCall h hnf
                        unfold callBodyCont at hm₂
                        cases hb : evalBody m₂ (bindAutoDecls stB (collectAutos defn.body))
                            defn.body with
                        | outOfFuel stx =>
                            simp only [hb] at hm₂
                            exact notFuelE hm₂ hnf
                        | ok stC c =>
                            simp only [hb] at hm₂
                            refine ⟨max m₁ m₂ + 2, ?_⟩
                            rw [evalExpr]; rw [evalCall]
                            simp only [hlk,
                              evalArgValues_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                                (by simp [EvalResultNotFuel]), hbind,
                              evalBody_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                                (by simp [ResultNotFuel])]
                            cases c <;> exact hm₂
                        | runtimeError stC msg =>
                            simp only [hb] at hm₂
                            refine ⟨max m₁ m₂ + 2, ?_⟩
                            rw [evalExpr]; rw [evalCall]
                            simp only [hlk,
                              evalArgValues_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                                (by simp [EvalResultNotFuel]), hbind,
                              evalBody_mono (show m₂ ≤ max m₁ m₂ by omega) hb
                                (by simp [ResultNotFuel])]
                            exact hm₂
                | control stA c =>
                    obtain ⟨m₁, hm₁⟩ := ih.args hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalCall]; simp only [hlk, hm₁]; exact h⟩
                | runtimeError stA msg =>
                    obtain ⟨m₁, hm₁⟩ := ih.args hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalCall]; simp only [hlk, hm₁]; exact h⟩
        | builtin fn arg? =>
            cases arg? with
            | none =>
                simp only [ExprTerm.ofExpr] at h
                rw [evalExprTerm] at h
                exact ⟨2, by rw [evalExpr]; rw [evalBuiltin]; exact h⟩
            | some a =>
                simp only [ExprTerm.ofExpr] at h
                rw [evalExprTerm] at h
                cases hsub : evalExprTerm k st (ExprTerm.ofExpr a) with
                | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
                | ok st₂ v =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalBuiltin]; simp only [hm₁]; exact h⟩
                | control st₂ c =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalBuiltin]; simp only [hm₁]; exact h⟩
                | runtimeError st₂ msg =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 2, by
                      rw [evalExpr]; rw [evalBuiltin]; simp only [hm₁]; exact h⟩
        | paren body =>
            simp only [ExprTerm.ofExpr] at h
            rw [evalExprTerm] at h
            obtain ⟨m₁, hm₁⟩ := ih.expr h hnf
            exact ⟨m₁ + 1, by rw [evalExpr]; exact hm₁⟩
      -- rel
      · intro st left rest r h hnf
        cases rest with
        | nil =>
            simp only [ExprTerm.ofRelRest] at h
            rw [evalRelChainTerm] at h
            exact ⟨1, by rw [evalRelChain]; exact h⟩
        | cons hd tail =>
            obtain ⟨op, e⟩ := hd
            simp only [ExprTerm.ofRelRest] at h
            rw [evalRelChainTerm] at h
            cases hsub : evalExprTerm k st (ExprTerm.ofExpr e) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | ok st₂ right =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                cases tail with
                | nil =>
                    simp only [ExprTerm.ofRelRest] at h
                    refine ⟨m₁ + 1, ?_⟩
                    rw [evalRelChain]
                    simp only [hm₁, List.isEmpty]
                    exact h
                | cons p t2 =>
                    obtain ⟨op2, e2⟩ := p
                    simp only [ExprTerm.ofRelRest] at h
                    cases hsub2 : evalRelChainTerm k st₂ (boolNum (applyRel op left right))
                        (ExprTerm.ofRelRest ((op2, e2) :: t2)) with
                    | outOfFuel stx =>
                        simp only [ExprTerm.ofRelRest] at hsub2
                        simp only [hsub2] at h
                        exact notFuelE h hnf
                    | ok stx vx =>
                        obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                        simp only [ExprTerm.ofRelRest] at hsub2
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalRelChain]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]), List.isEmpty,
                          evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
                    | control stx c =>
                        obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                        simp only [ExprTerm.ofRelRest] at hsub2
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalRelChain]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]), List.isEmpty,
                          evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
                    | runtimeError stx msg =>
                        obtain ⟨m₂, hm₂⟩ := ih.rel hsub2 (by simp [EvalResultNotFuel])
                        simp only [ExprTerm.ofRelRest] at hsub2
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalRelChain]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]), List.isEmpty,
                          evalRelChain_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
            | control st₂ c =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalRelChain]; simp only [hm₁]; exact h⟩
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalRelChain]; simp only [hm₁]; exact h⟩
      -- lval
      · intro st lv r h hnf
        cases lv with
        | var name =>
            simp only [LValTerm.ofLVal] at h
            rw [evalLValTerm] at h
            exact ⟨1, by rw [evalLValueTarget]; exact h⟩
        | special v =>
            simp only [LValTerm.ofLVal] at h
            rw [evalLValTerm] at h
            exact ⟨1, by rw [evalLValueTarget]; exact h⟩
        | array name idx =>
            simp only [LValTerm.ofLVal] at h
            rw [evalLValTerm] at h
            cases hsub : evalExprTerm k st (ExprTerm.ofExpr idx) with
            | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
            | ok st₂ v =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalLValueTarget]; simp only [hm₁]; exact h⟩
            | control st₂ c =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalLValueTarget]; simp only [hm₁]; exact h⟩
            | runtimeError st₂ msg =>
                obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                simp only [hsub] at h
                exact ⟨m₁ + 1, by rw [evalLValueTarget]; simp only [hm₁]; exact h⟩
      -- args
      · intro st as r h hnf
        cases as with
        | nil =>
            simp only [ArgTerm.ofArgs] at h
            rw [evalArgTerms] at h
            exact ⟨1, by rw [evalArgValues]; exact h⟩
        | cons a rest =>
            cases a with
            | expr e =>
                simp only [ArgTerm.ofArgs, ArgTerm.ofArg] at h
                rw [evalArgTerms] at h
                cases hsub : evalExprTerm k st (ExprTerm.ofExpr e) with
                | outOfFuel stx => simp only [hsub] at h; exact notFuelE h hnf
                | ok st₂ v =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    cases hsub2 : evalArgTerms k st₂ (ArgTerm.ofArgs rest) with
                    | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                    | ok st₃ vs =>
                        obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalArgValues]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]),
                          evalArgValues_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
                    | control st₃ c =>
                        obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalArgValues]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]),
                          evalArgValues_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
                    | runtimeError st₃ msg =>
                        obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                        simp only [hsub2] at h
                        refine ⟨max m₁ m₂ + 1, ?_⟩
                        rw [evalArgValues]
                        simp only [evalExpr_mono (show m₁ ≤ max m₁ m₂ by omega) hm₁
                            (by simp [EvalResultNotFuel]),
                          evalArgValues_mono (show m₂ ≤ max m₁ m₂ by omega) hm₂
                            (by simp [EvalResultNotFuel])]
                        exact h
                | control st₂ c =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 1, by rw [evalArgValues]; simp only [hm₁]; exact h⟩
                | runtimeError st₂ msg =>
                    obtain ⟨m₁, hm₁⟩ := ih.expr hsub (by simp [EvalResultNotFuel])
                    simp only [hsub] at h
                    exact ⟨m₁ + 1, by rw [evalArgValues]; simp only [hm₁]; exact h⟩
            | arrayRef name =>
                simp only [ArgTerm.ofArgs, ArgTerm.ofArg] at h
                rw [evalArgTerms] at h
                cases hsub2 : evalArgTerms k st (ArgTerm.ofArgs rest) with
                | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                | ok st₃ vs =>
                    obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    exact ⟨m₂ + 1, by rw [evalArgValues]; simp only [hm₂]; exact h⟩
                | control st₃ c =>
                    obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    exact ⟨m₂ + 1, by rw [evalArgValues]; simp only [hm₂]; exact h⟩
                | runtimeError st₃ msg =>
                    obtain ⟨m₂, hm₂⟩ := ih.args hsub2 (by simp [EvalResultNotFuel])
                    simp only [hsub2] at h
                    exact ⟨m₂ + 1, by rw [evalArgValues]; simp only [hm₂]; exact h⟩
      -- activeCall
      · intro st items r h hnf
        simp only [BodyTerm.ofBody] at h
        rw [evalExprTerm] at h
        cases hb : evalBodyTerm k st (.stmts (BodyTerm.ofBodyItems items)) with
        | outOfFuel stx => simp only [hb] at h; exact notFuelE h hnf
        | ok stB c =>
            have hb' : evalBodyTerm k st
                (.stmts (StmtTerm.ofStmts [] ++ BodyTerm.ofBodyItems items)) =
                .ok stB c := by simpa [StmtTerm.ofStmts] using hb
            obtain ⟨m₂, hm₂⟩ := ih.stmtsApp hb' (by simp [ResultNotFuel])
            simp only [hb] at h
            unfold stmtsThen at hm₂
            cases m₂ with
            | zero => simp [evalStmts] at hm₂
            | succ m₂' =>
                rw [evalStmts] at hm₂
                simp only [] at hm₂
                refine ⟨m₂' + 1, ?_⟩
                unfold callBodyCont
                rw [hm₂]
                exact h
        | runtimeError stB msg =>
            have hb' : evalBodyTerm k st
                (.stmts (StmtTerm.ofStmts [] ++ BodyTerm.ofBodyItems items)) =
                .runtimeError stB msg := by simpa [StmtTerm.ofStmts] using hb
            obtain ⟨m₂, hm₂⟩ := ih.stmtsApp hb' (by simp [ResultNotFuel])
            simp only [hb] at h
            unfold stmtsThen at hm₂
            cases m₂ with
            | zero => simp [evalStmts] at hm₂
            | succ m₂' =>
                rw [evalStmts] at hm₂
                simp only [] at hm₂
                refine ⟨m₂' + 1, ?_⟩
                unfold callBodyCont
                rw [hm₂]
                exact h
      -- stmt
      · exact mirror_stmt_field ih
      -- forCheck
      · exact mirror_forCheck_field ih
      -- forUpdate
      · exact mirror_forUpdate_field ih
      -- loopWhile
      · exact mirror_loopWhile_field ih
      -- loopFor
      · exact mirror_loopFor_field ih
      -- stmtsApp
      · exact mirror_stmtsApp_field ih

/-- Public mirror for a top-level statement group: a converging residual body
evaluation over `ofStmts ss` is reproduced by the source `evalStmts`. -/
theorem mirror_stmts {n : Nat} {st : RuntimeState} {ss : List Stmt} {r : Result Control}
    (h : evalBodyTerm n st (.stmts (StmtTerm.ofStmts ss)) = r)
    (hnf : ResultNotFuel r) : ∃ m, evalStmts m st ss = r := by
  have h' : evalBodyTerm n st
      (.stmts (StmtTerm.ofStmts ss ++ BodyTerm.ofBodyItems [])) = r := by
    simpa [BodyTerm.ofBodyItems] using h
  obtain ⟨m, hm⟩ := (mirrorProps n).stmtsApp h' hnf
  unfold stmtsThen at hm
  cases hss : evalStmts m st ss with
  | outOfFuel stx => simp only [hss] at hm; exact notFuelR hm hnf
  | ok stC c =>
      simp only [hss] at hm
      cases c with
      | normal =>
          cases m with
          | zero => simp [evalStmts] at hss
          | succ m' =>
              simp only [evalBody] at hm
              refine ⟨m' + 1, ?_⟩
              rw [hss]
              exact hm
      | «break» => exact ⟨m, hss.trans hm⟩
      | «return» v? => exact ⟨m, hss.trans hm⟩
      | quit => exact ⟨m, hss.trans hm⟩
  | runtimeError stC msg =>
      simp only [hss] at hm
      exact ⟨m, hss.trans hm⟩

end BigSmall

end Bc
