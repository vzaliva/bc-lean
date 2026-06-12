/-
  Preservation of the runtime `stopped` flag along non-quit small-step runs.

  These facts are proof-only infrastructure for the big-step/small-step
  equivalence.  The executable semantics remain in `Bc.SmallStep`.
-/

import Bc.BigStep
import Bc.BigSmall.Run
import Bc.SmallStep

namespace Bc

namespace BigSmall

open SmallStep

set_option maxHeartbeats 800000

/-! ### Small-step call-entry preservation -/

private theorem stopped_popFrame (st : RuntimeState) :
    (popFrame st).stopped = st.stopped := by
  rfl

private theorem enterFunction_next_stopped {st defn argValues st' e'}
    (h : enterFunction st defn argValues = .next st' e') :
    st'.stopped = st.stopped := by
  unfold enterFunction at h
  cases hbind : bindParams ({ st with frames := { constBase := st.ibase } :: st.frames })
      defn.params argValues with
  | error msg =>
      simp [hbind] at h
  | ok stBound =>
      simp [hbind] at h
      rcases h with ⟨rfl, rfl⟩
      calc
        (bindAutoDecls stBound (collectAutos defn.body)).stopped = stBound.stopped :=
          stopped_bindAutoDecls (collectAutos defn.body) stBound
        _ = ({ st with frames := { constBase := st.ibase } :: st.frames }).stopped :=
          stopped_bindParams hbind
        _ = st.stopped := rfl

/-! ### Big-step stopped preservation -/

mutual

private theorem evalExpr_ok_stopped {fuel st e st' v}
    (h : evalExpr fuel st e = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalExpr] at h
  | succ fuel' =>
      cases e with
      | num raw =>
          simp [evalExpr] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | var name =>
          simp [evalExpr] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | special v =>
          simp [evalExpr] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | arrayAccess name idx =>
          simp only [evalExpr] at h
          cases hidx : evalExpr fuel' st idx with
          | ok st₁ idxNum =>
              cases hindex : indexOfNum? idxNum with
              | ok idxNat =>
                  simp [hidx, hindex] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_ensureArrayId st₁ name).trans (evalExpr_ok_stopped hidx)
              | error msg =>
                  simp [hidx, hindex] at h
          | control st₁ control =>
              simp [hidx] at h
          | outOfFuel st₁ =>
              simp [hidx] at h
          | runtimeError st₁ msg =>
              simp [hidx] at h
      | assign lhs op rhs =>
          change evalAssign fuel' st lhs op rhs = .ok st' v at h
          exact evalAssign_ok_stopped (fuel := fuel') (st := st) (lhs := lhs) (op := op)
            (rhs := rhs) (st' := st') (v := v) h
      | rel first rest =>
          simp only [evalExpr] at h
          cases hfirst : evalExpr fuel' st first with
          | ok st₁ left =>
              simp [hfirst] at h
              exact (evalRelChain_ok_stopped h).trans (evalExpr_ok_stopped hfirst)
          | control st₁ control =>
              simp [hfirst] at h
          | outOfFuel st₁ =>
              simp [hfirst] at h
          | runtimeError st₁ msg =>
              simp [hfirst] at h
      | bin op lhs rhs =>
          simp only [evalExpr] at h
          cases hlhs : evalExpr fuel' st lhs with
          | ok st₁ left =>
              cases hrhs : evalExpr fuel' st₁ rhs with
              | ok st₂ right =>
                  cases happly : applyBin? op left right st₂.scale with
                  | ok result =>
                      simp [hlhs, hrhs, happly] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact (evalExpr_ok_stopped hrhs).trans (evalExpr_ok_stopped hlhs)
                  | error msg =>
                      simp [hlhs, hrhs, happly] at h
              | control st₂ control =>
                  simp [hlhs, hrhs] at h
              | outOfFuel st₂ =>
                  simp [hlhs, hrhs] at h
              | runtimeError st₂ msg =>
                  simp [hlhs, hrhs] at h
          | control st₁ control =>
              simp [hlhs] at h
          | outOfFuel st₁ =>
              simp [hlhs] at h
          | runtimeError st₁ msg =>
              simp [hlhs] at h
      | unary op arg =>
          change evalUnary fuel' st op arg = .ok st' v at h
          exact evalUnary_ok_stopped (fuel := fuel') (st := st) (op := op) (arg := arg)
            (st' := st') (v := v) h
      | call name args =>
          change evalCall fuel' st name args = .ok st' v at h
          exact evalCall_ok_stopped (fuel := fuel') (st := st) (name := name)
            (args := args) (st' := st') (v := v) h
      | builtin fn arg =>
          change evalBuiltin fuel' st fn arg = .ok st' v at h
          exact evalBuiltin_ok_stopped (fuel := fuel') (st := st) (fn := fn) (arg := arg)
            (st' := st') (v := v) h
      | paren body =>
          simp [evalExpr] at h
          exact evalExpr_ok_stopped h

private theorem evalExpr_control_stopped {fuel st e st' c}
    (h : evalExpr fuel st e = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalExpr] at h
  | succ fuel' =>
      cases e with
      | num raw =>
          simp [evalExpr] at h
      | var name =>
          simp [evalExpr] at h
      | special v =>
          simp [evalExpr] at h
      | arrayAccess name idx =>
          simp only [evalExpr] at h
          cases hidx : evalExpr fuel' st idx with
          | ok st₁ idxNum =>
              cases hindex : indexOfNum? idxNum <;> simp [hidx, hindex] at h
          | control st₁ control =>
              simp [hidx] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hidx hc
          | outOfFuel st₁ =>
              simp [hidx] at h
          | runtimeError st₁ msg =>
              simp [hidx] at h
      | assign lhs op rhs =>
          change evalAssign fuel' st lhs op rhs = .control st' c at h
          exact evalAssign_control_stopped (fuel := fuel') (st := st) (lhs := lhs)
            (op := op) (rhs := rhs) (st' := st') (c := c) h hc
      | rel first rest =>
          simp only [evalExpr] at h
          cases hfirst : evalExpr fuel' st first with
          | ok st₁ left =>
              simp [hfirst] at h
              exact (evalRelChain_control_stopped h hc).trans (evalExpr_ok_stopped hfirst)
          | control st₁ control =>
              simp [hfirst] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hfirst hc
          | outOfFuel st₁ =>
              simp [hfirst] at h
          | runtimeError st₁ msg =>
              simp [hfirst] at h
      | bin op lhs rhs =>
          simp only [evalExpr] at h
          cases hlhs : evalExpr fuel' st lhs with
          | ok st₁ left =>
              cases hrhs : evalExpr fuel' st₁ rhs with
              | ok st₂ right =>
                  cases happly : applyBin? op left right st₂.scale <;>
                    simp [hlhs, hrhs, happly] at h
              | control st₂ control =>
                  simp [hlhs, hrhs] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (evalExpr_control_stopped hrhs hc).trans (evalExpr_ok_stopped hlhs)
              | outOfFuel st₂ =>
                  simp [hlhs, hrhs] at h
              | runtimeError st₂ msg =>
                  simp [hlhs, hrhs] at h
          | control st₁ control =>
              simp [hlhs] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hlhs hc
          | outOfFuel st₁ =>
              simp [hlhs] at h
          | runtimeError st₁ msg =>
              simp [hlhs] at h
      | unary op arg =>
          change evalUnary fuel' st op arg = .control st' c at h
          exact evalUnary_control_stopped (fuel := fuel') (st := st) (op := op)
            (arg := arg) (st' := st') (c := c) h hc
      | call name args =>
          change evalCall fuel' st name args = .control st' c at h
          exact evalCall_control_stopped (fuel := fuel') (st := st) (name := name)
            (args := args) (st' := st') (c := c) h hc
      | builtin fn arg =>
          change evalBuiltin fuel' st fn arg = .control st' c at h
          exact evalBuiltin_control_stopped (fuel := fuel') (st := st) (fn := fn)
            (arg := arg) (st' := st') (c := c) h hc
      | paren body =>
          simp [evalExpr] at h
          exact evalExpr_control_stopped h hc

private theorem evalRelChain_ok_stopped {fuel st left rest st' v}
    (h : evalRelChain fuel st left rest = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalRelChain] at h
  | succ fuel' =>
      cases rest with
      | nil =>
          simp [evalRelChain] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons head tail =>
          rcases head with ⟨op, rhs⟩
          simp only [evalRelChain] at h
          cases hrhs : evalExpr fuel' st rhs with
          | ok st₁ right =>
              by_cases htail : tail.isEmpty
              · simp [hrhs, htail] at h
                rcases h with ⟨rfl, rfl⟩
                exact evalExpr_ok_stopped hrhs
              · simp [hrhs, htail] at h
                exact (evalRelChain_ok_stopped h).trans (evalExpr_ok_stopped hrhs)
          | control st₁ control =>
              simp [hrhs] at h
          | outOfFuel st₁ =>
              simp [hrhs] at h
          | runtimeError st₁ msg =>
              simp [hrhs] at h

private theorem evalRelChain_control_stopped {fuel st left rest st' c}
    (h : evalRelChain fuel st left rest = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalRelChain] at h
  | succ fuel' =>
      cases rest with
      | nil =>
          simp [evalRelChain] at h
      | cons head tail =>
          rcases head with ⟨op, rhs⟩
          simp only [evalRelChain] at h
          cases hrhs : evalExpr fuel' st rhs with
          | ok st₁ right =>
              by_cases htail : tail.isEmpty
              · simp [hrhs, htail] at h
              · simp [hrhs, htail] at h
                exact (evalRelChain_control_stopped h hc).trans (evalExpr_ok_stopped hrhs)
          | control st₁ control =>
              simp [hrhs] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hrhs hc
          | outOfFuel st₁ =>
              simp [hrhs] at h
          | runtimeError st₁ msg =>
              simp [hrhs] at h

private theorem evalLValueTarget_ok_stopped {fuel st lv st' target}
    (h : evalLValueTarget fuel st lv = .ok st' target) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalLValueTarget] at h
  | succ fuel' =>
      cases lv with
      | var n =>
          simp [evalLValueTarget] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | special v =>
          simp [evalLValueTarget] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | array name idx =>
          simp only [evalLValueTarget] at h
          cases hidx : evalExpr fuel' st idx with
          | ok st₁ idxNum =>
              cases hindex : indexOfNum? idxNum with
              | ok idxNat =>
                  simp [hidx, hindex] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_ensureArrayId st₁ name).trans (evalExpr_ok_stopped hidx)
              | error msg =>
                  simp [hidx, hindex] at h
          | control st₁ control =>
              simp [hidx] at h
          | outOfFuel st₁ =>
              simp [hidx] at h
          | runtimeError st₁ msg =>
              simp [hidx] at h

private theorem evalLValueTarget_control_stopped {fuel st lv st' c}
    (h : evalLValueTarget fuel st lv = .control st' c) (_hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalLValueTarget] at h
  | succ fuel' =>
      cases lv with
      | var n =>
          simp [evalLValueTarget] at h
      | special v =>
          simp [evalLValueTarget] at h
      | array name idx =>
          simp only [evalLValueTarget] at h
          cases hidx : evalExpr fuel' st idx with
          | ok st₁ idxNum =>
              cases hindex : indexOfNum? idxNum <;> simp [hidx, hindex] at h
          | control st₁ control =>
              simp [hidx] at h
          | outOfFuel st₁ =>
              simp [hidx] at h
          | runtimeError st₁ msg =>
              simp [hidx] at h

private theorem evalAssign_ok_stopped {fuel st lhs op rhs st' v}
    (h : evalAssign fuel st lhs op rhs = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalAssign] at h
  | succ fuel' =>
      simp only [evalAssign] at h
      cases hlhs : evalLValueTarget fuel' st lhs with
      | ok st₁ target =>
          cases hrhs : evalExpr fuel' st₁ rhs with
          | ok st₂ rhsValue =>
              cases happly : applyAssign? op (readLValueTarget st₂ target) rhsValue st₂.scale with
              | ok result =>
                  simp [hlhs, hrhs, happly] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_writeLValueTarget st₂ target result).trans
                    ((evalExpr_ok_stopped hrhs).trans (evalLValueTarget_ok_stopped hlhs))
              | error msg =>
                  simp [hlhs, hrhs, happly] at h
          | control st₂ control =>
              simp [hlhs, hrhs] at h
          | outOfFuel st₂ =>
              simp [hlhs, hrhs] at h
          | runtimeError st₂ msg =>
              simp [hlhs, hrhs] at h
      | control st₁ control =>
          simp [hlhs] at h
      | outOfFuel st₁ =>
          simp [hlhs] at h
      | runtimeError st₁ msg =>
          simp [hlhs] at h

private theorem evalAssign_control_stopped {fuel st lhs op rhs st' c}
    (h : evalAssign fuel st lhs op rhs = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalAssign] at h
  | succ fuel' =>
      simp only [evalAssign] at h
      cases hlhs : evalLValueTarget fuel' st lhs with
      | ok st₁ target =>
          cases hrhs : evalExpr fuel' st₁ rhs with
          | ok st₂ rhsValue =>
              cases happly : applyAssign? op (readLValueTarget st₂ target) rhsValue st₂.scale <;>
                simp [hlhs, hrhs, happly] at h
          | control st₂ control =>
              simp [hlhs, hrhs] at h
              rcases h with ⟨rfl, rfl⟩
              exact (evalExpr_control_stopped hrhs hc).trans
                (evalLValueTarget_ok_stopped hlhs)
          | outOfFuel st₂ =>
              simp [hlhs, hrhs] at h
          | runtimeError st₂ msg =>
              simp [hlhs, hrhs] at h
      | control st₁ control =>
          simp [hlhs] at h
          rcases h with ⟨rfl, rfl⟩
          exact evalLValueTarget_control_stopped hlhs hc
      | outOfFuel st₁ =>
          simp [hlhs] at h
      | runtimeError st₁ msg =>
          simp [hlhs] at h

private theorem evalUnary_ok_stopped {fuel st op arg st' v}
    (h : evalUnary fuel st op arg = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalUnary] at h
  | succ fuel' =>
      cases op with
      | neg =>
          simp only [evalUnary] at h
          cases harg : evalExpr fuel' st arg with
          | ok st₁ value =>
              simp [harg] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_ok_stopped harg
          | control st₁ control =>
              simp [harg] at h
          | outOfFuel st₁ =>
              simp [harg] at h
          | runtimeError st₁ msg =>
              simp [harg] at h
      | preIncr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none =>
              simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_bumpLValueTarget st₁ target true).trans
                    (evalLValueTarget_ok_stopped htarget)
              | control st₁ control =>
                  simp [hlv, htarget] at h
              | outOfFuel st₁ =>
                  simp [hlv, htarget] at h
              | runtimeError st₁ msg =>
                  simp [hlv, htarget] at h
      | preDecr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none =>
              simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_bumpLValueTarget st₁ target false).trans
                    (evalLValueTarget_ok_stopped htarget)
              | control st₁ control =>
                  simp [hlv, htarget] at h
              | outOfFuel st₁ =>
                  simp [hlv, htarget] at h
              | runtimeError st₁ msg =>
                  simp [hlv, htarget] at h
      | postIncr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none =>
              simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_bumpLValueTarget st₁ target true).trans
                    (evalLValueTarget_ok_stopped htarget)
              | control st₁ control =>
                  simp [hlv, htarget] at h
              | outOfFuel st₁ =>
                  simp [hlv, htarget] at h
              | runtimeError st₁ msg =>
                  simp [hlv, htarget] at h
      | postDecr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none =>
              simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact (stopped_bumpLValueTarget st₁ target false).trans
                    (evalLValueTarget_ok_stopped htarget)
              | control st₁ control =>
                  simp [hlv, htarget] at h
              | outOfFuel st₁ =>
                  simp [hlv, htarget] at h
              | runtimeError st₁ msg =>
                  simp [hlv, htarget] at h

private theorem evalUnary_control_stopped {fuel st op arg st' c}
    (h : evalUnary fuel st op arg = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalUnary] at h
  | succ fuel' =>
      cases op with
      | neg =>
          simp only [evalUnary] at h
          cases harg : evalExpr fuel' st arg with
          | ok st₁ value =>
              simp [harg] at h
          | control st₁ control =>
              simp [harg] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped harg hc
          | outOfFuel st₁ =>
              simp [harg] at h
          | runtimeError st₁ msg =>
              simp [harg] at h
      | preIncr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none => simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target => simp [hlv, htarget] at h
              | control st₁ control =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalLValueTarget_control_stopped htarget hc
              | outOfFuel st₁ => simp [hlv, htarget] at h
              | runtimeError st₁ msg => simp [hlv, htarget] at h
      | preDecr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none => simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target => simp [hlv, htarget] at h
              | control st₁ control =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalLValueTarget_control_stopped htarget hc
              | outOfFuel st₁ => simp [hlv, htarget] at h
              | runtimeError st₁ msg => simp [hlv, htarget] at h
      | postIncr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none => simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target => simp [hlv, htarget] at h
              | control st₁ control =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalLValueTarget_control_stopped htarget hc
              | outOfFuel st₁ => simp [hlv, htarget] at h
              | runtimeError st₁ msg => simp [hlv, htarget] at h
      | postDecr =>
          simp only [evalUnary] at h
          cases hlv : lvalOfExpr? arg with
          | none => simp [hlv] at h
          | some lv =>
              cases htarget : evalLValueTarget fuel' st lv with
              | ok st₁ target => simp [hlv, htarget] at h
              | control st₁ control =>
                  simp [hlv, htarget] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalLValueTarget_control_stopped htarget hc
              | outOfFuel st₁ => simp [hlv, htarget] at h
              | runtimeError st₁ msg => simp [hlv, htarget] at h

private theorem evalBuiltin_ok_stopped {fuel st fn arg st' v}
    (h : evalBuiltin fuel st fn arg = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalBuiltin] at h
  | succ fuel' =>
      cases arg with
      | none =>
          simp [evalBuiltin] at h
      | some e =>
          simp only [evalBuiltin] at h
          cases he : evalExpr fuel' st e with
          | ok st₁ value =>
              cases happly : applyBuiltin? fn value st₁.scale with
              | ok result =>
                  simp [he, happly] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalExpr_ok_stopped he
              | error msg =>
                  simp [he, happly] at h
          | control st₁ control =>
              simp [he] at h
          | outOfFuel st₁ =>
              simp [he] at h
          | runtimeError st₁ msg =>
              simp [he] at h

private theorem evalBuiltin_control_stopped {fuel st fn arg st' c}
    (h : evalBuiltin fuel st fn arg = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalBuiltin] at h
  | succ fuel' =>
      cases arg with
      | none =>
          simp [evalBuiltin] at h
      | some e =>
          simp only [evalBuiltin] at h
          cases he : evalExpr fuel' st e with
          | ok st₁ value =>
              cases happly : applyBuiltin? fn value st₁.scale <;> simp [he, happly] at h
          | control st₁ control =>
              simp [he] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped he hc
          | outOfFuel st₁ =>
              simp [he] at h
          | runtimeError st₁ msg =>
              simp [he] at h

private theorem evalArgValues_ok_stopped {fuel st args st' values}
    (h : evalArgValues fuel st args = .ok st' values) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalArgValues] at h
  | succ fuel' =>
      cases args with
      | nil =>
          simp [evalArgValues] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons arg rest =>
          cases arg with
          | expr e =>
              simp only [evalArgValues] at h
              cases he : evalExpr fuel' st e with
              | ok st₁ value =>
                  cases hrest : evalArgValues fuel' st₁ rest with
                  | ok st₂ valuesRest =>
                      simp [he, hrest] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact (evalArgValues_ok_stopped hrest).trans (evalExpr_ok_stopped he)
                  | control st₂ control =>
                      simp [he, hrest] at h
                  | outOfFuel st₂ =>
                      simp [he, hrest] at h
                  | runtimeError st₂ msg =>
                      simp [he, hrest] at h
              | control st₁ control =>
                  simp [he] at h
              | outOfFuel st₁ =>
                  simp [he] at h
              | runtimeError st₁ msg =>
                  simp [he] at h
          | arrayRef name =>
              simp only [evalArgValues] at h
              cases hrest : evalArgValues fuel' st rest with
              | ok st₁ valuesRest =>
                  simp [hrest] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalArgValues_ok_stopped hrest
              | control st₁ control =>
                  simp [hrest] at h
              | outOfFuel st₁ =>
                  simp [hrest] at h
              | runtimeError st₁ msg =>
                  simp [hrest] at h

private theorem evalArgValues_control_stopped {fuel st args st' c}
    (h : evalArgValues fuel st args = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalArgValues] at h
  | succ fuel' =>
      cases args with
      | nil =>
          simp [evalArgValues] at h
      | cons arg rest =>
          cases arg with
          | expr e =>
              simp only [evalArgValues] at h
              cases he : evalExpr fuel' st e with
              | ok st₁ value =>
                  cases hrest : evalArgValues fuel' st₁ rest with
                  | ok st₂ valuesRest =>
                      simp [he, hrest] at h
                  | control st₂ control =>
                      simp [he, hrest] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact (evalArgValues_control_stopped hrest hc).trans
                        (evalExpr_ok_stopped he)
                  | outOfFuel st₂ =>
                      simp [he, hrest] at h
                  | runtimeError st₂ msg =>
                      simp [he, hrest] at h
              | control st₁ control =>
                  simp [he] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalExpr_control_stopped he hc
              | outOfFuel st₁ =>
                  simp [he] at h
              | runtimeError st₁ msg =>
                  simp [he] at h
          | arrayRef name =>
              simp only [evalArgValues] at h
              cases hrest : evalArgValues fuel' st rest with
              | ok st₁ valuesRest =>
                  simp [hrest] at h
              | control st₁ control =>
                  simp [hrest] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalArgValues_control_stopped hrest hc
              | outOfFuel st₁ =>
                  simp [hrest] at h
              | runtimeError st₁ msg =>
                  simp [hrest] at h

private theorem evalCall_ok_stopped {fuel st name args st' v}
    (h : evalCall fuel st name args = .ok st' v) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalCall] at h
  | succ fuel' =>
      simp only [evalCall] at h
      cases hlookup : lookupFunction st name with
      | none =>
          simp [hlookup] at h
      | some defn =>
          cases hargs : evalArgValues fuel' st args with
          | ok stArgs argValues =>
              simp [hlookup, hargs] at h
              cases hbind : bindParams
                  ({ stArgs with frames := { constBase := stArgs.ibase } :: stArgs.frames })
                  defn.params argValues with
              | error msg =>
                  simp [hbind] at h
              | ok stBound =>
                  cases hbody : evalBody fuel' (bindAutoDecls stBound (collectAutos defn.body))
                      defn.body with
                  | ok stBody control =>
                      cases control <;> simp [hbind, hbody] at h
                      · rcases h with ⟨rfl, rfl⟩
                        calc
                          ({ stBody with frames := stBody.frames.drop 1 } : RuntimeState).stopped =
                              stBody.stopped := rfl
                          _ = (bindAutoDecls stBound (collectAutos defn.body)).stopped :=
                              evalBody_normal_stopped hbody
                          _ = stBound.stopped :=
                              stopped_bindAutoDecls (collectAutos defn.body) stBound
                          _ = ({ stArgs with frames :=
                                { constBase := stArgs.ibase } :: stArgs.frames } : RuntimeState).stopped :=
                              stopped_bindParams hbind
                          _ = stArgs.stopped := rfl
                          _ = st.stopped := evalArgValues_ok_stopped hargs
                      · rcases h with ⟨rfl, rfl⟩
                        calc
                          ({ stBody with frames := stBody.frames.drop 1 } : RuntimeState).stopped =
                              stBody.stopped := rfl
                          _ = (bindAutoDecls stBound (collectAutos defn.body)).stopped :=
                              evalBody_control_stopped hbody (by intro hq; cases hq)
                          _ = stBound.stopped :=
                              stopped_bindAutoDecls (collectAutos defn.body) stBound
                          _ = ({ stArgs with frames :=
                                { constBase := stArgs.ibase } :: stArgs.frames } : RuntimeState).stopped :=
                              stopped_bindParams hbind
                          _ = stArgs.stopped := rfl
                          _ = st.stopped := evalArgValues_ok_stopped hargs
                  | outOfFuel stBody =>
                      simp [hbind, hbody] at h
                  | runtimeError stBody msg =>
                      simp [hbind, hbody] at h
          | control stArgs control =>
              simp [hlookup, hargs] at h
          | outOfFuel stArgs =>
              simp [hlookup, hargs] at h
          | runtimeError stArgs msg =>
              simp [hlookup, hargs] at h

private theorem evalCall_control_stopped {fuel st name args st' c}
    (h : evalCall fuel st name args = .control st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalCall] at h
  | succ fuel' =>
      simp only [evalCall] at h
      cases hlookup : lookupFunction st name with
      | none =>
          simp [hlookup] at h
      | some defn =>
          cases hargs : evalArgValues fuel' st args with
          | ok stArgs argValues =>
              simp [hlookup, hargs] at h
              cases hbind : bindParams
                  ({ stArgs with frames := { constBase := stArgs.ibase } :: stArgs.frames })
                  defn.params argValues with
              | error msg =>
                  simp [hbind] at h
              | ok stBound =>
                  cases hbody : evalBody fuel' (bindAutoDecls stBound (collectAutos defn.body))
                      defn.body with
                  | ok stBody control =>
                      cases control <;> simp [hbind, hbody] at h
                      · rcases h with ⟨rfl, rfl⟩
                        exact False.elim (hc rfl)
                  | outOfFuel stBody =>
                      simp [hbind, hbody] at h
                  | runtimeError stBody msg =>
                      simp [hbind, hbody] at h
          | control stArgs control =>
              simp [hlookup, hargs] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalArgValues_control_stopped hargs hc
          | outOfFuel stArgs =>
              simp [hlookup, hargs] at h
          | runtimeError stArgs msg =>
              simp [hlookup, hargs] at h

private theorem evalStmt_normal_stopped {fuel st stmt st'}
    (h : evalStmt fuel st stmt = .ok st' .normal) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalStmt] at h
  | succ fuel' =>
      cases stmt with
      | expr e =>
          simp only [evalStmt] at h
          cases he : evalExpr fuel' st e with
          | ok st₁ value =>
              by_cases htop : isTopAssignment e
              · simp [he, htop] at h
                cases h
                exact evalExpr_ok_stopped he
              · simp [he, htop] at h
                cases h
                exact (stopped_printNumLine st₁ value).trans (evalExpr_ok_stopped he)
          | control st₁ control =>
              simp [he] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped he (by intro hq; cases hq)
          | outOfFuel st₁ =>
              simp [he] at h
          | runtimeError st₁ msg =>
              simp [he] at h
      | str s =>
          simp [evalStmt] at h
          cases h
          exact stopped_appendOutput st (decodeBcString s)
      | auto params =>
          simp [evalStmt] at h
          cases h
          rfl
      | «if» cond thenBranch =>
          simp only [evalStmt] at h
          cases hcond : evalExpr fuel' st cond with
          | ok st₁ n =>
              by_cases hz : n.isZero
              · simp [hcond, hz] at h
                cases h
                exact evalExpr_ok_stopped hcond
              · simp [hcond, hz] at h
                exact (evalStmt_normal_stopped h).trans (evalExpr_ok_stopped hcond)
          | control st₁ control =>
              simp [hcond] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hcond (by intro hq; cases hq)
          | outOfFuel st₁ =>
              simp [hcond] at h
          | runtimeError st₁ msg =>
              simp [hcond] at h
      | «while» cond body =>
          simp only [evalStmt] at h
          cases hcond : evalExpr fuel' st cond with
          | ok st₁ n =>
              by_cases hz : n.isZero
              · simp [hcond, hz] at h
                cases h
                exact evalExpr_ok_stopped hcond
              · simp [hcond, hz] at h
                cases hbody : evalStmt fuel' st₁ body with
                | ok st₂ control =>
                    cases control <;> simp [hbody] at h
                    · exact (evalStmt_normal_stopped h).trans
                        ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond))
                    · cases h
                      exact (evalStmt_control_stopped hbody (by intro hq; cases hq)).trans
                        (evalExpr_ok_stopped hcond)
                | outOfFuel st₂ =>
                    simp [hbody] at h
                | runtimeError st₂ msg =>
                    simp [hbody] at h
          | control st₁ control =>
              simp [hcond] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hcond (by intro hq; cases hq)
          | outOfFuel st₁ =>
              simp [hcond] at h
          | runtimeError st₁ msg =>
              simp [hcond] at h
      | «for» init cond update body =>
          simp only [evalStmt] at h
          cases hinit : evalExpr fuel' st init with
          | ok st₁ value =>
              simp [hinit] at h
              exact (evalFor_normal_stopped h).trans (evalExpr_ok_stopped hinit)
          | control st₁ control =>
              simp [hinit] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hinit (by intro hq; cases hq)
          | outOfFuel st₁ =>
              simp [hinit] at h
          | runtimeError st₁ msg =>
              simp [hinit] at h
      | «break» =>
          simp [evalStmt] at h
      | «return» value? =>
          cases value? with
          | none =>
              simp [evalStmt] at h
          | some e =>
              simp only [evalStmt] at h
              cases he : evalExpr fuel' st e with
              | ok st₁ value => simp [he] at h
              | control st₁ control =>
                  simp [he] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalExpr_control_stopped he (by intro hq; cases hq)
              | outOfFuel st₁ => simp [he] at h
              | runtimeError st₁ msg => simp [he] at h
      | «quit» =>
          simp [evalStmt] at h
      | «block» body =>
          simp [evalStmt] at h
          exact evalBody_normal_stopped h

private theorem evalStmt_control_stopped {fuel st stmt st' c}
    (h : evalStmt fuel st stmt = .ok st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  by_cases hnormal : c = .normal
  · subst c
    exact evalStmt_normal_stopped h
  cases fuel with
  | zero =>
      simp [evalStmt] at h
  | succ fuel' =>
      cases stmt with
      | expr e =>
          simp only [evalStmt] at h
          cases he : evalExpr fuel' st e with
          | ok st₁ value =>
              by_cases htop : isTopAssignment e
              · simp [he, htop] at h
                rcases h with ⟨_, hcNormal⟩
                exact False.elim (hnormal hcNormal.symm)
              · simp [he, htop] at h
                rcases h with ⟨_, hcNormal⟩
                exact False.elim (hnormal hcNormal.symm)
          | control st₁ control =>
              simp [he] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped he hc
          | outOfFuel st₁ =>
              simp [he] at h
          | runtimeError st₁ msg =>
              simp [he] at h
      | str s =>
          simp [evalStmt] at h
          rcases h with ⟨_, hcNormal⟩
          exact False.elim (hnormal hcNormal.symm)
      | auto params =>
          simp [evalStmt] at h
          rcases h with ⟨_, hcNormal⟩
          exact False.elim (hnormal hcNormal.symm)
      | «if» cond thenBranch =>
          simp only [evalStmt] at h
          cases hcond : evalExpr fuel' st cond with
          | ok st₁ n =>
              by_cases hz : n.isZero
              · simp [hcond, hz] at h
                rcases h with ⟨_, hcNormal⟩
                exact False.elim (hnormal hcNormal.symm)
              · simp [hcond, hz] at h
                exact (evalStmt_control_stopped h hc).trans (evalExpr_ok_stopped hcond)
          | control st₁ control =>
              simp [hcond] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hcond hc
          | outOfFuel st₁ =>
              simp [hcond] at h
          | runtimeError st₁ msg =>
              simp [hcond] at h
      | «while» cond body =>
          simp only [evalStmt] at h
          cases hcond : evalExpr fuel' st cond with
          | ok st₁ n =>
              by_cases hz : n.isZero
              · simp [hcond, hz] at h
                rcases h with ⟨_, hcNormal⟩
                exact False.elim (hnormal hcNormal.symm)
              · simp [hcond, hz] at h
                cases hbody : evalStmt fuel' st₁ body with
                | ok st₂ control =>
                    cases control <;> simp [hbody] at h
                    · exact (evalStmt_control_stopped h hc).trans
                        ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond))
                    · rcases h with ⟨_, hcNormal⟩
                      exact False.elim (hnormal hcNormal.symm)
                    · rcases h with ⟨rfl, rfl⟩
                      exact (evalStmt_control_stopped hbody hc).trans (evalExpr_ok_stopped hcond)
                    · rcases h with ⟨rfl, rfl⟩
                      exact False.elim (hc rfl)
                | outOfFuel st₂ =>
                    simp [hbody] at h
                | runtimeError st₂ msg =>
                    simp [hbody] at h
          | control st₁ control =>
              simp [hcond] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hcond hc
          | outOfFuel st₁ =>
              simp [hcond] at h
          | runtimeError st₁ msg =>
              simp [hcond] at h
      | «for» init cond update body =>
          simp only [evalStmt] at h
          cases hinit : evalExpr fuel' st init with
          | ok st₁ value =>
              simp [hinit] at h
              exact (evalFor_control_stopped h hc).trans (evalExpr_ok_stopped hinit)
          | control st₁ control =>
              simp [hinit] at h
              rcases h with ⟨rfl, rfl⟩
              exact evalExpr_control_stopped hinit hc
          | outOfFuel st₁ =>
              simp [hinit] at h
          | runtimeError st₁ msg =>
              simp [hinit] at h
      | «break» =>
          simp [evalStmt] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | «return» value? =>
          cases value? with
          | none =>
              simp [evalStmt] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
          | some e =>
              simp only [evalStmt] at h
              cases he : evalExpr fuel' st e with
              | ok st₁ value =>
                  simp [he] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalExpr_ok_stopped he
              | control st₁ control =>
                  simp [he] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact evalExpr_control_stopped he hc
              | outOfFuel st₁ =>
                  simp [he] at h
              | runtimeError st₁ msg =>
                  simp [he] at h
      | «quit» =>
          simp [evalStmt] at h
          rcases h with ⟨rfl, rfl⟩
          exact False.elim (hc rfl)
      | «block» body =>
          simp [evalStmt] at h
          exact evalBody_control_stopped h hc

private theorem evalFor_normal_stopped {fuel st cond update body st'}
    (h : evalFor fuel st cond update body = .ok st' .normal) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalFor] at h
  | succ fuel' =>
      simp only [evalFor] at h
      cases hcond : evalExpr fuel' st cond with
      | ok st₁ n =>
          by_cases hz : n.isZero
          · simp [hcond, hz] at h
            cases h
            exact evalExpr_ok_stopped hcond
          · simp [hcond, hz] at h
            cases hbody : evalStmt fuel' st₁ body with
            | ok st₂ control =>
                cases control <;> simp [hbody] at h
                · cases hupdate : evalExpr fuel' st₂ update with
                  | ok st₃ value =>
                      simp [hupdate] at h
                      exact (evalFor_normal_stopped h).trans
                        ((evalExpr_ok_stopped hupdate).trans
                          ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond)))
                  | control st₃ control =>
                      simp [hupdate] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact (evalExpr_control_stopped hupdate (by intro hq; cases hq)).trans
                        ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond))
                  | outOfFuel st₃ =>
                      simp [hupdate] at h
                  | runtimeError st₃ msg =>
                      simp [hupdate] at h
                · cases h
                  exact (evalStmt_control_stopped hbody (by intro hq; cases hq)).trans
                    (evalExpr_ok_stopped hcond)
            | outOfFuel st₂ =>
                simp [hbody] at h
            | runtimeError st₂ msg =>
                simp [hbody] at h
      | control st₁ control =>
          simp [hcond] at h
          rcases h with ⟨rfl, rfl⟩
          exact evalExpr_control_stopped hcond (by intro hq; cases hq)
      | outOfFuel st₁ =>
          simp [hcond] at h
      | runtimeError st₁ msg =>
          simp [hcond] at h

private theorem evalFor_control_stopped {fuel st cond update body st' c}
    (h : evalFor fuel st cond update body = .ok st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  by_cases hnormal : c = .normal
  · subst c
    exact evalFor_normal_stopped h
  cases fuel with
  | zero =>
      simp [evalFor] at h
  | succ fuel' =>
      simp only [evalFor] at h
      cases hcond : evalExpr fuel' st cond with
      | ok st₁ n =>
          by_cases hz : n.isZero
          · simp [hcond, hz] at h
            rcases h with ⟨_, hcNormal⟩
            exact False.elim (hnormal hcNormal.symm)
          · simp [hcond, hz] at h
            cases hbody : evalStmt fuel' st₁ body with
            | ok st₂ control =>
                cases control <;> simp [hbody] at h
                · cases hupdate : evalExpr fuel' st₂ update with
                  | ok st₃ value =>
                      simp [hupdate] at h
                      exact (evalFor_control_stopped h hc).trans
                        ((evalExpr_ok_stopped hupdate).trans
                          ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond)))
                  | control st₃ control =>
                      simp [hupdate] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact (evalExpr_control_stopped hupdate hc).trans
                        ((evalStmt_normal_stopped hbody).trans (evalExpr_ok_stopped hcond))
                  | outOfFuel st₃ =>
                      simp [hupdate] at h
                  | runtimeError st₃ msg =>
                      simp [hupdate] at h
                · rcases h with ⟨_, hcNormal⟩
                  exact False.elim (hnormal hcNormal.symm)
                · rcases h with ⟨rfl, rfl⟩
                  exact (evalStmt_control_stopped hbody hc).trans (evalExpr_ok_stopped hcond)
                · rcases h with ⟨rfl, rfl⟩
                  exact False.elim (hc rfl)
            | outOfFuel st₂ =>
                simp [hbody] at h
            | runtimeError st₂ msg =>
                simp [hbody] at h
      | control st₁ control =>
          simp [hcond] at h
          rcases h with ⟨rfl, rfl⟩
          exact evalExpr_control_stopped hcond hc
      | outOfFuel st₁ =>
          simp [hcond] at h
      | runtimeError st₁ msg =>
          simp [hcond] at h

private theorem evalStmts_normal_stopped {fuel st stmts st'}
    (h : evalStmts fuel st stmts = .ok st' .normal) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalStmts] at h
  | succ fuel' =>
      cases stmts with
      | nil =>
          simp [evalStmts] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons stmt rest =>
          simp only [evalStmts] at h
          cases hstmt : evalStmt fuel' st stmt with
          | ok st₁ control =>
              cases control <;> simp [hstmt] at h
              · exact (evalStmts_normal_stopped h).trans (evalStmt_normal_stopped hstmt)
          | outOfFuel st₁ =>
              simp [hstmt] at h
          | runtimeError st₁ msg =>
              simp [hstmt] at h

private theorem evalStmts_control_stopped {fuel st stmts st' c}
    (h : evalStmts fuel st stmts = .ok st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalStmts] at h
  | succ fuel' =>
      cases stmts with
      | nil =>
          simp [evalStmts] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons stmt rest =>
          simp only [evalStmts] at h
          cases hstmt : evalStmt fuel' st stmt with
          | ok st₁ control =>
              cases control <;> simp [hstmt] at h
              · exact (evalStmts_control_stopped h hc).trans
                  (evalStmt_normal_stopped hstmt)
              · rcases h with ⟨rfl, rfl⟩
                exact evalStmt_control_stopped hstmt hc
              · rcases h with ⟨rfl, rfl⟩
                exact evalStmt_control_stopped hstmt hc
              · rcases h with ⟨rfl, rfl⟩
                exact False.elim (hc rfl)
          | outOfFuel st₁ =>
              simp [hstmt] at h
          | runtimeError st₁ msg =>
              simp [hstmt] at h

private theorem evalBody_normal_stopped {fuel st body st'}
    (h : evalBody fuel st body = .ok st' .normal) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalBody] at h
  | succ fuel' =>
      cases body with
      | nil =>
          simp [evalBody] at h
          cases h
          rfl
      | cons item rest =>
          cases item with
          | newline =>
              simp [evalBody] at h
              exact evalBody_normal_stopped h
          | stmts ss =>
              simp only [evalBody] at h
              cases hss : evalStmts fuel' st ss with
              | ok st₁ control =>
                  cases control <;> simp [hss] at h
                  · exact (evalBody_normal_stopped h).trans
                      (evalStmts_normal_stopped hss)
              | outOfFuel st₁ =>
                  simp [hss] at h
              | runtimeError st₁ msg =>
                  simp [hss] at h

private theorem evalBody_control_stopped {fuel st body st' c}
    (h : evalBody fuel st body = .ok st' c) (hc : c ≠ .quit) :
    st'.stopped = st.stopped := by
  cases fuel with
  | zero =>
      simp [evalBody] at h
  | succ fuel' =>
      cases body with
      | nil =>
          simp [evalBody] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | cons item rest =>
          cases item with
          | newline =>
              simp [evalBody] at h
              exact evalBody_control_stopped h hc
          | stmts ss =>
              simp only [evalBody] at h
              cases hss : evalStmts fuel' st ss with
              | ok st₁ control =>
                  cases control <;> simp [hss] at h
                  · exact (evalBody_control_stopped h hc).trans
                      (evalStmts_normal_stopped hss)
                  · rcases h with ⟨rfl, rfl⟩
                    exact evalStmts_control_stopped hss hc
                  · rcases h with ⟨rfl, rfl⟩
                    exact evalStmts_control_stopped hss hc
                  · rcases h with ⟨rfl, rfl⟩
                    exact False.elim (hc rfl)
              | outOfFuel st₁ =>
                  simp [hss] at h
              | runtimeError st₁ msg =>
                  simp [hss] at h

end

theorem evalTopItem_normal_stopped {fuel st item st'}
    (h : evalTopItem fuel st item = .ok st' .normal) :
    st'.stopped = st.stopped := by
  cases item with
  | funDef defn =>
      simp [evalTopItem] at h
      cases h
      exact stopped_setFunction st defn
  | stmts stmts =>
      exact evalStmts_normal_stopped h

end BigSmall

end Bc
