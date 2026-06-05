/-
  Progress theorem for the structural small-step semantics.

  Software Foundations states progress for a small-step relation as: every term
  is either a value or can step to another term. For bc's source-shaped
  residual configurations, terminal outcomes are normal completion, propagated
  control, and runtime errors. Fuel belongs to the interpreter runner, not to
  the one-step transition relation.
-/

import Bc.SmallStep

namespace Bc

namespace SmallStep

/-- The relational view of one executable small-step transition. -/
inductive Transition : Config → Config → Prop where
  | ofNext {config config' : Config} :
      step config = .next config' → Transition config config'

/-- Terminal one-step outcomes for the fuel-free structural semantics. -/
inductive Terminal (config : Config) : Prop where
  | done (st : RuntimeState) :
      step config = .done st → Terminal config
  | control (st : RuntimeState) (control : Control) :
      step config = .control st control → Terminal config
  | runtimeError (st : RuntimeState) (message : String) :
      step config = .runtimeError st message → Terminal config

/-- A generic normal form: a state that cannot take a transition. -/
def NormalForm {α : Type} (R : α → α → Prop) (x : α) : Prop :=
  ¬ ∃ y, R x y

/-- A stuck configuration is a non-terminal normal form. -/
def Stuck (config : Config) : Prop :=
  NormalForm Transition config ∧ ¬ Terminal config

/-- Progress: every configuration either has a terminal result or can take a step. -/
theorem progress (config : Config) :
    Terminal config ∨ ∃ config', Transition config config' := by
  cases h : step config with
  | next config' =>
      exact .inr ⟨config', .ofNext h⟩
  | done st =>
      exact .inl (.done st h)
  | control st control =>
      exact .inl (.control st control h)
  | runtimeError st message =>
      exact .inl (.runtimeError st message h)

/-- Terminal configurations cannot take a transition. -/
theorem terminal_is_normal_form {config : Config}
    (h : Terminal config) : NormalForm Transition config := by
  intro hstep
  rcases hstep with ⟨config', htransition⟩
  cases htransition with
  | ofNext hnext =>
      cases h with
      | done _ hterminal =>
          rw [hterminal] at hnext
          cases hnext
      | control _ _ hterminal =>
          rw [hterminal] at hnext
          cases hnext
      | runtimeError _ _ hterminal =>
          rw [hterminal] at hnext
          cases hnext

/-- A normal form for the transition relation must be terminal. -/
theorem normal_form_is_terminal {config : Config}
    (h : NormalForm Transition config) : Terminal config := by
  match progress config with
  | .inl hterminal => exact hterminal
  | .inr hstep => exact False.elim (h hstep)

/-- Normal forms and terminal configurations coincide for this step relation. -/
theorem normal_form_iff_terminal (config : Config) :
    NormalForm Transition config ↔ Terminal config := by
  constructor
  · exact normal_form_is_terminal
  · exact terminal_is_normal_form

/-- Corollary of progress: there are no stuck configurations. -/
theorem not_stuck (config : Config) : ¬ Stuck config := by
  intro h
  exact h.2 (normal_form_is_terminal h.1)

end SmallStep

end Bc
