/-
  Progress theorem for the declarative structural small-step semantics.

  Software Foundations states progress for a small-step relation as: every term
  is either a value or can step to another term. For bc's source-shaped
  residual configurations, terminal outcomes are normal completion, propagated
  control, and runtime errors. The proof rests on `stepProg_complete`, which
  shows that the declarative relation covers every executable one-step result.
  Fuel belongs to the interpreter runner, not to the one-step transition
  relation.
-/

import Bc.SmallStepProperties

namespace Bc

namespace SmallStep

/-- A non-terminal declarative program transition. -/
def Transition (config config' : Config) : Prop :=
  StepProg config (.next config')

/-- Terminal declarative one-step outcomes for the fuel-free structural semantics. -/
inductive Terminal (config : Config) : Prop where
  | done (st : RuntimeState) :
      StepProg config (.done st) → Terminal config
  | control (st : RuntimeState) (control : Control) :
      StepProg config (.control st control) → Terminal config
  | runtimeError (st : RuntimeState) (message : String) :
      StepProg config (.runtimeError st message) → Terminal config

/-- A generic normal form: a state that cannot take a transition. -/
def NormalForm {α : Type} (R : α → α → Prop) (x : α) : Prop :=
  ¬ ∃ y, R x y

/-- A stuck configuration is a non-terminal normal form. -/
def Stuck (config : Config) : Prop :=
  NormalForm Transition config ∧ ¬ Terminal config

/-- Progress: every configuration either has a terminal result or can take a step. -/
theorem progress (config : Config) :
    Terminal config ∨ ∃ config', Transition config config' := by
  have hstep : StepProg config (step config) := stepProg_complete (c := config)
  cases h : step config with
  | next config' =>
      rw [h] at hstep
      exact .inr ⟨config', hstep⟩
  | done st =>
      rw [h] at hstep
      exact .inl (.done st hstep)
  | control st control =>
      rw [h] at hstep
      exact .inl (.control st control hstep)
  | runtimeError st message =>
      rw [h] at hstep
      exact .inl (.runtimeError st message hstep)

/-- Terminal configurations cannot take a transition. -/
theorem terminal_is_normal_form {config : Config}
    (h : Terminal config) : NormalForm Transition config := by
  intro hstep
  cases hstep with
  | intro config' htransition =>
      cases h with
      | done _ hterminal =>
          cases stepProg_deterministic hterminal htransition
      | control _ _ hterminal =>
          cases stepProg_deterministic hterminal htransition
      | runtimeError _ _ hterminal =>
          cases stepProg_deterministic hterminal htransition

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
