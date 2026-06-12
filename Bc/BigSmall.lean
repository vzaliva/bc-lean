/-
  Agreement statements for the big-step and small-step evaluators.

  Both evaluators are fuel-bounded, but their fuel counters measure different
  things: recursive big-step calls versus individual small-step transitions.
  The intended adequacy statement is therefore fuel-insensitive: if one
  evaluator reaches a final result with some amount of fuel, the other reaches
  the same final result with some amount of fuel.
-/

import Bc.BigStep
import Bc.BigSmall.Backward
import Bc.BigSmall.Forward
import Bc.BigSmall.Fuel
import Bc.BigSmall.Stopped
import Bc.SmallStep

namespace Bc

namespace BigSmall

open SmallStep

/-! ### Quit-predicate alignment (source AST ↔ residual terms) -/

theorem StmtTerm.listContainsQuit_append (xs ys : List StmtTerm) :
    StmtTerm.listContainsQuit (xs ++ ys) =
      (StmtTerm.listContainsQuit xs || StmtTerm.listContainsQuit ys) := by
  induction xs with
  | nil => simp [StmtTerm.listContainsQuit]
  | cons x xs ih => simp [StmtTerm.listContainsQuit, ih, Bool.or_assoc]

mutual

theorem containsQuit_ofStmt : (s : Stmt) →
    StmtTerm.containsQuit (StmtTerm.ofStmt s) = Stmt.containsQuit s
  | .expr _ => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .str _ => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .auto _ => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .if _ thenBranch => by
      simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit,
        containsQuit_ofStmt thenBranch]
  | .while _ body => by
      simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit,
        containsQuit_ofStmt body]
  | .for _ _ _ body => by
      simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit,
        containsQuit_ofStmt body]
  | .break => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .return none => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .return (some _) => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .quit => by simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit]
  | .block body => by
      simp [StmtTerm.containsQuit, StmtTerm.ofStmt, Stmt.containsQuit,
        BodyTerm.containsQuit, containsQuit_ofBodyItems body]
termination_by s => sizeOf s

theorem listContainsQuit_ofStmts : (ss : List Stmt) →
    StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = stmtsContainQuit ss
  | [] => by simp [StmtTerm.listContainsQuit, StmtTerm.ofStmts, stmtsContainQuit]
  | s :: rest => by
      simp [StmtTerm.listContainsQuit, StmtTerm.ofStmts, stmtsContainQuit,
        listContainsQuit_ofStmts rest, containsQuit_ofStmt s]
termination_by ss => sizeOf ss

theorem containsQuit_ofBodyItems : (items : List BodyItem) →
    BodyTerm.containsQuit (.stmts (BodyTerm.ofBodyItems items)) = bodyContainsQuit items
  | [] => by simp [BodyTerm.containsQuit, BodyTerm.ofBodyItems, bodyContainsQuit,
      StmtTerm.listContainsQuit]
  | BodyItem.stmts ss :: rest => by
      have hrest :
          StmtTerm.listContainsQuit (BodyTerm.ofBodyItems rest) = bodyContainsQuit rest := by
        simpa [BodyTerm.containsQuit] using containsQuit_ofBodyItems rest
      simp [BodyTerm.containsQuit, BodyTerm.ofBodyItems,
        listContainsQuit_ofStmts ss, stmtsContainQuit, bodyContainsQuit,
        bodyItemContainsQuit, StmtTerm.listContainsQuit_append, hrest, Bool.or_assoc]
  | BodyItem.newline :: rest => by
      simp [BodyTerm.containsQuit, BodyTerm.ofBodyItems, bodyContainsQuit,
        bodyItemContainsQuit, containsQuit_ofBodyItems rest]
termination_by items => sizeOf items

end

/-! ### Top-item flattening and quit alignment -/

private def topItemStmtsOf (ss : List StmtTerm) : List TopItemTerm :=
  ss.map (fun s => TopItemTerm.stmt s)

theorem listContainsQuit_ofStmtTerms (ss : List StmtTerm) :
    (topItemStmtsOf ss).any TopItemTerm.containsQuit = StmtTerm.listContainsQuit ss := by
  induction ss with
  | nil => simp [topItemStmtsOf, TopItemTerm.containsQuit, StmtTerm.listContainsQuit]
  | cons s rest ih =>
      have ih' : (List.map (fun s => TopItemTerm.stmt s) rest).any TopItemTerm.containsQuit =
          StmtTerm.listContainsQuit rest := by
        simpa [topItemStmtsOf] using ih
      simp [topItemStmtsOf, StmtTerm.listContainsQuit, List.any, List.map, ih',
        TopItemTerm.containsQuit]

theorem TopItemTerm.ofTopItem_stmts_map_noQuit (ss : List Stmt) (h : ¬ stmtsContainQuit ss) :
    TopItemTerm.ofTopItem (.stmts ss) = topItemStmtsOf (StmtTerm.ofStmts ss) := by
  simp [TopItemTerm.ofTopItem, topItemStmtsOf, h]

theorem TopItemTerm.ofTopItem_stmts_quit (ss : List Stmt) (h : stmtsContainQuit ss) :
    TopItemTerm.ofTopItem (.stmts ss) = [.stmt .quit] := by
  simp [TopItemTerm.ofTopItem, h]

theorem TopItemTerm.containsQuit_ofTopItem_stmts (ss : List Stmt) :
    (TopItemTerm.ofTopItem (.stmts ss)).any TopItemTerm.containsQuit =
      TopItem.containsQuit (.stmts ss) := by
  by_cases h : stmtsContainQuit ss
  · simp [TopItemTerm.ofTopItem, h, TopItem.containsQuit, TopItemTerm.containsQuit,
      StmtTerm.containsQuit]
  · rw [TopItemTerm.ofTopItem_stmts_map_noQuit ss h, listContainsQuit_ofStmtTerms,
      listContainsQuit_ofStmts, TopItem.containsQuit]

theorem TopItemTerm.containsQuit_ofTopItem_funDef (defn : FunDef) :
    (TopItemTerm.ofTopItem (.funDef defn)).any TopItemTerm.containsQuit =
      TopItem.containsQuit (.funDef defn) := by
  simp [TopItemTerm.ofTopItem, TopItem.containsQuit, TopItemTerm.containsQuit,
    bodyContainsQuit]

theorem TopItemTerm.containsQuit_ofTopItem (item : TopItem) :
    (TopItemTerm.ofTopItem item).any TopItemTerm.containsQuit = TopItem.containsQuit item := by
  cases item with
  | funDef defn => exact TopItemTerm.containsQuit_ofTopItem_funDef defn
  | stmts ss => exact TopItemTerm.containsQuit_ofTopItem_stmts ss

theorem topItemStmtsOf_append (xs ys : List StmtTerm) :
    topItemStmtsOf (xs ++ ys) = topItemStmtsOf xs ++ topItemStmtsOf ys := by
  simp [topItemStmtsOf, List.map_append]

private theorem stepStmt_seq_next_eq {st s second st' s'}
    (hstep : stepStmt st s = .next st' s') :
    stepStmt st (.seq s second) = .next st' (.seq s' second) := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_done_eq {st s second st'}
    (hstep : stepStmt st s = .done st') :
    stepStmt st (.seq s second) = .next st' second := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_control_eq {st s second st' c}
    (hstep : stepStmt st s = .control st' c) :
    stepStmt st (.seq s second) = .control st' c := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_error_eq {st s second st' msg}
    (hstep : stepStmt st s = .runtimeError st' msg) :
    stepStmt st (.seq s second) = .runtimeError st' msg := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_loop_next_eq {st body after st' body'}
    (hstep : stepStmt st body = .next st' body') :
    stepStmt st (.loopBody body after) = .next st' (.loopBody body' after) := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_done_eq {st body after st'}
    (hstep : stepStmt st body = .done st') :
    stepStmt st (.loopBody body after) = .next st' after := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_break_eq {st body after st'}
    (hstep : stepStmt st body = .control st' .break) :
    stepStmt st (.loopBody body after) = .done st' := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_control_eq {st body after st' c}
    (hnot : c ≠ .break) (hstep : stepStmt st body = .control st' c) :
    stepStmt st (.loopBody body after) = .control st' c := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_error_eq {st body after st' msg}
    (hstep : stepStmt st body = .runtimeError st' msg) :
    stepStmt st (.loopBody body after) = .runtimeError st' msg := by
  cases body <;> simp_all [stepStmt]

mutual

private theorem stepStmt_next_preserves_noQuit {st s st' s'}
    (hno : StmtTerm.containsQuit s = false)
    (hstep : stepStmt st s = .next st' s') :
    StmtTerm.containsQuit s' = false := by
  match s with
  | .done => simp [stepStmt] at hstep
  | .expr original expr =>
      cases expr
      case value value =>
        cases htop : isTopAssignment original <;> simp [stepStmt, htop] at hstep
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit]
  | .eval expr =>
      cases expr
      case value value =>
        simp [stepStmt] at hstep
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit]
  | .str _ => simp [stepStmt] at hstep
  | .auto _ => simp [stepStmt] at hstep
  | .ifThen cond branch =>
      simp [StmtTerm.containsQuit] at hno
      cases cond
      case value value =>
        cases hz : value.isZero <;> simp [stepStmt, hz] at hstep
        rcases hstep with ⟨_, rfl⟩
        exact hno
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
  | .while source cond body =>
      simp [StmtTerm.containsQuit] at hno
      cases cond
      case value value =>
        cases hz : value.isZero <;> simp [stepStmt, hz] at hstep
        rcases hstep with ⟨_, rfl⟩
        simp [StmtTerm.containsQuit, hno]
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
  | .forCheck source cond update body =>
      simp [StmtTerm.containsQuit] at hno
      cases cond
      case value value =>
        cases hz : value.isZero <;> simp [stepStmt, hz] at hstep
        rcases hstep with ⟨_, rfl⟩
        simp [StmtTerm.containsQuit, hno]
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
  | .forUpdate source updateSource update body =>
      simp [StmtTerm.containsQuit] at hno
      cases update
      case value value =>
        simp [stepStmt] at hstep
        rcases hstep with ⟨_, rfl⟩
        simp [StmtTerm.containsQuit, hno]
      all_goals
        simp [stepStmt] at hstep
        generalize hx : stepExpr st _ = out at hstep
        cases out <;> simp at hstep
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
        · rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hno]
  | .loopBody body after =>
      simp [StmtTerm.containsQuit] at hno
      rcases hno with ⟨hbodyNo, hafterNo⟩
      cases hbody : stepStmt st body with
      | next stx body' =>
          rw [stepStmt_loop_next_eq hbody] at hstep
          rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hafterNo,
            stepStmt_next_preserves_noQuit hbodyNo hbody]
      | done stx =>
          rw [stepStmt_loop_done_eq hbody] at hstep
          rcases hstep with ⟨_, rfl⟩
          exact hafterNo
      | control stx c =>
          by_cases hbreak : c = .break
          · subst c
            rw [stepStmt_loop_break_eq hbody] at hstep
            simp at hstep
          · rw [stepStmt_loop_control_eq hbreak hbody] at hstep
            simp at hstep
      | runtimeError stx msg =>
          rw [stepStmt_loop_error_eq hbody] at hstep
          simp at hstep
  | .seq first second =>
      simp [StmtTerm.containsQuit] at hno
      rcases hno with ⟨hfirstNo, hsecondNo⟩
      cases hfirst : stepStmt st first with
      | next stx first' =>
          rw [stepStmt_seq_next_eq hfirst] at hstep
          rcases hstep with ⟨_, rfl⟩
          simp [StmtTerm.containsQuit, hsecondNo,
            stepStmt_next_preserves_noQuit hfirstNo hfirst]
      | done stx =>
          rw [stepStmt_seq_done_eq hfirst] at hstep
          rcases hstep with ⟨_, rfl⟩
          exact hsecondNo
      | control stx c =>
          rw [stepStmt_seq_control_eq hfirst] at hstep
          simp at hstep
      | runtimeError stx msg =>
          rw [stepStmt_seq_error_eq hfirst] at hstep
          simp at hstep
  | .break => simp [stepStmt] at hstep
  | .return value? =>
      cases value? with
      | none => simp [stepStmt] at hstep
      | some expr =>
          cases expr
          case value value =>
            simp [stepStmt] at hstep
          all_goals
            simp [stepStmt] at hstep
            generalize hx : stepExpr st _ = out at hstep
            cases out <;> simp at hstep
            · rcases hstep with ⟨_, rfl⟩
              simp [StmtTerm.containsQuit]
            · rcases hstep with ⟨_, rfl⟩
              simp [StmtTerm.containsQuit]
  | .quit => simp [stepStmt] at hstep
  | .block body =>
      have hbodyNo : BodyTerm.containsQuit body = false := by
        simpa [StmtTerm.containsQuit] using hno
      cases hbody : stepBody st body <;> simp [stepStmt, hbody] at hstep ⊢
      rcases hstep with ⟨_, rfl⟩
      simpa [StmtTerm.containsQuit] using stepBody_next_preserves_noQuit hbodyNo hbody
termination_by sizeOf s

private theorem stepBody_next_preserves_noQuit {st body st' body'}
    (hno : BodyTerm.containsQuit body = false)
    (hstep : stepBody st body = .next st' body') :
    BodyTerm.containsQuit body' = false := by
  match body with
  | .stmts [] => simp [stepBody] at hstep
  | .stmts (stmt :: rest) =>
      simp [BodyTerm.containsQuit, StmtTerm.listContainsQuit] at hno
      rcases hno with ⟨hstmtNo, hrestNo⟩
      cases hstmt : stepStmt st stmt <;> simp [stepBody, hstmt] at hstep
      · rcases hstep with ⟨_, rfl⟩
        simp [BodyTerm.containsQuit, StmtTerm.listContainsQuit, hrestNo,
          stepStmt_next_preserves_noQuit hstmtNo hstmt]
      · rcases hstep with ⟨_, rfl⟩
        simp [BodyTerm.containsQuit, hrestNo]
termination_by sizeOf body

end

private theorem stepBody_next_preserves_noQuit_stmts {st terms st' terms'}
    (hno : StmtTerm.listContainsQuit terms = false)
    (hstep : stepBody st (.stmts terms) = .next st' (.stmts terms')) :
    StmtTerm.listContainsQuit terms' = false := by
  have h := stepBody_next_preserves_noQuit (body := BodyTerm.stmts terms)
    (body' := BodyTerm.stmts terms') (by simpa [BodyTerm.containsQuit] using hno) hstep
  simpa [BodyTerm.containsQuit] using h

private theorem stepConfig_body_next {st terms rest st' terms'}
    (hno : StmtTerm.listContainsQuit terms = false)
    (hstep : stepBody st (.stmts terms) = .next st' (.stmts terms')) :
    step ⟨st, topItemStmtsOf terms ++ rest⟩ =
      .next ⟨st', topItemStmtsOf terms' ++ rest⟩ := by
  cases terms with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt terms =>
      simp [StmtTerm.listContainsQuit] at hno
      rcases hno with ⟨hstmtNo, hrestNo⟩
      simp [topItemStmtsOf, step, TopItemTerm.containsQuit, hstmtNo, stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      · rcases hstep with ⟨rfl, rfl⟩
        rfl
      · rcases hstep with ⟨rfl, rfl⟩
        rfl

private theorem stepConfig_body_control {st terms rest st' c}
    (hno : StmtTerm.listContainsQuit terms = false)
    (hstep : stepBody st (.stmts terms) = .control st' c) :
    step ⟨st, topItemStmtsOf terms ++ rest⟩ = .control st' c := by
  cases terms with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt terms =>
      simp [StmtTerm.listContainsQuit] at hno
      rcases hno with ⟨hstmtNo, _⟩
      simp [topItemStmtsOf, step, TopItemTerm.containsQuit, hstmtNo, stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      rcases hstep with ⟨rfl, rfl⟩
      constructor <;> rfl

private theorem stepConfig_body_error {st terms rest st' msg}
    (hno : StmtTerm.listContainsQuit terms = false)
    (hstep : stepBody st (.stmts terms) = .runtimeError st' msg) :
    step ⟨st, topItemStmtsOf terms ++ rest⟩ = .runtimeError st' msg := by
  cases terms with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt terms =>
      simp [StmtTerm.listContainsQuit] at hno
      rcases hno with ⟨hstmtNo, _⟩
      simp [topItemStmtsOf, step, TopItemTerm.containsQuit, hstmtNo, stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      rcases hstep with ⟨rfl, rfl⟩
      constructor <;> rfl

theorem BodyRuns.lift_done_to_config {rest : ProgramTerm}
    {st terms st' o}
    (hno : StmtTerm.listContainsQuit terms = false)
    (h : BodyRuns st (.stmts terms) (.done st'))
    (hcont : ConfigRuns ⟨st', rest⟩ o) :
    ConfigRuns ⟨st, topItemStmtsOf terms ++ rest⟩ o := by
  generalize hbody : BodyTerm.stmts terms = body at h
  generalize hout : BodyOutcome.done st' = out at h
  induction h generalizing terms with
  | stop hstep _ =>
      cases hbody
      cases hout
      cases terms with
      | nil =>
          simp [stepBody] at hstep
          cases hstep
          simpa [topItemStmtsOf] using hcont
      | cons stmt terms =>
          simp [stepBody] at hstep
          generalize hstmt : stepStmt _ stmt = outStmt at hstep
          cases outStmt <;> simp at hstep
  | next hstep _ ih =>
      rename_i oldBody nextState nextBody nextOut
      cases hbody
      cases nextState with
      | stmts terms' =>
          have hno' := stepBody_next_preserves_noQuit_stmts hno hstep
          exact ConfigRuns.next
            (stepConfig_body_next hno hstep)
            (ih hno' rfl hout)

theorem BodyRuns.lift_control_to_config {rest : ProgramTerm}
    {st terms st' c}
    (hno : StmtTerm.listContainsQuit terms = false)
    (h : BodyRuns st (.stmts terms) (.control st' c)) :
    ConfigRuns ⟨st, topItemStmtsOf terms ++ rest⟩ (.control st' c) := by
  generalize hbody : BodyTerm.stmts terms = body at h
  generalize hout : BodyOutcome.control st' c = out at h
  induction h generalizing terms with
  | stop hstep _ =>
      cases hbody
      cases hout
      exact ConfigRuns.stop (stepConfig_body_control hno hstep) (by simp [StepResultFinal])
  | next hstep _ ih =>
      rename_i oldBody nextState nextBody nextOut
      cases hbody
      cases nextState with
      | stmts terms' =>
          have hno' := stepBody_next_preserves_noQuit_stmts hno hstep
          exact ConfigRuns.next
            (stepConfig_body_next hno hstep)
            (ih hno' rfl hout)

theorem BodyRuns.lift_error_to_config {rest : ProgramTerm}
    {st terms st' msg}
    (hno : StmtTerm.listContainsQuit terms = false)
    (h : BodyRuns st (.stmts terms) (.runtimeError st' msg)) :
    ConfigRuns ⟨st, topItemStmtsOf terms ++ rest⟩ (.runtimeError st' msg) := by
  generalize hbody : BodyTerm.stmts terms = body at h
  generalize hout : BodyOutcome.runtimeError st' msg = out at h
  induction h generalizing terms with
  | stop hstep _ =>
      cases hbody
      cases hout
      exact ConfigRuns.stop (stepConfig_body_error hno hstep) (by simp [StepResultFinal])
  | next hstep _ ih =>
      rename_i oldBody nextState nextBody nextOut
      cases hbody
      cases nextState with
      | stmts terms' =>
          have hno' := stepBody_next_preserves_noQuit_stmts hno hstep
          exact ConfigRuns.next
            (stepConfig_body_next hno hstep)
            (ih hno' rfl hout)

private def resultToRunResult : Result Control → RunResult
  | .ok st _ => .success st
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

private theorem step_topItem_containsQuit {st item rest}
    (hquit : TopItem.containsQuit item = true) :
    step ⟨st, TopItemTerm.ofTopItem item ++ rest⟩ = .done { st with stopped := true } := by
  cases item with
  | funDef defn =>
      have hbody : bodyContainsQuit defn.body = true := by
        simpa [TopItem.containsQuit] using hquit
      simp [TopItemTerm.ofTopItem, step, TopItemTerm.containsQuit, hbody]
  | stmts ss =>
      simp [TopItemTerm.ofTopItem, TopItem.containsQuit] at hquit
      simp [TopItemTerm.ofTopItem, hquit, step, TopItemTerm.containsQuit,
        StmtTerm.containsQuit]

private theorem evalProgramItems_to_ConfigRuns {fuel st program r}
    (hst : st.stopped = false)
    (h : evalProgramItems fuel st program = r) (hnf : ResultNotFuel r) :
    ∃ o, ConfigRuns ⟨st, ProgramTerm.ofProgram program⟩ o ∧
      stepResultToRunResult o = resultToRunResult r := by
  induction fuel generalizing st program r with
  | zero =>
      simp [evalProgramItems] at h
      subst r
      cases hnf
  | succ fuel' ih =>
      cases program with
      | nil =>
          simp [evalProgramItems] at h
          cases h
          exact ⟨.done st, ConfigRuns.stop (by simp [ProgramTerm.ofProgram, step])
            (by simp [StepResultFinal]), by simp [stepResultToRunResult, resultToRunResult]⟩
      | cons item rest =>
          simp only [evalProgramItems] at h
          cases hquit : TopItem.containsQuit item with
          | true =>
              simp [hquit] at h
              cases h
              exact ⟨.done { st with stopped := true },
                ConfigRuns.stop
                  (by simpa [ProgramTerm.ofProgram] using
                    (step_topItem_containsQuit (st := st) (item := item)
                      (rest := ProgramTerm.ofProgram rest) hquit))
                  (by simp [StepResultFinal]),
                by simp [stepResultToRunResult, resultToRunResult]⟩
          | false =>
              simp [hquit] at h
              cases htop : evalTopItem fuel' st item with
              | ok st₁ control =>
                  cases control with
                  | normal =>
                      have hst₁ : st₁.stopped = false := by
                        exact (evalTopItem_normal_stopped htop).trans hst
                      simp [htop, hst₁] at h
                      rcases ih hst₁ h hnf with ⟨o, hcont, hout⟩
                      cases item with
                      | funDef defn =>
                          simp [evalTopItem] at htop
                          cases htop
                          exact ⟨o,
                            ConfigRuns.next
                              (by
                                have hbody : bodyContainsQuit defn.body = false := by
                                  simpa [TopItem.containsQuit] using hquit
                                simp [ProgramTerm.ofProgram, TopItemTerm.ofTopItem, step, next,
                                  TopItemTerm.containsQuit, hbody])
                              hcont,
                            hout⟩
                      | stmts ss =>
                          have hbody : BodyRuns st (.stmts (StmtTerm.ofStmts ss)) (.done st₁) :=
                            evalStmts_to_BodyRuns htop (by simp [ResultNotFuel])
                          have hnoEq : stmtsContainQuit ss = false := by
                            simpa [TopItem.containsQuit] using hquit
                          have hno : StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = false := by
                            simpa [listContainsQuit_ofStmts, hnoEq]
                          have hnoProp : ¬ stmtsContainQuit ss := by
                            intro hs
                            simp [hs] at hnoEq
                          have hmap := TopItemTerm.ofTopItem_stmts_map_noQuit ss hnoProp
                          exact ⟨o,
                            by
                              simpa [ProgramTerm.ofProgram, hmap] using
                                (BodyRuns.lift_done_to_config
                                  (rest := ProgramTerm.ofProgram rest) hno hbody hcont),
                            hout⟩
                  | «break» =>
                      simp [htop] at h
                      cases h
                      cases item with
                      | funDef defn =>
                          simp [evalTopItem] at htop
                      | stmts ss =>
                          have hbody : BodyRuns st (.stmts (StmtTerm.ofStmts ss))
                              (.control st₁ .break) :=
                            evalStmts_to_BodyRuns htop (by simp [ResultNotFuel])
                          have hnoEq : stmtsContainQuit ss = false := by
                            simpa [TopItem.containsQuit] using hquit
                          have hno : StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = false := by
                            simpa [listContainsQuit_ofStmts, hnoEq]
                          have hnoProp : ¬ stmtsContainQuit ss := by
                            intro hs
                            simp [hs] at hnoEq
                          have hmap := TopItemTerm.ofTopItem_stmts_map_noQuit ss hnoProp
                          exact ⟨.control st₁ .break,
                            by
                              simpa [ProgramTerm.ofProgram, hmap] using
                                (BodyRuns.lift_control_to_config
                                  (rest := ProgramTerm.ofProgram rest) hno hbody),
                            by simp [stepResultToRunResult, resultToRunResult]⟩
                  | «return» value? =>
                      simp [htop] at h
                      cases h
                      cases item with
                      | funDef defn =>
                          simp [evalTopItem] at htop
                      | stmts ss =>
                          have hbody : BodyRuns st (.stmts (StmtTerm.ofStmts ss))
                              (.control st₁ (.return value?)) :=
                            evalStmts_to_BodyRuns htop (by simp [ResultNotFuel])
                          have hnoEq : stmtsContainQuit ss = false := by
                            simpa [TopItem.containsQuit] using hquit
                          have hno : StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = false := by
                            simpa [listContainsQuit_ofStmts, hnoEq]
                          have hnoProp : ¬ stmtsContainQuit ss := by
                            intro hs
                            simp [hs] at hnoEq
                          have hmap := TopItemTerm.ofTopItem_stmts_map_noQuit ss hnoProp
                          exact ⟨.control st₁ (.return value?),
                            by
                              simpa [ProgramTerm.ofProgram, hmap] using
                                (BodyRuns.lift_control_to_config
                                  (rest := ProgramTerm.ofProgram rest) hno hbody),
                            by cases value? <;> simp [stepResultToRunResult, resultToRunResult]⟩
                  | «quit» =>
                      simp [htop] at h
                      cases h
                      cases item with
                      | funDef defn =>
                          simp [evalTopItem] at htop
                      | stmts ss =>
                          have hbody : BodyRuns st (.stmts (StmtTerm.ofStmts ss))
                              (.control st₁ .quit) :=
                            evalStmts_to_BodyRuns htop (by simp [ResultNotFuel])
                          have hnoEq : stmtsContainQuit ss = false := by
                            simpa [TopItem.containsQuit] using hquit
                          have hno : StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = false := by
                            simpa [listContainsQuit_ofStmts, hnoEq]
                          have hnoProp : ¬ stmtsContainQuit ss := by
                            intro hs
                            simp [hs] at hnoEq
                          have hmap := TopItemTerm.ofTopItem_stmts_map_noQuit ss hnoProp
                          exact ⟨.control st₁ .quit,
                            by
                              simpa [ProgramTerm.ofProgram, hmap] using
                                (BodyRuns.lift_control_to_config
                                  (rest := ProgramTerm.ofProgram rest) hno hbody),
                            by simp [stepResultToRunResult, resultToRunResult]⟩
              | outOfFuel st₁ =>
                  simp [htop] at h
                  subst r
                  cases hnf
              | runtimeError st₁ msg =>
                  simp [htop] at h
                  cases h
                  cases item with
                  | funDef defn =>
                      simp [evalTopItem] at htop
                  | stmts ss =>
                      have hbody : BodyRuns st (.stmts (StmtTerm.ofStmts ss))
                          (.runtimeError st₁ msg) :=
                        evalStmts_to_BodyRuns htop (by simp [ResultNotFuel])
                      have hnoEq : stmtsContainQuit ss = false := by
                        simpa [TopItem.containsQuit] using hquit
                      have hno : StmtTerm.listContainsQuit (StmtTerm.ofStmts ss) = false := by
                        simpa [listContainsQuit_ofStmts, hnoEq]
                      have hnoProp : ¬ stmtsContainQuit ss := by
                        intro hs
                        simp [hs] at hnoEq
                      have hmap := TopItemTerm.ofTopItem_stmts_map_noQuit ss hnoProp
                      exact ⟨.runtimeError st₁ msg,
                        by
                          simpa [ProgramTerm.ofProgram, hmap] using
                            (BodyRuns.lift_error_to_config
                              (rest := ProgramTerm.ofProgram rest) hno hbody),
                        by simp [stepResultToRunResult, resultToRunResult]⟩

/-! ### Final-result agreement -/

/-- Semantic final results exclude `outOfFuel`, which is an interpreter bound artifact. -/
inductive FinalRunResult : RunResult → Prop where
  | success (st : RuntimeState) :
      FinalRunResult (.success st)
  | runtimeError (st : RuntimeState) (message : String) :
      FinalRunResult (.runtimeError st message)

theorem RunResultFinal_of_FinalRunResult {r : RunResult} (h : FinalRunResult r) :
    RunResultFinal r := by cases h <;> simp [RunResultFinal]

theorem FinalRunResult_of_RunResultFinal {r : RunResult} (h : RunResultFinal r) :
    FinalRunResult r := by
  cases r with
  | success st => exact .success st
  | outOfFuel st => simp [RunResultFinal] at h
  | runtimeError st msg => exact .runtimeError st msg

/-- Big-step evaluation reaches a final result from the given initial state. -/
def BigTerminatesWith (st : RuntimeState) (program : Program) (result : RunResult) : Prop :=
  FinalRunResult result ∧ ∃ fuel, Bc.runProgramWithState fuel st program = result

/-- Small-step evaluation reaches a final result from the given initial state. -/
def SmallTerminatesWith (st : RuntimeState) (program : Program) (result : RunResult) : Prop :=
  FinalRunResult result ∧ ∃ fuel, SmallStep.runProgramWithState fuel st program = result

/-- Big-step final results are reproducible by the small-step evaluator. -/
private theorem big_to_small_runProgramWithState {st : RuntimeState} {program : Program}
    {result : RunResult} (hst : st.stopped = false) :
    BigTerminatesWith st program result → SmallTerminatesWith st program result := by
  intro hbig
  rcases hbig with ⟨hfinal, fuel, hrun⟩
  constructor
  · exact hfinal
  · unfold Bc.runProgramWithState at hrun
    cases heval : evalProgramItems fuel st program with
    | ok st' control =>
        simp [heval] at hrun
        cases hrun
        rcases evalProgramItems_to_ConfigRuns hst heval (by simp [ResultNotFuel]) with
          ⟨o, hcfg, hout⟩
        rcases ConfigRuns.to_fuel hcfg with ⟨smallFuel, hsmall⟩
        exact ⟨smallFuel, by
          simpa [SmallStep.runProgramWithState, SmallStep.initialConfig, hsmall, hout,
            resultToRunResult]⟩
    | outOfFuel st' =>
        simp [heval] at hrun
        cases hrun
        cases hfinal
    | runtimeError st' msg =>
        simp [heval] at hrun
        cases hrun
        rcases evalProgramItems_to_ConfigRuns hst heval (by simp [ResultNotFuel]) with
          ⟨o, hcfg, hout⟩
        rcases ConfigRuns.to_fuel hcfg with ⟨smallFuel, hsmall⟩
        exact ⟨smallFuel, by
          simpa [SmallStep.runProgramWithState, SmallStep.initialConfig, hsmall, hout,
            resultToRunResult]⟩

/-- Small-step final results are reproducible by the big-step evaluator.

    Rather than rebuild the simulation in reverse, we use that the small-step
    evaluator has a unique final result (`runProgramWithState_final_unique`): a
    terminating small run yields a finite `ConfigRuns`, which (by
    `termination_transfer`) forces big-step termination with *some* final result
    `r'`; the forward direction reproduces `r'` on the small side, and small-step
    determinism identifies `r'` with the given `result`. -/
private theorem small_to_big_runProgramWithState {st : RuntimeState} {program : Program}
    {result : RunResult} (hst : st.stopped = false) :
    SmallTerminatesWith st program result → BigTerminatesWith st program result := by
  intro hsmall
  rcases hsmall with ⟨hfinal, fs, hfs⟩
  have hnotfuel : ∀ st₀, result ≠ .outOfFuel st₀ := by
    intro st₀; cases hfinal <;> simp
  -- The terminating small run yields a finite `ConfigRuns` derivation.
  rcases ConfigRuns.of_fuel (c := SmallStep.initialConfig st program) (r := result)
      (by simpa [SmallStep.runProgramWithState] using hfs) hnotfuel with ⟨o, hcfg, _⟩
  -- Termination transfer: big-step also terminates (with some final result).
  rcases termination_transfer (program := program) hst
      (by simpa [SmallStep.initialConfig] using hcfg) with ⟨fb, hnf⟩
  have hr'fin : RunResultFinal (Bc.runProgramWithState fb st program) :=
    runProgramWithState_final_of_notFuel hnf
  have hbig' : BigTerminatesWith st program (Bc.runProgramWithState fb st program) :=
    ⟨FinalRunResult_of_RunResultFinal hr'fin, fb, rfl⟩
  -- Forward direction reproduces that result on the small side.
  rcases big_to_small_runProgramWithState hst hbig' with ⟨_, fs', hfs'⟩
  -- Small-step determinism pins the two final results together.
  have heq : result = Bc.runProgramWithState fb st program :=
    runProgramWithState_final_unique hfs (RunResultFinal_of_FinalRunResult hfinal)
      hfs' hr'fin
  exact ⟨hfinal, fb, heq.symm⟩

/-- Big-step and small-step evaluation agree on final results from a valid entry state. -/
theorem runProgramWithState_iff (st : RuntimeState) (program : Program) (result : RunResult)
    (hst : st.stopped = false) :
    BigTerminatesWith st program result ↔ SmallTerminatesWith st program result := by
  constructor
  · exact big_to_small_runProgramWithState hst
  · exact small_to_big_runProgramWithState hst

/-- Initial-state specialization of `BigTerminatesWith`. -/
def BigTerminates (program : Program) (result : RunResult) : Prop :=
  FinalRunResult result ∧ ∃ fuel, Bc.runProgram fuel program = result

/-- Initial-state specialization of `SmallTerminatesWith`. -/
def SmallTerminates (program : Program) (result : RunResult) : Prop :=
  FinalRunResult result ∧ ∃ fuel, SmallStep.runProgram fuel program = result

/-- Big-step and small-step evaluation agree on all final initial-state results. -/
theorem runProgram_iff (program : Program) (result : RunResult) :
    BigTerminates program result ↔ SmallTerminates program result := by
  simpa [BigTerminates, SmallTerminates, BigTerminatesWith, SmallTerminatesWith,
    Bc.runProgram, SmallStep.runProgram] using
    (runProgramWithState_iff initialState program result (by simp [initialState]))

end BigSmall

end Bc
