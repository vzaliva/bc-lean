/-
  A fuel-bounded big-step interpreter over the *residual* small-step terms.

  `Bc.evalExpr` and friends only evaluate source AST.  The small-step semantics,
  however, produces residual terms (`.value`, `.assignTarget`, `.activeCall`,
  `.loopBody`, …) that have no source counterpart.  To run the backward
  simulation by a clean structural induction over `*Runs` derivations, we need a
  big-step evaluator defined directly on residual terms.

  `evalExprTerm` etc. mirror the step functions of `Bc/SmallStep.lean` exactly:
  on source-shaped terms they agree with `Bc.evalExpr` (see `Residual` mirror
  lemmas), and each constructor's result is what a finished small-step run of
  that term yields.
-/

import Bc.BigStep
import Bc.SmallStep

namespace Bc

namespace BigSmall

open SmallStep

mutual

/-- Big-step evaluation of a residual expression term. -/
def evalExprTerm (fuel : Nat) (st : RuntimeState) (e : ExprTerm) : EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match e with
      | .value n => .ok st n
      | .num raw => .ok st (Num.ofInputString raw (currentConstBase st))
      | .var name => .ok st (lookupScalar st name)
      | .special v => .ok st (specialValue st v)
      | .arrayAccess name index =>
          match evalExprTerm fuel' st index with
          | .ok st idxNum =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  .ok st (getArrayElem st id idx)
              | .error msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .assign lhs op rhs =>
          match evalLValTerm fuel' st lhs with
          | .ok st target =>
              match evalExprTerm fuel' st rhs with
              | .ok st rhsValue =>
                  let old := readLValueTarget st target
                  match applyAssign? op old rhsValue st.scale with
                  | .ok n => .ok (writeLValueTarget st target n) n
                  | .error msg => .runtimeError st msg
              | .control st c => .control st c
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .assignTarget target op rhs =>
          match evalExprTerm fuel' st rhs with
          | .ok st rhsValue =>
              let old := readLValueTarget st target
              match applyAssign? op old rhsValue st.scale with
              | .ok n => .ok (writeLValueTarget st target n) n
              | .error msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .rel first rest =>
          match evalExprTerm fuel' st first with
          | .ok st n => evalRelChainTerm fuel' st n rest
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .bin op lhs rhs =>
          match evalExprTerm fuel' st lhs with
          | .ok st a =>
              match evalExprTerm fuel' st rhs with
              | .ok st b =>
                  match applyBin? op a b st.scale with
                  | .ok n => .ok st n
                  | .error msg => .runtimeError st msg
              | .control st c => .control st c
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .neg arg =>
          match evalExprTerm fuel' st arg with
          | .ok st v => .ok st (Num.neg v)
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .bump op target =>
          match evalLValTerm fuel' st target with
          | .ok st tgt =>
              let (st, old, newValue) :=
                bumpLValueTarget st tgt (op == .preIncr || op == .postIncr)
              match op with
              | .preIncr | .preDecr => .ok st newValue
              | .postIncr | .postDecr => .ok st old
              | .neg => .ok st newValue
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .badBump _ _ =>
          .runtimeError st "increment/decrement operand is not an lvalue"
      | .call name args =>
          match lookupFunction st name with
          | none => .runtimeError st s!"Function {name} not defined"
          | some defn =>
              match evalArgTerms fuel' st args with
              | .ok st argValues =>
                  let frame : Frame := { constBase := st.ibase }
                  let stWithFrame := { st with frames := frame :: st.frames }
                  match bindParams stWithFrame defn.params argValues with
                  | .error msg => .runtimeError stWithFrame msg
                  | .ok st =>
                      let st := bindAutoDecls st (collectAutos defn.body)
                      evalExprTerm fuel' st (.activeCall (BodyTerm.ofBody defn.body))
              | .control st c => .control st c
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
      | .activeCall body =>
          match evalBodyTerm fuel' st body with
          | .ok st .normal => .ok (popFrame st) Num.zero
          | .ok st (.return v?) => .ok (popFrame st) (returnValue v?)
          | .ok st .break => .runtimeError (popFrame st) "Break outside a loop"
          | .ok st .quit => .control (popFrame st) .quit
          | .outOfFuel st => .outOfFuel (popFrame st)
          | .runtimeError st msg => .runtimeError (popFrame st) msg
      | .builtin _ none => .runtimeError st "invalid builtin arity"
      | .builtin fn (some arg) =>
          match evalExprTerm fuel' st arg with
          | .ok st v =>
              match applyBuiltin? fn v st.scale with
              | .ok r => .ok st r
              | .error msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .paren body => evalExprTerm fuel' st body

/-- Big-step evaluation of a residual relational-chain tail. -/
def evalRelChainTerm (fuel : Nat) (st : RuntimeState) (left : Num)
    (rest : List (RelOp × ExprTerm)) : EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match rest with
      | [] => .ok st left
      | (op, rhs) :: tail =>
          match evalExprTerm fuel' st rhs with
          | .ok st right =>
              let out := boolNum (applyRel op left right)
              match tail with
              | [] => .ok st out
              | _ => evalRelChainTerm fuel' st out tail
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

/-- Big-step evaluation of a residual lvalue term. -/
def evalLValTerm (fuel : Nat) (st : RuntimeState) (lv : LValTerm) :
    EvalResult LValueTarget :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match lv with
      | .target t => .ok st t
      | .var name => .ok st (.scalar name)
      | .special v => .ok st (.special v)
      | .array name index =>
          match evalExprTerm fuel' st index with
          | .ok st idxNum =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  .ok st (.arrayElem id idx)
              | .error msg => .runtimeError st msg
          | .control st _ => .runtimeError st "control escaped from lvalue evaluation"
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

/-- Big-step evaluation of residual argument terms. -/
def evalArgTerms (fuel : Nat) (st : RuntimeState) (args : List ArgTerm) :
    EvalResult (List (Sum Num Name)) :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match args with
      | [] => .ok st []
      | .arrayRef name :: rest =>
          match evalArgTerms fuel' st rest with
          | .ok st vs => .ok st (.inr name :: vs)
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .expr e :: rest =>
          match evalExprTerm fuel' st e with
          | .ok st v =>
              match evalArgTerms fuel' st rest with
              | .ok st vs => .ok st (.inl v :: vs)
              | .control st c => .control st c
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .control st c => .control st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

/-- Big-step evaluation of a residual statement term. -/
def evalStmtTerm (fuel : Nat) (st : RuntimeState) (s : StmtTerm) : Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match s with
      | .done => .ok st .normal
      | .expr original e =>
          match evalExprTerm fuel' st e with
          | .ok st v =>
              if isTopAssignment original then .ok st .normal
              else .ok (printNumLine st v) .normal
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .eval e =>
          match evalExprTerm fuel' st e with
          | .ok st _ => .ok st .normal
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .str strv => .ok (appendOutput st (decodeBcString strv)) .normal
      | .auto _ => .ok st .normal
      | .ifThen cond thenBranch =>
          match evalExprTerm fuel' st cond with
          | .ok st n =>
              if n.isZero then .ok st .normal else evalStmtTerm fuel' st thenBranch
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .while condSource cond body =>
          match evalExprTerm fuel' st cond with
          | .ok st n =>
              if n.isZero then .ok st .normal
              else evalStmtTerm fuel' st
                (.loopBody body (.while condSource (ExprTerm.ofExpr condSource) body))
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .forCheck condSource cond updateSource body =>
          match evalExprTerm fuel' st cond with
          | .ok st n =>
              if n.isZero then .ok st .normal
              else evalStmtTerm fuel' st
                (.loopBody body (.forUpdate condSource updateSource
                  (ExprTerm.ofExpr updateSource) body))
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .forUpdate condSource updateSource update body =>
          match evalExprTerm fuel' st update with
          | .ok st _ =>
              evalStmtTerm fuel' st
                (.forCheck condSource (ExprTerm.ofExpr condSource) updateSource body)
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .loopBody body after =>
          match evalStmtTerm fuel' st body with
          | .ok st .normal => evalStmtTerm fuel' st after
          | .ok st .break => .ok st .normal
          | .ok st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .seq first second =>
          match evalStmtTerm fuel' st first with
          | .ok st .normal => evalStmtTerm fuel' st second
          | .ok st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .break => .ok st .break
      | .return none => .ok st (.return none)
      | .return (some e) =>
          match evalExprTerm fuel' st e with
          | .ok st v => .ok st (.return (some v))
          | .control st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .quit => .ok { st with stopped := true } .quit
      | .block body => evalBodyTerm fuel' st body

/-- Big-step evaluation of a residual body term. -/
def evalBodyTerm (fuel : Nat) (st : RuntimeState) (body : BodyTerm) : Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match body with
      | .stmts [] => .ok st .normal
      | .stmts (stmt :: rest) =>
          match evalStmtTerm fuel' st stmt with
          | .ok st .normal => evalBodyTerm fuel' st (.stmts rest)
          | .ok st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

end

end BigSmall

end Bc
