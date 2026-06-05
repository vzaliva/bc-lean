/-
  Shared types and helpers for `Bc/SmallStep.lean` and `Bc/SmallStepRel.lean`.

  Executable-only pieces (program initialisation, lift combinators) live in
  `SmallStep.lean` and `SmallStepRel.lean` respectively; adequacy proofs and
  their helper predicates are in `SmallStepProperties.lean`.
-/

import Bc.Runtime

namespace Bc

namespace SmallStep

mutual

inductive ExprTerm where
  | value (value : Num)
  | num (raw : String)
  | var (name : Name)
  | special (var : SpecialVar)
  | arrayAccess (name : Name) (index : ExprTerm)
  | assign (lhs : LValTerm) (op : AssignOp) (rhs : ExprTerm)
  | assignTarget (target : LValueTarget) (op : AssignOp) (rhs : ExprTerm)
  | rel (first : ExprTerm) (rest : List (RelOp × ExprTerm))
  | bin (op : BinOp) (lhs rhs : ExprTerm)
  | neg (arg : ExprTerm)
  | bump (op : UnOp) (target : LValTerm)
  | badBump (op : UnOp) (arg : ExprTerm)
  | call (name : Name) (args : List ArgTerm)
  | activeCall (body : BodyTerm)
  | builtin (fn : Builtin) (arg : Option ExprTerm)
  | paren (body : ExprTerm)
  deriving Repr

inductive LValTerm where
  | target (target : LValueTarget)
  | var (name : Name)
  | special (var : SpecialVar)
  | array (name : Name) (index : ExprTerm)
  deriving Repr

inductive ArgTerm where
  | expr (expr : ExprTerm)
  | arrayRef (name : Name)
  deriving Repr

inductive StmtTerm where
  | done
  | expr (original : Expr) (expr : ExprTerm)
  | eval (expr : ExprTerm)
  | str (value : String)
  | auto (params : List ParamDecl)
  | ifThen (cond : ExprTerm) (thenBranch : StmtTerm)
  | while (condSource : Expr) (cond : ExprTerm) (body : StmtTerm)
  | forCheck (condSource : Expr) (cond : ExprTerm) (updateSource : Expr) (body : StmtTerm)
  | forUpdate (condSource updateSource : Expr) (update : ExprTerm) (body : StmtTerm)
  | loopBody (body : StmtTerm) (after : StmtTerm)
  | seq (first second : StmtTerm)
  | break
  | return (value : Option ExprTerm)
  | quit
  | block (body : BodyTerm)
  deriving Repr

inductive BodyTerm where
  | stmts (stmts : List StmtTerm)
  deriving Repr

end

inductive TopItemTerm where
  | funDef (defn : FunDef)
  | stmt (stmt : StmtTerm)
  deriving Repr

abbrev ProgramTerm := List TopItemTerm

structure Config where
  state : RuntimeState
  program : ProgramTerm
  deriving Repr

inductive StepResult where
  | next (config : Config)
  | done (state : RuntimeState)
  | control (state : RuntimeState) (control : Control)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive ExprOutcome where
  | next (state : RuntimeState) (expr : ExprTerm)
  | value (state : RuntimeState) (value : Num)
  | control (state : RuntimeState) (control : Control)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive LValOutcome where
  | next (state : RuntimeState) (lval : LValTerm)
  | target (state : RuntimeState) (target : LValueTarget)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive ArgListOutcome where
  | next (state : RuntimeState) (args : List ArgTerm)
  | values (state : RuntimeState) (values : List (Sum Num Name))
  | control (state : RuntimeState) (control : Control)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive StmtOutcome where
  | next (state : RuntimeState) (stmt : StmtTerm)
  | done (state : RuntimeState)
  | control (state : RuntimeState) (control : Control)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive BodyOutcome where
  | next (state : RuntimeState) (body : BodyTerm)
  | done (state : RuntimeState)
  | control (state : RuntimeState) (control : Control)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

def returnValue : Option Num → Num
  | none => Num.zero
  | some n => n

def popFrame (st : RuntimeState) : RuntimeState :=
  { st with frames := st.frames.drop 1 }

mutual

def ExprTerm.ofExpr : Expr → ExprTerm
  | .num raw => .num raw
  | .var name => .var name
  | .special v => .special v
  | .arrayAccess name index => .arrayAccess name (ExprTerm.ofExpr index)
  | .assign lhs op rhs => .assign (LValTerm.ofLVal lhs) op (ExprTerm.ofExpr rhs)
  | .rel first rest => .rel (ExprTerm.ofExpr first) (ExprTerm.ofRelRest rest)
  | .bin op lhs rhs => .bin op (ExprTerm.ofExpr lhs) (ExprTerm.ofExpr rhs)
  | .unary .neg arg => .neg (ExprTerm.ofExpr arg)
  | .unary op arg =>
      match LValTerm.ofExpr? arg with
      | some target => .bump op target
      | none => .badBump op (ExprTerm.ofExpr arg)
  | .call name args => .call name (ArgTerm.ofArgs args)
  | .builtin fn none => .builtin fn none
  | .builtin fn (some arg) => .builtin fn (some (ExprTerm.ofExpr arg))
  | .paren body => .paren (ExprTerm.ofExpr body)
termination_by e => sizeOf e

def ExprTerm.ofRelRest : List (RelOp × Expr) → List (RelOp × ExprTerm)
  | [] => []
  | (op, e) :: rest => (op, ExprTerm.ofExpr e) :: ExprTerm.ofRelRest rest
termination_by rest => sizeOf rest

def LValTerm.ofLVal : LVal → LValTerm
  | .var name => .var name
  | .special v => .special v
  | .array name index => .array name (ExprTerm.ofExpr index)
termination_by lv => sizeOf lv

def LValTerm.ofExpr? : Expr → Option LValTerm
  | .var name => some (.var name)
  | .special v => some (.special v)
  | .arrayAccess name index => some (.array name (ExprTerm.ofExpr index))
  | .paren body => LValTerm.ofExpr? body
  | _ => none
termination_by e => sizeOf e

def ArgTerm.ofArg : Arg → ArgTerm
  | .expr e => .expr (ExprTerm.ofExpr e)
  | .arrayRef name => .arrayRef name
termination_by arg => sizeOf arg

def ArgTerm.ofArgs : List Arg → List ArgTerm
  | [] => []
  | arg :: rest => ArgTerm.ofArg arg :: ArgTerm.ofArgs rest
termination_by args => sizeOf args

def StmtTerm.ofStmt : Stmt → StmtTerm
  | .expr e => .expr e (ExprTerm.ofExpr e)
  | .str s => .str s
  | .auto params => .auto params
  | .if cond thenBranch => .ifThen (ExprTerm.ofExpr cond) (StmtTerm.ofStmt thenBranch)
  | .while cond body => .while cond (ExprTerm.ofExpr cond) (StmtTerm.ofStmt body)
  | .for init cond update body =>
      .seq (.eval (ExprTerm.ofExpr init))
        (.forCheck cond (ExprTerm.ofExpr cond) update (StmtTerm.ofStmt body))
  | .break => .break
  | .return none => .return none
  | .return (some e) => .return (some (ExprTerm.ofExpr e))
  | .quit => .quit
  | .block body => .block (.stmts (BodyTerm.ofBodyItems body))
termination_by stmt => sizeOf stmt

def StmtTerm.ofStmts : List Stmt → List StmtTerm
  | [] => []
  | stmt :: rest => StmtTerm.ofStmt stmt :: StmtTerm.ofStmts rest
termination_by stmts => sizeOf stmts

def BodyTerm.ofBodyItems : List BodyItem → List StmtTerm
  | [] => []
  | BodyItem.stmts stmts :: rest => StmtTerm.ofStmts stmts ++ BodyTerm.ofBodyItems rest
  | BodyItem.newline :: rest => BodyTerm.ofBodyItems rest
termination_by items => sizeOf items

end

def BodyTerm.ofBody (body : List BodyItem) : BodyTerm :=
  .stmts (BodyTerm.ofBodyItems body)

mutual

private def StmtTerm.containsQuit : StmtTerm → Bool
  | .done => false
  | .expr _ _ => false
  | .eval _ => false
  | .str _ => false
  | .auto _ => false
  | .ifThen _ thenBranch => StmtTerm.containsQuit thenBranch
  | .while _ _ body => StmtTerm.containsQuit body
  | .forCheck _ _ _ body => StmtTerm.containsQuit body
  | .forUpdate _ _ _ body => StmtTerm.containsQuit body
  | .loopBody body after => StmtTerm.containsQuit body || StmtTerm.containsQuit after
  | .seq first second => StmtTerm.containsQuit first || StmtTerm.containsQuit second
  | .break => false
  | .return none => false
  | .return (some _) => false
  | .quit => true
  | .block body => BodyTerm.containsQuit body
termination_by stmt => sizeOf stmt

private def BodyTerm.containsQuit : BodyTerm → Bool
  | .stmts stmts => StmtTerm.listContainsQuit stmts
termination_by body => sizeOf body

private def StmtTerm.listContainsQuit : List StmtTerm → Bool
  | [] => false
  | stmt :: rest => StmtTerm.containsQuit stmt || StmtTerm.listContainsQuit rest
termination_by stmts => sizeOf stmts

end

def TopItemTerm.containsQuit (item : TopItemTerm) : Bool :=
  match item with
  | .funDef defn => bodyContainsQuit defn.body
  | TopItemTerm.stmt s => StmtTerm.containsQuit s

def enterFunction (st : RuntimeState) (defn : FunDef)
    (argValues : List (Sum Num Name)) : ExprOutcome :=
  let frame : Frame := { constBase := st.ibase }
  let stWithFrame := { st with frames := frame :: st.frames }
  match bindParams stWithFrame defn.params argValues with
  | .error msg => .runtimeError stWithFrame msg
  | .ok st =>
      let st := bindAutoDecls st (collectAutos defn.body)
      .next st (.activeCall (BodyTerm.ofBody defn.body))

end SmallStep

end Bc
