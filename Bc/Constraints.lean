/-
  bc.y expression-context rules (`ct_warn` / context checks). Not operational semantics.
-/

import Bc.Meta

namespace Bc

structure CheckCtx where
  inFunction : Bool := false
  deriving Repr, BEq

namespace CheckCtx

def inFun (ctx : CheckCtx) : CheckCtx := { ctx with inFunction := true }

end CheckCtx

namespace Constraints

private def checkComparison (msg : String) (i : ExprInfo) : Except String Unit :=
  if i.hasComparison then .error msg else .ok ()

private def checkAssignRhs (i : ExprInfo) : Except String Unit :=
  if i.topIsAssign then .error "comparison in assignment" else .ok ()

private def checkReturnExpr (i : ExprInfo) : Except String Unit := do
  if i.hasComparison then
    throw "comparison in return expresion"
  if !i.inParens then
    throw "return expression requires parenthesis"

partial def checkExpr (ctx : CheckCtx) (_loc : String) (e : Expr) : Except String Unit := do
  match e with
  | .arrayAccess _ idx => checkComparison "comparison in subscript" (Expr.info idx)
  | .assign _ _ rhs => checkAssignRhs (Expr.info rhs)
  | .call _ args =>
      for a in args do
        match a with
        | .expr arg => checkComparison "comparison in argument" (Expr.info arg)
        | .arrayRef _ => pure ()
  | .builtin _ arg =>
      match arg with
      | none => pure ()
      | some e => checkComparison "comparison in argument" (Expr.info e)
  | _ => pure ()
  for sub in e.children do
    checkExpr ctx "" sub

mutual
partial def checkBody (ctx : CheckCtx) (body : List BodyItem) : Except String Unit := do
  for item in body do
    match item with
    | .newline => pure ()
    | .stmts ss =>
        for s in ss do
          checkStmt ctx s

partial def checkStmt (ctx : CheckCtx) (s : Stmt) : Except String Unit := do
  match s with
  | .expr e =>
      -- bc warns on comparison in expression statements; corpus programs use
      -- comparisons only in controlled contexts, so we do not reject here.
      checkExpr ctx "" e
  | .if cond t e =>
      checkExpr ctx "" cond
      checkStmt ctx t
      match e with | none => pure () | some s' => checkStmt ctx s'
  | .while cond body =>
      checkExpr ctx "" cond
      checkStmt ctx body
  | .for init cond upd body => do
      match init with
      | none => pure ()
      | some e => checkComparison "Comparison in first for expression" (Expr.info e)
      match cond with
      | none => pure ()
      | some e => checkExpr ctx "" e
      match upd with
      | none => pure ()
      | some e => checkComparison "Comparison in third for expression" (Expr.info e)
      checkStmt ctx body
  | .return none =>
      if !ctx.inFunction then
        throw "Return outside of a function."
  | .return (some e) => do
      if !ctx.inFunction then
        throw "Return outside of a function."
      checkReturnExpr (Expr.info e)
      checkExpr ctx "" e
  | .print items =>
      for it in items do
        match it with
        | .expr e => checkExpr ctx "" e
        | .str _ => pure ()
  | .block body => checkBody ctx body
  | .auto _ | .break | .continue | .quit | .halt | .warranty | .limits | .str _ => pure ()
end

partial def checkFunDef (defn : FunDef) : Except String Unit :=
  checkBody (CheckCtx.inFun {}) defn.body

partial def checkTopItem (item : TopItem) : Except String Unit :=
  match item with
  | .funDef d => checkFunDef d
  | .stmts ss =>
      for s in ss do
        checkStmt {} s

def checkProgram (_path : String) (prog : Program) : Except String Program := do
  for item in prog do
    checkTopItem item
  return prog

end Constraints

end Bc
