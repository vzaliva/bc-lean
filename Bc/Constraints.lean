/-
  bc.y expression-context rules (`ct_warn` / context checks). Not operational semantics.
-/

import Bc.Meta

namespace Bc

structure CheckCtx where
  inFunction : Bool := false
  inVoidFunction : Bool := false
  loopDepth : Nat := 0
  deriving Repr, BEq

namespace CheckCtx

def inFun (ctx : CheckCtx) (isVoid : Bool) : CheckCtx :=
  { ctx with inFunction := true, inVoidFunction := isVoid }

def inLoop (ctx : CheckCtx) : CheckCtx :=
  { ctx with loopDepth := ctx.loopDepth + 1 }

end CheckCtx

namespace Constraints

private def checkReturnValue (ctx : CheckCtx) : Except String Unit :=
  if ctx.inVoidFunction then
    throw "Return expression in a void function."
  else
    pure ()

partial def checkExpr (ctx : CheckCtx) (_loc : String) (e : Expr) : Except String Unit := do
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
      checkStmt (CheckCtx.inLoop ctx) body
  | .for init cond upd body => do
      match init with
      | none => pure ()
      | some e => checkExpr ctx "" e
      match cond with
      | none => pure ()
      | some e => checkExpr ctx "" e
      match upd with
      | none => pure ()
      | some e => checkExpr ctx "" e
      checkStmt (CheckCtx.inLoop ctx) body
  | .break =>
      if ctx.loopDepth == 0 then
        throw "Break outside a for/while"
  | .continue =>
      if ctx.loopDepth == 0 then
        throw "Continue outside a for"
  | .return none =>
      if !ctx.inFunction then
        throw "Return outside of a function."
  | .return (some e) => do
      if !ctx.inFunction then
        throw "Return outside of a function."
      checkReturnValue ctx
      checkExpr ctx "" e
  | .print items =>
      for it in items do
        match it with
        | .expr e => checkExpr ctx "" e
        | .str _ => pure ()
  | .block body => checkBody ctx body
  | .auto _ | .quit | .halt | .warranty | .limits | .str _ => pure ()
end

partial def checkFunDef (defn : FunDef) : Except String Unit :=
  checkBody (CheckCtx.inFun {} defn.void) defn.body

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
