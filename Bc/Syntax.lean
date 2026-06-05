/-
  Surface syntax AST for the POSIX bc subset.
-/

namespace Bc

/-- Reference implementation version used for comparison runs. -/
def targetVersion : String := "1.07.1"

abbrev Name := String

inductive SpecialVar where
  | ibase | obase | scale
  deriving Repr, BEq, DecidableEq

inductive Builtin where
  | length | sqrt | scale
  deriving Repr, BEq, DecidableEq

inductive RelOp where
  | eq | ne | le | ge | lt | gt
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod | pow
  deriving Repr, BEq, DecidableEq

inductive AssignOp where
  | assign | addAssign | subAssign | mulAssign | divAssign | modAssign | powAssign
  deriving Repr, BEq, DecidableEq

inductive UnOp where
  | neg | preIncr | preDecr | postIncr | postDecr
  deriving Repr, BEq, DecidableEq

mutual
inductive LVal where
  | var (name : Name)
  | array (name : Name) (index : Expr)
  | special (var : SpecialVar)
  deriving Repr

inductive Expr where
  | num (value : String)
  | var (name : Name)
  | special (var : SpecialVar)
  | arrayAccess (name : Name) (index : Expr)
  | assign (lhs : LVal) (op : AssignOp) (rhs : Expr)
  /-- Relational expression. POSIX bc permits only a *single* relational operator
      and only inside a condition; this is an intentional super-set (the chain is
      evaluated left-associatively, yielding 0/1) because the parser is kept
      syntax-only and does not enforce the contextual restriction. -/
  | rel (first : Expr) (rest : List (RelOp × Expr))
  | bin (op : BinOp) (lhs : Expr) (rhs : Expr)
  | unary (op : UnOp) (arg : Expr)
  | call (name : Name) (args : List Arg)
  | builtin (fn : Builtin) (arg : Option Expr)
  /-- Parenthesised expression. Semantically transparent (both evaluators just
      recurse); retained so the AST round-trips faithfully through the
      pretty-printer for golden tests. -/
  | paren (body : Expr)
  deriving Repr

inductive Arg where
  | expr (e : Expr)
  | arrayRef (name : Name)
  deriving Repr
end

inductive ParamDecl where
  | scalar (name : Name)
  | array (name : Name)
  deriving Repr, BEq, DecidableEq

mutual
inductive Stmt where
  | expr (e : Expr)
  | str (value : String)
  /-- `auto` declaration. Only meaningful at the head of a function body (where
      the evaluator collects it via `collectAutos`); modelled as a statement to
      keep the parser syntax-only, and treated as a no-op when executed. -/
  | auto (params : List ParamDecl)
  | if (cond : Expr) (thenBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  | for (init : Expr) (cond : Expr) (update : Expr) (body : Stmt)
  | break
  | return (value : Option Expr)
  | quit
  | block (body : List BodyItem)
  deriving Repr

inductive BodyItem where
  | stmts (ss : List Stmt)
  | newline
  deriving Repr
end

structure FunDef where
  name : Name
  params : List ParamDecl
  body : List BodyItem
  deriving Repr

inductive TopItem where
  | funDef (defn : FunDef)
  | stmts (ss : List Stmt)
  deriving Repr

abbrev Program := List TopItem

end Bc
