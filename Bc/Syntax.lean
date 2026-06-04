/-
  Surface syntax AST for GNU bc 1.07.1.
-/

namespace Bc

/-- Project version string for the bc dialect being modelled. -/
def targetVersion : String := "1.07.1"

abbrev Name := String

inductive SpecialVar where
  | ibase | obase | scale | last | history | dot
  deriving Repr, BEq, DecidableEq

inductive Builtin where
  | length | sqrt | scale | read | random
  deriving Repr, BEq, DecidableEq

inductive RelOp where
  | eq | ne | le | ge | lt | gt
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod | pow
  deriving Repr, BEq, DecidableEq

inductive LogicOp where
  | and | or
  deriving Repr, BEq, DecidableEq

inductive AssignOp where
  | assign | addAssign | subAssign | mulAssign | divAssign | modAssign | powAssign
  deriving Repr, BEq, DecidableEq

inductive UnOp where
  | neg | not | preIncr | preDecr | postIncr | postDecr
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
  | rel (first : Expr) (rest : List (RelOp × Expr))
  | bin (op : BinOp) (lhs : Expr) (rhs : Expr)
  | logic (op : LogicOp) (lhs : Expr) (rhs : Expr)
  | unary (op : UnOp) (arg : Expr)
  | call (name : Name) (args : List Arg)
  | builtin (fn : Builtin) (arg : Option Expr)
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
  | refArray (name : Name)
  | varArray (name : Name)
  deriving Repr, BEq, DecidableEq

mutual
inductive Stmt where
  | expr (e : Expr)
  | str (value : String)
  | auto (params : List ParamDecl)
  | if (cond : Expr) (thenBranch : Stmt) (elseBranch : Option Stmt)
  | while (cond : Expr) (body : Stmt)
  | for (init : Option Expr) (cond : Option Expr) (update : Option Expr) (body : Stmt)
  | break
  | continue
  | return (value : Option Expr)
  | quit
  | halt
  | print (items : List PrintItem)
  | warranty
  | limits
  | block (body : List BodyItem)
  deriving Repr

inductive PrintItem where
  | expr (e : Expr)
  | str (value : String)
  deriving Repr

inductive BodyItem where
  | stmts (ss : List Stmt)
  | newline
  deriving Repr
end

structure FunDef where
  void : Bool
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
