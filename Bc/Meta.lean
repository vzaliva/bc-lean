/-
  Expression metadata mirroring bc.y flag bits (see bc/bc.y lines 446–453).
-/

import Bc.Syntax

namespace Bc

/-- Metadata carried on expressions for bc.y context checks. -/
structure ExprInfo where
  /-- `EX_COMP` — comparison or boolean operator present. -/
  hasComparison : Bool := false
  /-- `EX_PAREN` — wrapped in parentheses. -/
  inParens : Bool := false
  /-- Top-level operator is assignment (`EX_ASSGN` / value 0). -/
  topIsAssign : Bool := false
  /-- `EX_VOID` — void expression (deferred until symbol table). -/
  isVoid : Bool := false
  /-- `EX_EMPTY` — missing optional expression. -/
  isEmpty : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ExprInfo

def reg : ExprInfo := {}

def merge (a b : ExprInfo) : ExprInfo :=
  { hasComparison := a.hasComparison || b.hasComparison
    inParens := false
    topIsAssign := false
    isVoid := a.isVoid || b.isVoid
    isEmpty := a.isEmpty || b.isEmpty }

def withParen (i : ExprInfo) : ExprInfo :=
  { i with inParens := true, topIsAssign := false }

def assignRhs (i : ExprInfo) : ExprInfo :=
  { i with inParens := false, topIsAssign := false }

end ExprInfo

namespace Expr

mutual
  partial def info : Expr → ExprInfo
  | .num _ | .var _ | .special _ => ExprInfo.reg
  | .arrayAccess _ idx => (info idx).assignRhs
  | .assign _ _ rhs =>
      { hasComparison := (info rhs).hasComparison
        inParens := false
        topIsAssign := true
        isVoid := (info rhs).isVoid
        isEmpty := false }
  | .rel first rest =>
      if rest.isEmpty then
        (info first).assignRhs
      else
        { hasComparison := true, inParens := false, topIsAssign := false
          isVoid := (info first).isVoid || rest.any (fun (_, e) => (info e).isVoid)
          isEmpty := false }
  | .bin _ lhs rhs => ExprInfo.merge (info lhs) (info rhs)
  | .logic _ lhs rhs =>
      { hasComparison := true, inParens := false, topIsAssign := false
        isVoid := (info lhs).isVoid || (info rhs).isVoid, isEmpty := false }
  | .unary op arg =>
      match op with
      | .not =>
          { hasComparison := true, inParens := false, topIsAssign := false
            isVoid := (info arg).isVoid, isEmpty := false }
      | _ => (info arg).assignRhs
  | .call _ args =>
      { hasComparison := args.any (fun a => match a with | .expr e => (info e).hasComparison | _ => false)
        inParens := false, topIsAssign := false, isVoid := false, isEmpty := false }
  | .builtin _ arg =>
      match arg with
      | none => ExprInfo.reg
      | some e => (info e).assignRhs
  | .paren body => ExprInfo.withParen (info body)

  partial def infoLVal : LVal → ExprInfo
  | .var _ | .special _ => ExprInfo.reg
  | .array _ idx => (info idx).assignRhs
end

partial def children : Expr → List Expr
  | .num _ | .var _ | .special _ => []
  | .arrayAccess _ idx => [idx]
  | .assign lhs _ rhs =>
      match lhs with
      | .array _ idx => idx :: [rhs]
      | _ => [rhs]
  | .rel first rest => first :: rest.map Prod.snd
  | .bin _ l r | .logic _ l r => [l, r]
  | .unary _ a => [a]
  | .call _ args => args.filterMap fun | .expr e => some e | _ => none
  | .builtin _ arg => arg.toList
  | .paren b => [b]

end Expr

end Bc
