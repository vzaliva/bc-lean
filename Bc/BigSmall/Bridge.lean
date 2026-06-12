/-
  Alignment lemmas between source AST and small-step residual terms.
-/

import Bc.BigSmall.Fuel

namespace Bc

namespace BigSmall

open SmallStep

theorem LValTerm.ofExpr?_eq (e : Expr) :
    LValTerm.ofExpr? e = (lvalOfExpr? e).map LValTerm.ofLVal := by
  match e with
  | .var _ => simp [LValTerm.ofExpr?, lvalOfExpr?, LValTerm.ofLVal]
  | .special _ => simp [LValTerm.ofExpr?, lvalOfExpr?, LValTerm.ofLVal]
  | .arrayAccess name index =>
      simp [LValTerm.ofExpr?, lvalOfExpr?, LValTerm.ofLVal]
  | .paren body => simp [LValTerm.ofExpr?, lvalOfExpr?, LValTerm.ofExpr?_eq body]
  | .num _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .assign _ _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .rel _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .bin _ _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .unary _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .call _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]
  | .builtin _ _ => simp [LValTerm.ofExpr?, lvalOfExpr?]

theorem ProgramTerm.ofProgram_eq (program : Program) :
    ProgramTerm.ofProgram program =
      program.foldr (fun item acc => TopItemTerm.ofTopItem item ++ acc) [] := by
  induction program with
  | nil => rfl
  | cons item rest ih =>
      simp [ProgramTerm.ofProgram, ih, List.foldr]

end BigSmall

end Bc
