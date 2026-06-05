/-
  Stable pretty-printing for bc AST golden tests.
-/

import Bc.Syntax

open Std

namespace Bc

private def commaLine : Format := Format.text "," ++ Format.line

private def bracket (l r : String) (xs : List Format) : Format :=
  Format.bracket l (Format.joinSep xs commaLine) r

private def ppSpecialVar : SpecialVar → Format
  | .ibase => "ibase"
  | .obase => "obase"
  | .scale => "scale"

private def ppBuiltin : Builtin → Format
  | .length => "length"
  | .sqrt => "sqrt"
  | .scale => "scale"

private def ppRelOp : RelOp → Format
  | .eq => "=="
  | .ne => "!="
  | .le => "<="
  | .ge => ">="
  | .lt => "<"
  | .gt => ">"

private def ppBinOp : BinOp → Format
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .pow => "^"

private def ppAssignOp : AssignOp → Format
  | .assign => "="
  | .addAssign => "+="
  | .subAssign => "-="
  | .mulAssign => "*="
  | .divAssign => "/="
  | .modAssign => "%="
  | .powAssign => "^="

private def ppUnOp : UnOp → Format
  | .neg => "-"
  | .preIncr => "++"
  | .preDecr => "--"
  | .postIncr => "++"
  | .postDecr => "--"

mutual
  partial def ppLVal : LVal → Format
  | .var n => Format.text n
  | .array n idx => Format.text n ++ Format.text "[" ++ ppExpr idx ++ Format.text "]"
  | .special v => ppSpecialVar v

  partial def ppExpr : Expr → Format
  | .num v => Format.text v
  | .var n => Format.text n
  | .special v => ppSpecialVar v
  | .arrayAccess n idx => Format.text n ++ Format.text "[" ++ ppExpr idx ++ Format.text "]"
  | .assign lhs op rhs =>
      ppLVal lhs ++ Format.text " " ++ ppAssignOp op ++ Format.text " " ++ ppExpr rhs
  | .rel first rest =>
      let chain := rest.foldl (fun acc (op, e) =>
        acc ++ Format.text " " ++ ppRelOp op ++ Format.text " " ++ ppExpr e) (ppExpr first)
      chain
  | .bin op lhs rhs =>
      ppExpr lhs ++ Format.text " " ++ ppBinOp op ++ Format.text " " ++ ppExpr rhs
  | .unary op arg =>
      match op with
      | .postIncr => ppExpr arg ++ Format.text "++"
      | .postDecr => ppExpr arg ++ Format.text "--"
      | _ => ppUnOp op ++ ppExpr arg
  | .call name args =>
      Format.text name ++ bracket "(" ")" (args.map ppArg)
  | .builtin fn arg =>
      let head := ppBuiltin fn ++ Format.text "("
      match arg with
      | none => head ++ Format.text ")"
      | some e => head ++ ppExpr e ++ Format.text ")"
  | .paren body => Format.text "(" ++ ppExpr body ++ Format.text ")"

  partial def ppArg : Arg → Format
  | .expr e => ppExpr e
  | .arrayRef n => Format.text n ++ Format.text "[]"
end

private def ppParamDecl : ParamDecl → Format
  | .scalar n => Format.text n
  | .array n => Format.text n ++ Format.text "[]"

mutual
partial def ppBodyItem : BodyItem → Format
  | .stmts ss => Format.joinSep (ss.map ppStmt) (Format.text "; " ++ Format.line)
  | .newline => Format.nil

partial def ppStmt : Stmt → Format
  | .expr e => ppExpr e
  | .str s => Format.text (String.quote s)
  | .auto ps => Format.text "auto " ++ bracket "" "" (ps.map ppParamDecl)
  | .if cond t =>
      Format.text "if (" ++ ppExpr cond ++ Format.text ") " ++ ppStmt t
  | .while cond body =>
      Format.text "while (" ++ ppExpr cond ++ Format.text ") " ++ ppStmt body
  | .for init cond upd body =>
      Format.text "for (" ++ ppExpr init ++ Format.text "; " ++ ppExpr cond ++
        Format.text "; " ++ ppExpr upd ++ Format.text ") " ++ ppStmt body
  | .break => "break"
  | .return none => "return"
  | .return (some e) => Format.text "return " ++ ppExpr e
  | .quit => "quit"
  | .block body => bracket "{" "}" (body.map ppBodyItem)
end

partial def ppFunDef (defn : FunDef) : Format :=
  Format.text "define " ++ Format.text defn.name ++ Format.text " " ++
    bracket "(" ")" (defn.params.map ppParamDecl) ++ Format.line ++
    bracket "{" "}" (defn.body.map ppBodyItem)

partial def ppTopItem : TopItem → Format
  | .funDef d => ppFunDef d
  | .stmts ss => Format.joinSep (ss.map ppStmt) (Format.text "; " ++ Format.line)

def ppProgram (prog : Program) : String :=
  Format.pretty (Format.joinSep (prog.map ppTopItem) Format.line)

end Bc
