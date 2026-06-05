/-
  Tree-sitter XML → bc surface AST.
-/

import Bc.Syntax
import Bc.Xml.Basic
import Bc.Xml.Parser

open System
open Bc.Xml

namespace Bc

private def forbiddenParseNodes := ["ERROR", "MISSING", "UNEXPECTED"]

private def assertCleanXml (xml : String) : Except String Unit := do
  for tag in forbiddenParseNodes do
    if xml.contains s!"<{tag}" || xml.contains s!"<{tag} " then
      throw s!"tree-sitter parse tree contains {tag} node"

private def trimText (s : String) : String :=
  s.trimAscii.toString

private def textOf (content : Array Content) : String :=
  content.foldl (init := "") fun acc c =>
    match c with
    | .Character s => acc ++ trimText s
    | _ => acc

private def filterElements (content : Array Content) : Array Element :=
  content.filterMap fun
    | .Element e => some e
    | _ => none

private def childElements (x : Element) : Array Element :=
  match x with
  | .Element _ _ content => filterElements content

private def charTokens (x : Element) : List String :=
  match x with
  | .Element _ _ content =>
      content.toList.filterMap fun
        | .Character s =>
            let t := trimText s
            if t.isEmpty then none else some t
        | _ => none

private def leadingTextBeforeField (field : String) (x : Element) : String :=
  match x with
  | .Element _ _ content =>
      let rec go : List Content → String → String
        | [], acc => acc
        | .Character s :: rest, acc => go rest (acc ++ " " ++ trimText s)
        | .Element (.Element _ attrs _) :: rest, acc =>
            if attrs.get? "field" == some field then acc else go rest acc
        | _ :: rest, acc => go rest acc
      go content.toList ""

private def fieldsNamed (x : Element) (field : String) : Array Element :=
  childElements x |>.filter fun e =>
    match e with
    | .Element _ attrs _ => attrs.get? "field" == some field

private def fieldAt (x : Element) (field : String) : Option Element :=
  (fieldsNamed x field)[0]?

private def mapMToList {α β} (xs : Array α) (f : α → Except String β) : Except String (List β) := do
  let arr ← xs.mapM f
  return arr.toList

private def elementName (e : Element) : String :=
  match e with | .Element n _ _ => n

private structure Source where
  lines : Array String

private def Source.ofString (s : String) : Source :=
  { lines := (s.splitOn "\n").toArray }

private def attrNat (key : String) (x : Element) : Except String Nat :=
  match x with
  | .Element name attrs _ =>
      match attrs.get? key with
      | none => throw s!"missing {key} attribute in {name}"
      | some raw =>
          match raw.toNat? with
          | some n => pure n
          | none => throw s!"invalid {key} attribute in {name}: {raw}"

private def sourceLine (src : Source) (row : Nat) : Except String String :=
  match src.lines[row]? with
  | some line => pure line
  | none => throw s!"source span row out of range: {row}"

private def sliceLine (line : String) (startCol endCol : Nat) : String :=
  ((line.drop startCol).take (endCol - startCol)).toString

private def joinWithNewlines : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun acc line => acc ++ "\n" ++ line) x

private def sourceSlice (src : Source) (x : Element) : Except String String := do
  let srow ← attrNat "srow" x
  let scol ← attrNat "scol" x
  let erow ← attrNat "erow" x
  let ecol ← attrNat "ecol" x
  if srow == erow then
    let line ← sourceLine src srow
    return sliceLine line scol ecol
  else
    let firstLine ← sourceLine src srow
    let lastLine ← sourceLine src erow
    let mut parts : List String := [sliceLine firstLine scol firstLine.length]
    for offset in List.range (erow - srow - 1) do
      let line ← sourceLine src (srow + 1 + offset)
      parts := parts ++ [line]
    parts := parts ++ [sliceLine lastLine 0 ecol]
    return joinWithNewlines parts

private def stringLiteralBody (raw : String) : String :=
  if raw.length >= 2 then
    ((raw.drop 1).take (raw.length - 2)).toString
  else
    raw

private def stringValueFromSource (src : Source) (x : Element) : Except String String := do
  return stringLiteralBody (← sourceSlice src x)

private def firstChild (x : Element) : Except String Element :=
  match (childElements x)[0]? with
  | some e => .ok e
  | none => .error s!"no child elements in {elementName x}"

private def singleElement (tag : String) (x : Element) : Except String Element :=
  match childElements x |>.find? fun e => elementName e == tag with
  | some e => .ok e
  | none => .error s!"expected element {tag} in {elementName x}"

private def optionalElement (tag : String) (x : Element) : Except String (Option Element) :=
  match childElements x |>.find? fun e => elementName e == tag with
  | some e => .ok (some e)
  | none => .ok none

private def expectTag (tag : String) (x : Element) : Except String Element :=
  match x with
  | .Element name _ _ =>
      if name == tag then .ok x else .error s!"expected {tag}, got {name}"

private def parseRelOp (s : String) : Except String RelOp :=
  match s with
  | "==" => .ok .eq
  | "!=" => .ok .ne
  | "<=" => .ok .le
  | ">=" => .ok .ge
  | "<" => .ok .lt
  | ">" => .ok .gt
  | _ => .error s!"unknown relational operator: {s}"

private def parseBinOp (s : String) : Except String BinOp :=
  match s with
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "/" => .ok .div
  | "%" => .ok .mod
  | "^" => .ok .pow
  | _ => .error s!"unknown binary operator: {s}"

private def parseAssignOp (s : String) : Except String AssignOp :=
  match trimText s with
  | "=" => .ok .assign
  | "+=" => .ok .addAssign
  | "-=" => .ok .subAssign
  | "*=" => .ok .mulAssign
  | "/=" => .ok .divAssign
  | "%=" => .ok .modAssign
  | "^=" => .ok .powAssign
  | op => .error s!"unknown assignment operator: {op}"

private def parseSpecialVar (s : String) : Except String SpecialVar :=
  match trimText s with
  | "ibase" => .ok .ibase
  | "obase" => .ok .obase
  | "scale" => .ok .scale
  | "last" => .ok .last
  | "history" => .ok .history
  | "." => .ok .dot
  | v => .error s!"unknown special variable: {v}"

private def contentOf (e : Element) : Array Content :=
  match e with | .Element _ _ c => c

private def knownBuiltinNames : List String :=
  ["length", "sqrt", "scale", "read", "random"]

private def builtinNameFrom (x : Element) : Except String String := do
  let raw := textOf (contentOf x)
  match knownBuiltinNames.find? (fun name => raw.contains name) with
  | some name => .ok name
  | none => throw s!"missing builtin name in {elementName x} (text {raw})"

private def parseBuiltinName (s : String) : Except String Builtin :=
  match trimText s with
  | "length" => .ok .length
  | "sqrt" => .ok .sqrt
  | "scale" => .ok .scale
  | "read" => .ok .read
  | "random" => .ok .random
  | v => .error s!"unknown builtin: {v}"

private def headCharToken (x : Element) : Except String String :=
  match charTokens x with
  | op :: _ => .ok op
  | [] => .error s!"expected operator token in {elementName x}"

private def foldChained (parseOp : String → Except String α) (mk : α → Expr → Expr → Expr)
    (first : Expr) (ops : List String) (rhss : List Expr) : Except String Expr := do
  if ops.length ≠ rhss.length then
    throw s!"operator/operand count mismatch ({ops.length} vs {rhss.length})"
  let mut acc := first
  for (opStr, rhs) in ops.zip rhss do
    let op ← parseOp opStr
    acc := mk op acc rhs
  return acc

private def foldChainedRight (parseOp : String → Except String α)
    (mk : α → Expr → Expr → Expr) (first : Expr) (ops : List String) (rhss : List Expr) :
    Except String Expr := do
  if ops.length ≠ rhss.length then
    throw s!"operator/operand count mismatch ({ops.length} vs {rhss.length})"
  match ops, rhss with
  | [], [] => return first
  | opStr :: ops', rhs :: rhss' =>
      let op ← parseOp opStr
      let right ← foldChainedRight parseOp mk rhs ops' rhss'
      return mk op first right
  | _, _ => throw "operator/operand count mismatch"
termination_by ops

private def runTreeSitterXml (file : String) : IO String := do
  let cwd ← IO.currentDir
  let configPath := cwd / "config.json"
  let output ← IO.Process.output {
    cmd := "tree-sitter"
    args := #["parse", "-x", file, "--config-path", toString configPath]
    stderr := .piped
    stdout := .piped
  }
  if output.exitCode ≠ 0 then
    throw <| IO.userError s!"tree-sitter failed on {file}:\n{output.stderr}"
  return output.stdout

private def lvalToExpr : LVal → Expr
  | .var n => .var n
  | .special v => .special v
  | .array n idx => .arrayAccess n idx

mutual

  private partial def xmlToExpr : Element → Except String Expr
  | x =>
      expectTag "expression" x >>= xmlToExpression

  private partial def xmlToExpression (x : Element) : Except String Expr := do
    let elems := childElements x
    match elems[0]? with
    | none => throw "empty expression"
    | some e =>
        match e with
        | .Element "assignment_expression" _ _ => xmlToAssign e
        | .Element "logical_or_expression" _ _ => xmlToOr e
        | .Element name _ _ => throw s!"unexpected expression form: {name}"

  private partial def xmlToAssign (x : Element) : Except String Expr := do
    let lhsEl ← singleElement "named_expression" x
    let lhs ← xmlToLVal lhsEl
    let opEl ← singleElement "assign_op" x
    let opStr := textOf (contentOf opEl)
    let op ← parseAssignOp opStr
    let rhsEl ← singleElement "expression" x
    let rhs ← xmlToExpression rhsEl
    return .assign lhs op rhs

  private partial def xmlToOr (x : Element) : Except String Expr := do
    let firstEl ← singleElement "logical_and_expression" x
    let first ← xmlToAnd firstEl
    let ops := charTokens x |>.filter (· == "||")
    let rhss ← mapMToList (fieldsNamed x "right") xmlToAnd
    foldChained (fun _ => pure LogicOp.or) (fun _ l r => Expr.logic .or l r) first ops rhss

  private partial def xmlToAnd (x : Element) : Except String Expr := do
    let firstEl ← singleElement "logical_not_expression" x
    let first ← xmlToNot firstEl
    let ops := charTokens x |>.filter (· == "&&")
    let rhss ← mapMToList (fieldsNamed x "right") xmlToNot
    foldChained (fun _ => pure LogicOp.and) (fun _ l r => Expr.logic .and l r) first ops rhss

  private partial def xmlToNot (x : Element) : Except String Expr := do
    if charTokens x |>.contains "!" then do
      let rel ← singleElement "relational_expression" x
      let inner ← xmlToRel rel
      return .unary .not inner
    else
      singleElement "relational_expression" x >>= xmlToRel

  private partial def xmlToRel (x : Element) : Except String Expr := do
    let firstEl ← singleElement "additive_expression" x
    let first ← xmlToAdd firstEl
    let opEls := fieldsNamed x "operator"
    let ops ← opEls.toList.mapM fun e => parseRelOp (textOf (match e with | .Element _ _ c => c))
    let rhss ← mapMToList (fieldsNamed x "right") xmlToAdd
    if ops.isEmpty then
      return first
    else
      if ops.length ≠ rhss.length then
        throw "relational operator/operand mismatch"
      return .rel first (ops.zip rhss)

  private partial def xmlToAdd (x : Element) : Except String Expr := do
    let firstEl ← singleElement "multiplicative_expression" x
    let first ← xmlToMul firstEl
    let ops := charTokens x |>.filter (fun t => t == "+" || t == "-")
    let rhss ← mapMToList (fieldsNamed x "right") xmlToMul
    foldChained parseBinOp (fun op l r => Expr.bin op l r) first ops rhss

  private partial def xmlToMul (x : Element) : Except String Expr := do
    let firstEl ← singleElement "power_expression" x
    let first ← xmlToPow firstEl
    let ops := charTokens x |>.filter (fun t => t == "*" || t == "/" || t == "%")
    let rhss ← mapMToList (fieldsNamed x "right") xmlToPow
    foldChained parseBinOp (fun op l r => Expr.bin op l r) first ops rhss

  private partial def xmlToPow (x : Element) : Except String Expr := do
    let firstEl ← singleElement "unary_expression" x
    let first ← xmlToUnary firstEl
    let ops := charTokens x |>.filter (· == "^")
    let rhss ← mapMToList (fieldsNamed x "right") xmlToUnary
    foldChainedRight parseBinOp (fun op l r => Expr.bin op l r) first ops rhss

  private partial def xmlToUnary (x : Element) : Except String Expr := do
    let toks := charTokens x
    if toks.contains "++" then do
      let named ← match fieldAt x "operand" with
        | some e => pure e
        | none => singleElement "named_expression" x
      let lv ← xmlToLVal named
      return .unary .preIncr (lvalToExpr lv)
    else if toks.contains "--" then do
      let named ← match fieldAt x "operand" with
        | some e => pure e
        | none => singleElement "named_expression" x
      let lv ← xmlToLVal named
      return .unary .preDecr (lvalToExpr lv)
    else if toks.contains "-" then do
      let innerEl ← match fieldAt x "operand" with
        | some e => pure e
        | none => singleElement "unary_expression" x
      let inner ←
        if elementName innerEl == "unary_expression" then xmlToUnary innerEl
        else if elementName innerEl == "postfix_expression" then xmlToPostfix innerEl
        else throw "expected unary or postfix operand"
      return .unary .neg inner
    else
      singleElement "postfix_expression" x >>= xmlToPostfix

  private partial def xmlToPostfix (x : Element) : Except String Expr := do
    let postOps := charTokens x |>.filter (fun t => t == "++" || t == "--")
    if postOps.length > 0 || (fieldsNamed x "operator").size > 0 then do
      let lvEl ← match fieldAt x "operand" with
        | some e => pure e
        | none => singleElement "named_expression" x
      let lv ← xmlToLVal lvEl
      let opStr ← match postOps with
        | op :: _ => pure op
        | [] => headCharToken x
      let op := if opStr == "++" then UnOp.postIncr else UnOp.postDecr
      return .unary op (lvalToExpr lv)
    else
      singleElement "primary_expression" x >>= xmlToPrimary

  private partial def xmlToPrimary (x : Element) : Except String Expr := do
    let el ← firstChild x
    match elementName el with
    | "number" => return .num (trimText (textOf (contentOf el)))
    | "identifier" => return .var (trimText (textOf (contentOf el)))
    | "special_variable" =>
        parseSpecialVar (textOf (contentOf el)) >>= fun v => return .special v
    | "array_element" => do
        let arrEl ← singleElement "identifier" el
        let name := trimText (textOf (contentOf arrEl))
        let idxEl ← singleElement "expression" el
        let idx ← xmlToExpression idxEl
        return .arrayAccess name idx
    | "function_call" => xmlToCall el
    | "builtin_call" => xmlToBuiltin el
    | "parenthesized_expression" => do
        let innerEl ← singleElement "expression" el
        let inner ← xmlToExpression innerEl
        return .paren inner
    | name => throw s!"unexpected primary: {name}"

  private partial def xmlToCall (x : Element) : Except String Expr := do
    let nameEl ← singleElement "identifier" x
    let name := trimText (textOf (contentOf nameEl))
    match ← optionalElement "argument_list" x with
    | none => return .call name []
    | some al => do
        let args ← mapMToList (childElements al) xmlToArg
        return .call name args

  private partial def xmlToBuiltin (x : Element) : Except String Expr := do
    let fnName ← builtinNameFrom x
    let fn ← parseBuiltinName fnName
    match ← optionalElement "expression" x with
    | none => return .builtin fn none
    | some e => do
        let arg ← xmlToExpression e
        return .builtin fn (some arg)

  private partial def xmlToArg (x : Element) : Except String Arg := do
    let _ ← expectTag "argument" x
    let el ← firstChild x
    match elementName el with
    | "expression" =>
        let e ← xmlToExpression el
        return .expr e
    | "identifier" => return .arrayRef (trimText (textOf (contentOf el)))
    | _ => throw "invalid argument"

  private partial def xmlToLVal (x : Element) : Except String LVal := do
    let _ ← expectTag "named_expression" x
    let el ← firstChild x
    match elementName el with
    | "identifier" => return .var (trimText (textOf (contentOf el)))
    | "special_variable" =>
        parseSpecialVar (textOf (contentOf el)) >>= fun v => return .special v
    | "array_element" => do
        let arrEl ← singleElement "identifier" el
        let name := trimText (textOf (contentOf arrEl))
        let idxEl ← singleElement "expression" el
        let idx ← xmlToExpression idxEl
        return .array name idx
    | _ => throw "invalid named_expression"

  private partial def xmlToStmt (src : Source) (x : Element) : Except String Stmt := do
    let _ ← expectTag "statement" x
    let inner ← firstChild x
    match elementName inner with
    | "expression_statement" => do
        let eEl ← singleElement "expression" inner
        let e ← xmlToExpression eEl
        return .expr e
    | "string_statement" => do
        let sEl ← singleElement "string" inner
        return .str (← stringValueFromSource src sEl)
    | "auto_statement" => do
        let dl ← singleElement "define_list" inner
        let ps ← xmlToDefineList dl
        return .auto ps
    | "if_statement" => xmlToIf src inner
    | "while_statement" => xmlToWhile src inner
    | "for_statement" => xmlToFor src inner
    | "break_statement" => return .break
    | "continue_statement" => return .continue
    | "return_statement" => do
        match ← optionalElement "expression" inner with
        | none => return .return none
        | some eEl => do
            let e ← xmlToExpression eEl
            return .return (some e)
    | "quit_statement" => return .quit
    | "halt_statement" => return .halt
    | "print_statement" => do
        let pl ← singleElement "print_list" inner
        let items ← mapMToList (childElements pl) (xmlToPrintItem src)
        return .print items
    | "warranty_statement" => return .warranty
    | "limits_statement" => return .limits
    | "block_statement" => do
        let body ← xmlToBody src inner
        return .block body
    | name => throw s!"unexpected statement: {name}"

  private partial def xmlToIf (src : Source) (x : Element) : Except String Stmt := do
    let condEl ← singleElement "expression" x
    let cond ← xmlToExpression condEl
    let thenEl ← singleElement "statement" x
    let thenBranch ← xmlToStmt src thenEl
    let elseBranch ← match ← optionalElement "else_clause" x with
      | none => pure none
      | some ec => do
          let sEl ← singleElement "statement" ec
          let s ← xmlToStmt src sEl
          pure (some s)
    return .if cond thenBranch elseBranch

  private partial def xmlToWhile (src : Source) (x : Element) : Except String Stmt := do
    let condEl ← singleElement "expression" x
    let cond ← xmlToExpression condEl
    let bodyEl ← singleElement "statement" x
    let body ← xmlToStmt src bodyEl
    return .while cond body

  private partial def xmlToFor (src : Source) (x : Element) : Except String Stmt := do
    let init' ← match fieldAt x "init" with
      | none => pure none
      | some e => xmlToExpression e >>= fun v => pure (some v)
    let cond' ← match fieldAt x "condition" with
      | none => pure none
      | some e => xmlToExpression e >>= fun v => pure (some v)
    let upd' ← match fieldAt x "update" with
      | none => pure none
      | some e => xmlToExpression e >>= fun v => pure (some v)
    let bodyEl ← singleElement "statement" x
    let body ← xmlToStmt src bodyEl
    return .for init' cond' upd' body

  private partial def xmlToPrintItem (src : Source) (x : Element) : Except String PrintItem := do
    let _ ← expectTag "print_element" x
    let el ← firstChild x
    match elementName el with
    | "string" => return .str (← stringValueFromSource src el)
    | "expression" =>
        let e ← xmlToExpression el
        return .expr e
    | _ => throw "invalid print_element"

  private partial def xmlToDefineItem (x : Element) : Except String ParamDecl := do
    let _ ← expectTag "define_item" x
    let toks := charTokens x
    let nameEl ← singleElement "identifier" x
    let name := trimText (textOf (contentOf nameEl))
    if toks.contains "*" then
      return .varArray name
    else if toks.contains "&" then
      return .refArray name
    else if toks.contains "[" || (textOf (contentOf x)).contains "[" then
      return .array name
    else
      return .scalar name

  private partial def xmlToDefineList (x : Element) : Except String (List ParamDecl) := do
    let _ ← expectTag "define_list" x
    let mut acc : List ParamDecl := []
    for e in childElements x do
      if elementName e == "define_item" then do
        let p ← xmlToDefineItem e
        acc := acc ++ [p]
      else pure ()
    return acc

  private partial def xmlToBody (src : Source) (x : Element) : Except String (List BodyItem) := do
    let mut items : List BodyItem := []
    let mut pending : List Stmt := []
    match x with
    | .Element _ _ content =>
        for c in content do
          match c with
          | .Element e =>
              match elementName e with
              | "statement_sequence" => do
                  let stmts ← mapMToList (childElements e) fun sEl =>
                    if elementName sEl == "statement" then xmlToStmt src sEl
                    else throw "expected statement"
                  pending := pending ++ stmts
              | "newline" => do
                  if !pending.isEmpty then
                    items := items ++ [.stmts pending]
                    pending := []
                  items := items ++ [.newline]
              | "block_comment" | "line_comment" => pure ()
              | _ => pure ()
          | _ => pure ()
    if !pending.isEmpty then
      items := items ++ [.stmts pending]
    return items

  private partial def xmlToFunDef (src : Source) (x : Element) : Except String FunDef := do
    let _ ← expectTag "function_definition" x
    let void := (leadingTextBeforeField "name" x).contains "void"
    let name ← match fieldAt x "name" with
      | some el =>
          if elementName el == "identifier" then
            pure (trimText (textOf (contentOf el)))
          else
            throw "missing function name"
      | none => throw "missing function name"
    let params ← match ← optionalElement "parameter_list" x with
      | none => pure []
      | some pl => do
          let dl ← singleElement "define_list" pl
          xmlToDefineList dl
    let body ← xmlToBody src x
    return { void, name, params, body }

  private partial def xmlToStmtSeq (src : Source) (x : Element) : Except String (List Stmt) := do
    let _ ← expectTag "statement_sequence" x
    mapMToList (childElements x) fun e =>
      if elementName e == "statement" then xmlToStmt src e
      else throw "expected statement in sequence"

  private partial def xmlToTopItem (src : Source) (x : Element) : Except String TopItem := do
    match elementName x with
    | "function_definition" =>
        let d ← xmlToFunDef src x
        return .funDef d
    | "statement_sequence" => do
        let ss ← xmlToStmtSeq src x
        return .stmts ss
    | name => throw s!"unexpected top-level item: {name}"

end

private def xmlToProgram (src : Source) (root : Element) : Except String Program := do
  let root ← expectTag "source_file" root
  let mut items : List TopItem := []
  for e in childElements root do
    match elementName e with
    | "function_definition" =>
        let d ← xmlToFunDef src e
        items := items ++ [.funDef d]
    | "statement_sequence" =>
        let ss ← xmlToStmtSeq src e
        if ss.isEmpty then pure () else items := items ++ [.stmts ss]
    | "newline" => pure ()
    | "block_comment" | "line_comment" => pure ()
    | name => throw s!"unexpected source_file child: {name}"
  return items

def parseBcFile (path : String) : IO Program := do
  let source ← IO.FS.readFile path
  let xmlStr ← runTreeSitterXml path
  match assertCleanXml xmlStr with
  | .error e => throw <| IO.userError e
  | .ok () =>
      match parse xmlStr with
      | .error e => throw <| IO.userError s!"XML parse error in {path}: {e}"
      | .ok root =>
          match xmlToProgram (Source.ofString source) root with
          | .error e => throw <| IO.userError s!"AST conversion error in {path}: {e}"
          | .ok prog => return prog

end Bc
