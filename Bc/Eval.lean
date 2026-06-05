/-
  Fuel-bounded big-step operational semantics for GNU bc 1.07.1.

  The evaluator is intentionally executable: effects such as read(), random(),
  and output are modelled in IO.  Recursive semantic functions are fuel-bounded
  and total; parser/pretty-printer infrastructure may remain partial, but this
  module does not use partial definitions.
-/

import Bc.Syntax

namespace Bc

private def bcDimMax : Nat := 16777215
private def bcBaseMax : Nat := 2147483647
private def bcScaleMax : Nat := 2147483647

structure Num where
  coeff : Int
  scale : Nat
  deriving Repr, BEq, DecidableEq

namespace Num

def zero : Num := { coeff := 0, scale := 0 }
def one : Num := { coeff := 1, scale := 0 }

def isZero (n : Num) : Bool :=
  n.coeff == 0

def pow10 (n : Nat) : Int :=
  Int.ofNat (10 ^ n)

def alignCoeff (n : Num) (s : Nat) : Int :=
  n.coeff * pow10 (s - n.scale)

def intPart (n : Num) : Int :=
  Int.tdiv n.coeff (pow10 n.scale)

def absCoeffNat (n : Num) : Nat :=
  n.coeff.natAbs

private def natDigitsCore : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => natDigitsCore ((n + 1) / 10) (acc + 1)
termination_by n _ => n

def natDigits : Nat → Nat
  | 0 => 1
  | n + 1 => natDigitsCore (n + 1) 0

def integerDigits (n : Num) : Nat :=
  let a := absCoeffNat n
  if a == 0 then
    1
  else
    let ds := natDigits a
    if ds > n.scale then ds - n.scale else 1

def length (n : Num) : Nat :=
  let a := absCoeffNat n
  if a == 0 then
    1
  else if n.scale > 0 && a < 10 ^ n.scale then
    n.scale
  else
    natDigits a

def add (a b : Num) : Num :=
  let s := max a.scale b.scale
  { coeff := alignCoeff a s + alignCoeff b s, scale := s }

def sub (a b : Num) : Num :=
  let s := max a.scale b.scale
  { coeff := alignCoeff a s - alignCoeff b s, scale := s }

def neg (a : Num) : Num :=
  { a with coeff := -a.coeff }

def mulWithScale (a b : Num) (wantedScale : Nat) : Num :=
  let fullScale := a.scale + b.scale
  let prodScale := min fullScale (max wantedScale (max a.scale b.scale))
  let raw := a.coeff * b.coeff
  let drop := fullScale - prodScale
  { coeff := Int.tdiv raw (pow10 drop), scale := prodScale }

def div? (a b : Num) (wantedScale : Nat) : Except String Num := do
  if b.isZero then
    throw "Divide by zero"
  else
    let numerator := a.coeff * pow10 (b.scale + wantedScale)
    let denominator := b.coeff * pow10 a.scale
    return { coeff := Int.tdiv numerator denominator, scale := wantedScale }

def modulo? (a b : Num) (wantedScale : Nat) : Except String Num := do
  if b.isZero then
    throw "Modulo by zero"
  else
    let q ← div? a b wantedScale
    let rscale := max a.scale (b.scale + wantedScale)
    let prod :=
      { coeff := q.coeff * b.coeff * pow10 (rscale - (q.scale + b.scale)), scale := rscale }
    return sub { coeff := a.coeff * pow10 (rscale - a.scale), scale := rscale } prod

def powNatWithScale (base : Num) : Nat → Nat → Num
  | _, 0 => one
  | calcScale, e + 1 =>
      let prev := powNatWithScale base calcScale e
      mulWithScale prev base calcScale
termination_by _ e => e

def pow? (base expo : Num) (wantedScale : Nat) : Except String Num := do
  let e := expo.intPart
  let mag := e.natAbs
  if e == 0 then
    return one
  else if e < 0 then
    let p := powNatWithScale base (base.scale * mag) mag
    div? one p wantedScale
  else
    let resultScale := min (base.scale * mag) (max wantedScale base.scale)
    let p := powNatWithScale base (base.scale * mag) mag
    return { coeff := Int.tdiv p.coeff (pow10 (p.scale - resultScale)), scale := resultScale }

private def floorSqrtAux (n lo hi : Nat) : Nat → Nat
  | 0 => lo
  | fuel + 1 =>
      if hi <= lo then
        lo
      else if hi == lo + 1 then
        if hi * hi <= n then hi else lo
      else
        let mid := (lo + hi) / 2
        if mid * mid <= n then
          floorSqrtAux n mid hi fuel
        else
          floorSqrtAux n lo (mid - 1) fuel

def floorSqrt (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => floorSqrtAux (k + 1) 0 (k + 1) (k + 2)

def sqrt? (n : Num) (wantedScale : Nat) : Except String Num := do
  if n.coeff < 0 then
    throw "Square root of a negative number"
  else if n.isZero then
    return zero
  else if n.coeff == pow10 n.scale then
    return one
  else
    let rscale := max wantedScale n.scale
    let scaled :=
      if n.scale <= 2 * rscale then
        n.coeff.natAbs * 10 ^ (2 * rscale - n.scale)
      else
        n.coeff.natAbs / 10 ^ (n.scale - 2 * rscale)
    return { coeff := Int.ofNat (floorSqrt scaled), scale := rscale }

private def digitChar? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'A' <= c && c <= 'Z' then
    some (10 + c.toNat - 'A'.toNat)
  else if 'a' <= c && c <= 'z' then
    some (10 + c.toNat - 'a'.toNat)
  else
    none

private def cleanNumberChars (s : String) : List Char :=
  s.toList.filter fun c => c != '\\' && c != '\n' && c != '\r'

private def splitNumberChars (cs : List Char) : List Char × List Char :=
  let rec go (front rest : List Char) :=
    match rest with
    | [] => (front.reverse, [])
    | '.' :: tail => (front.reverse, tail)
    | c :: tail => go (c :: front) tail
  go [] cs

private def digitValue (base : Nat) (isSingleInteger : Bool) (d : Nat) : Nat :=
  if isSingleInteger then d else if d >= base then base - 1 else d

private def parseNatInBase (base : Nat) (singleInteger : Bool) (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * base + digitValue base singleInteger d) 0

def ofInputString (raw : String) (base : Nat) : Num :=
  let base := max 2 (min 36 base)
  let cleaned := cleanNumberChars raw
  let (negative, chars) :=
    match cleaned with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cleaned)
  let (intChars, fracChars) := splitNumberChars chars
  let intDigits := intChars.filterMap digitChar?
  let fracDigits := fracChars.filterMap digitChar?
  let singleInteger := intDigits.length == 1 && fracDigits.isEmpty
  let intVal := parseNatInBase base singleInteger intDigits
  let fracVal := parseNatInBase base false fracDigits
  let fracLen := fracDigits.length
  let sign (n : Int) := if negative then -n else n
  if fracLen == 0 then
    { coeff := sign (Int.ofNat intVal), scale := 0 }
  else
    let denom := base ^ fracLen
    let numerator := (intVal * denom + fracVal) * 10 ^ fracLen
    { coeff := sign (Int.ofNat (numerator / denom)), scale := fracLen }

def ofInt (i : Int) : Num :=
  { coeff := i, scale := 0 }

private def leftPad (width : Nat) (s : String) : String :=
  let missing := width - s.length
  String.ofList (List.replicate missing '0') ++ s

private def decimalDigits (n : Nat) : String :=
  toString n

def toDecimalString (n : Num) : String :=
  if n.coeff == 0 then
    "0"
  else
    let sign := if n.coeff < 0 then "-" else ""
    let digits := decimalDigits n.coeff.natAbs
    if n.scale == 0 then
      sign ++ digits
    else
      let padded := leftPad (n.scale + 1) digits
      let splitAt := padded.length - n.scale
      let intPart := (padded.take splitAt).toString
      let fracPart := (padded.drop splitAt).toString
      let intOut := if intPart == "0" then "" else intPart
      sign ++ intOut ++ "." ++ fracPart

private def digitToChar (d : Nat) : Char :=
  if d < 10 then
    Char.ofNat ('0'.toNat + d)
  else
    Char.ofNat ('A'.toNat + d - 10)

private def natToBaseDigits (base : Nat) : Nat → List Nat
  | 0 => [0]
  | n + 1 =>
      let rec go (fuel value : Nat) (acc : List Nat) : List Nat :=
        match fuel with
        | 0 => acc
        | fuel' + 1 =>
            if value == 0 then acc else go fuel' (value / base) ((value % base) :: acc)
      go (n + 2) (n + 1) []

def toBaseString (n : Num) (base : Nat) : String :=
  if base == 10 then
    toDecimalString n
  else
    let base := max 2 base
    let sign := if n.coeff < 0 then "-" else ""
    let absNum := { n with coeff := Int.ofNat n.coeff.natAbs }
    let intNat := absNum.intPart.natAbs
    let intDigits := natToBaseDigits base intNat
    let intStr :=
      if base <= 16 then
        String.ofList (intDigits.map digitToChar)
      else
        String.intercalate " " (intDigits.map toString)
    let fracCoeff := absNum.coeff - Int.ofNat intNat * pow10 absNum.scale
    if absNum.scale == 0 || fracCoeff == 0 then
      sign ++ intStr
    else
      let rec fracLoop (fuel : Nat) (coeff : Int) (acc : List Nat) : List Nat :=
        match fuel with
        | 0 => acc.reverse
        | fuel' + 1 =>
            let shifted := coeff * Int.ofNat base
            let d := Int.tdiv shifted (pow10 absNum.scale)
            let rest := shifted - d * pow10 absNum.scale
            fracLoop fuel' rest (d.natAbs :: acc)
      let fracDigits := fracLoop absNum.scale fracCoeff []
      let fracStr :=
        if base <= 16 then
          String.ofList (fracDigits.map digitToChar)
        else
          String.intercalate " " (fracDigits.map toString)
      sign ++ intStr ++ "." ++ fracStr

end Num

abbrev BcArray := List (Nat × Num)
abbrev ArrayId := Nat

structure Frame where
  scalars : List (Name × Num) := []
  arrays : List (Name × ArrayId) := []
  constBase : Nat := 10
  deriving Repr

structure RuntimeState where
  globals : List (Name × Num) := []
  globalArrays : List (Name × ArrayId) := []
  arrayStore : List (ArrayId × BcArray) := []
  nextArrayId : ArrayId := 0
  frames : List Frame := []
  functions : List (Name × FunDef) := []
  ibase : Nat := 10
  obase : Nat := 10
  scale : Nat := 0
  last : Num := Num.zero
  history : Int := -1
  input : List Char := []
  output : String := ""
  outCol : Nat := 0
  halted : Bool := false
  deriving Repr

inductive Value where
  | num (n : Num)
  | void
  deriving Repr, BEq

inductive Result (α : Type) where
  | ok (state : RuntimeState) (value : α)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive Control where
  | normal
  | break
  | continue
  | return (value : Value)
  | stop
  deriving Repr, BEq

def initialState (input : String := "") : RuntimeState :=
  { input := input.toList }

private def assocGet? [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  match xs with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else assocGet? rest k

private def assocContains [BEq α] (xs : List (α × β)) (k : α) : Bool :=
  match assocGet? xs k with
  | some _ => true
  | none => false

private def assocSet [BEq α] (xs : List (α × β)) (k : α) (v : β) : List (α × β) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if k' == k then (k, v) :: rest else (k', v') :: assocSet rest k v

private def assocErase [BEq α] (xs : List (α × β)) (k : α) : List (α × β) :=
  match xs with
  | [] => []
  | (k', v') :: rest =>
      if k' == k then rest else (k', v') :: assocErase rest k

private def setFunction (st : RuntimeState) (defn : FunDef) : RuntimeState :=
  { st with functions := assocSet st.functions defn.name defn }

private def lookupFunction (st : RuntimeState) (name : Name) : Option FunDef :=
  assocGet? st.functions name

private def currentConstBase (st : RuntimeState) : Nat :=
  match st.frames with
  | frame :: _ => frame.constBase
  | [] => st.ibase

private def lookupScalarInFrames (frames : List Frame) (name : Name) : Option Num :=
  match frames with
  | [] => none
  | f :: rest =>
      match assocGet? f.scalars name with
      | some n => some n
      | none => lookupScalarInFrames rest name

private def updateScalarInFrames (frames : List Frame) (name : Name) (value : Num) :
    Option (List Frame) :=
  match frames with
  | [] => none
  | f :: rest =>
      if assocContains f.scalars name then
        some ({ f with scalars := assocSet f.scalars name value } :: rest)
      else
        match updateScalarInFrames rest name value with
        | some rest' => some (f :: rest')
        | none => none

private def lookupScalar (st : RuntimeState) (name : Name) : Num :=
  match lookupScalarInFrames st.frames name with
  | some n => n
  | none =>
      match assocGet? st.globals name with
      | some n => n
      | none => Num.zero

private def setScalar (st : RuntimeState) (name : Name) (value : Num) : RuntimeState :=
  match updateScalarInFrames st.frames name value with
  | some frames => { st with frames := frames }
  | none => { st with globals := assocSet st.globals name value }

private def lookupArrayInFrames (frames : List Frame) (name : Name) : Option ArrayId :=
  match frames with
  | [] => none
  | f :: rest =>
      match assocGet? f.arrays name with
      | some id => some id
      | none => lookupArrayInFrames rest name

private def freshArray (st : RuntimeState) : RuntimeState × ArrayId :=
  let id := st.nextArrayId
  ({ st with nextArrayId := id + 1, arrayStore := assocSet st.arrayStore id [] }, id)

private def ensureGlobalArray (st : RuntimeState) (name : Name) : RuntimeState × ArrayId :=
  match assocGet? st.globalArrays name with
  | some id => (st, id)
  | none =>
      let (st, id) := freshArray st
      ({ st with globalArrays := assocSet st.globalArrays name id }, id)

private def ensureArrayId (st : RuntimeState) (name : Name) : RuntimeState × ArrayId :=
  match lookupArrayInFrames st.frames name with
  | some id => (st, id)
  | none => ensureGlobalArray st name

private def getArray (st : RuntimeState) (id : ArrayId) : BcArray :=
  match assocGet? st.arrayStore id with
  | some a => a
  | none => []

private def setArray (st : RuntimeState) (id : ArrayId) (a : BcArray) : RuntimeState :=
  { st with arrayStore := assocSet st.arrayStore id a }

private def getArrayElem (st : RuntimeState) (id : ArrayId) (idx : Nat) : Num :=
  match assocGet? (getArray st id) idx with
  | some n => n
  | none => Num.zero

private def setArrayElem (st : RuntimeState) (id : ArrayId) (idx : Nat) (value : Num) :
    RuntimeState :=
  setArray st id (assocSet (getArray st id) idx value)

private def indexOfNum? (n : Num) : Except String Nat := do
  let idx := n.intPart
  if idx < 0 then
    throw "Array subscript out of bounds"
  else
    let natIdx := idx.natAbs
    if natIdx > bcDimMax || (natIdx == 0 && !n.isZero) then
      throw "Array subscript out of bounds"
    else
      return natIdx

private def specialValue (st : RuntimeState) : SpecialVar → Num
  | .ibase => Num.ofInt (Int.ofNat st.ibase)
  | .obase => Num.ofInt (Int.ofNat st.obase)
  | .scale => Num.ofInt (Int.ofNat st.scale)
  | .last => st.last
  | .history => Num.ofInt st.history
  | .dot => st.last

private def assignSpecial (st : RuntimeState) (v : SpecialVar) (n : Num) : RuntimeState :=
  match v with
  | .ibase =>
      let raw := n.intPart
      let ibase :=
        if raw < 2 then 2
        else if raw > 36 then 36
        else raw.natAbs
      { st with ibase := ibase }
  | .obase =>
      let raw := n.intPart
      let obase :=
        if raw < 2 then 2
        else if raw.natAbs > bcBaseMax then bcBaseMax
        else raw.natAbs
      { st with obase := obase }
  | .scale =>
      let raw := n.intPart
      let scale :=
        if raw < 0 then 0
        else if raw.natAbs > bcScaleMax then bcScaleMax
        else raw.natAbs
      { st with scale := scale }
  | .last | .dot => { st with last := n }
  | .history => { st with history := n.intPart }

private def appendOutputChar (st : RuntimeState) (c : Char) : RuntimeState :=
  if c == '\n' then
    { st with output := st.output ++ "\n", outCol := 0 }
  else
    let nextCol := st.outCol + 1
    if nextCol == 69 then
      { st with output := st.output ++ "\\\n" ++ String.ofList [c], outCol := 1 }
    else
      { st with output := st.output ++ String.ofList [c], outCol := nextCol }

private def appendOutput (st : RuntimeState) (s : String) : RuntimeState :=
  s.toList.foldl appendOutputChar st

private def printNumNoNewline (st : RuntimeState) (n : Num) : RuntimeState :=
  let s := Num.toBaseString n st.obase
  { (appendOutput st s) with last := n }

private def printNumLine (st : RuntimeState) (n : Num) : RuntimeState :=
  appendOutput (printNumNoNewline st n) "\n"

private def decodeStringChars : List Char → List Char
  | [] => []
  | '\\' :: c :: rest =>
      let mapped? :=
        match c with
        | 'a' => some (Char.ofNat 7)
        | 'b' => some '\x08'
        | 'f' => some '\x0c'
        | 'n' => some '\n'
        | 'q' => some '"'
        | 'r' => some '\r'
        | 't' => some '\t'
        | '\\' => some '\\'
        | _ => none
      match mapped? with
      | some m => m :: decodeStringChars rest
      | none => decodeStringChars rest
  | c :: rest => c :: decodeStringChars rest

private def decodeBcString (s : String) : String :=
  String.ofList (decodeStringChars s.toList)

private def applyRel (op : RelOp) (a b : Num) : Bool :=
  let s := max a.scale b.scale
  let x := Num.alignCoeff a s
  let y := Num.alignCoeff b s
  match op with
  | .eq => x == y
  | .ne => x != y
  | .le => x <= y
  | .ge => x >= y
  | .lt => x < y
  | .gt => x > y

private def boolNum (b : Bool) : Num :=
  if b then Num.one else Num.zero

private def lvalOfExpr? : Expr → Option LVal
  | .var n => some (.var n)
  | .special v => some (.special v)
  | .arrayAccess n idx => some (.array n idx)
  | .paren e => lvalOfExpr? e
  | _ => none

private def collectAutosFromStmt (s : Stmt) : List ParamDecl :=
  match s with
  | .auto ps => ps
  | _ => []

private def collectAutosFromBodyItem : BodyItem → List ParamDecl
  | .stmts ss => ss.foldr (fun s acc => collectAutosFromStmt s ++ acc) []
  | .newline => []

private def collectAutos (body : List BodyItem) : List ParamDecl :=
  body.foldr (fun item acc => collectAutosFromBodyItem item ++ acc) []

private def bindAutoDecl (st : RuntimeState) (decl : ParamDecl) : RuntimeState :=
  match st.frames with
  | [] => st
  | frame :: rest =>
      match decl with
      | .scalar n =>
          { st with frames :=
              { frame with scalars := assocSet frame.scalars n Num.zero } :: rest }
      | .array n | .refArray n | .varArray n =>
          let (st, id) := freshArray st
          match st.frames with
          | frame :: rest =>
              { st with frames := { frame with arrays := assocSet frame.arrays n id } :: rest }
          | [] => st

private def bindAutoDecls (st : RuntimeState) (decls : List ParamDecl) : RuntimeState :=
  decls.foldl bindAutoDecl st

private def isTopAssignment : Expr → Bool
  | .assign _ _ _ => true
  | _ => false

mutual

def evalExpr (fuel : Nat) (st : RuntimeState) (expr : Expr) : IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match expr with
      | .num raw =>
          return .ok st (.num (Num.ofInputString raw (currentConstBase st)))
      | .var name =>
          return .ok st (.num (lookupScalar st name))
      | .special v =>
          return .ok st (.num (specialValue st v))
      | .arrayAccess name idxExpr =>
          match ← evalExpr fuel' st idxExpr with
          | .ok st (.num idxNum) =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  return .ok st (.num (getArrayElem st id idx))
              | .error msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression as subscript"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .assign lhs op rhs =>
          evalAssign fuel' st lhs op rhs
      | .rel first rest =>
          match ← evalExpr fuel' st first with
          | .ok st (.num n) => evalRelChain fuel' st n rest
          | .ok st .void => return .runtimeError st "void expression with comparison"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .bin op lhs rhs =>
          match ← evalExpr fuel' st lhs with
          | .ok st (.num a) =>
              match ← evalExpr fuel' st rhs with
              | .ok st (.num b) =>
                  let result? :=
                    match op with
                    | .add => Except.ok (Num.add a b)
                    | .sub => Except.ok (Num.sub a b)
                    | .mul => Except.ok (Num.mulWithScale a b st.scale)
                    | .div => Num.div? a b st.scale
                    | .mod => Num.modulo? a b st.scale
                    | .pow => Num.pow? a b st.scale
                  match result? with
                  | .ok n => return .ok st (.num n)
                  | .error msg => return .runtimeError st msg
              | .ok st .void => return .runtimeError st "void expression with binary operator"
              | .outOfFuel st => return .outOfFuel st
              | .runtimeError st msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression with binary operator"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .logic op lhs rhs =>
          match ← evalExpr fuel' st lhs with
          | .ok st (.num a) =>
              match op with
              | .and =>
                  if a.isZero then
                    return .ok st (.num Num.zero)
                  else
                    match ← evalExpr fuel' st rhs with
                    | .ok st (.num b) => return .ok st (.num (boolNum (!b.isZero)))
                    | .ok st .void => return .runtimeError st "void expression with &&"
                    | .outOfFuel st => return .outOfFuel st
                    | .runtimeError st msg => return .runtimeError st msg
              | .or =>
                  if !a.isZero then
                    return .ok st (.num Num.one)
                  else
                    match ← evalExpr fuel' st rhs with
                    | .ok st (.num b) => return .ok st (.num (boolNum (!b.isZero)))
                    | .ok st .void => return .runtimeError st "void expression with ||"
                    | .outOfFuel st => return .outOfFuel st
                    | .runtimeError st msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression with boolean operator"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .unary op arg =>
          evalUnary fuel' st op arg
      | .call name args =>
          evalCall fuel' st name args
      | .builtin fn arg =>
          evalBuiltin fuel' st fn arg
      | .paren body =>
          evalExpr fuel' st body

def evalRelChain (fuel : Nat) (st : RuntimeState) (left : Num)
    (rest : List (RelOp × Expr)) : IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match rest with
      | [] => return .ok st (.num left)
      | (op, rhs) :: tail =>
          match ← evalExpr fuel' st rhs with
          | .ok st (.num right) =>
              let out := boolNum (applyRel op left right)
              if tail.isEmpty then
                return .ok st (.num out)
              else
                evalRelChain fuel' st out tail
          | .ok st .void => return .runtimeError st "void expression with comparison"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def evalLValRef (fuel : Nat) (st : RuntimeState) (lv : LVal) :
    IO (Result (Sum (Name ⊕ SpecialVar) (ArrayId × Nat))) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match lv with
      | .var n => return .ok st (Sum.inl (Sum.inl n))
      | .special v => return .ok st (Sum.inl (Sum.inr v))
      | .array name idxExpr =>
          match ← evalExpr fuel' st idxExpr with
          | .ok st (.num idxNum) =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  return .ok st (Sum.inr (id, idx))
              | .error msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression as subscript"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def readRef (st : RuntimeState) (ref : Sum (Name ⊕ SpecialVar) (ArrayId × Nat)) : Num :=
  match ref with
  | .inl (.inl name) => lookupScalar st name
  | .inl (.inr v) => specialValue st v
  | .inr (id, idx) => getArrayElem st id idx

def writeRef (st : RuntimeState) (ref : Sum (Name ⊕ SpecialVar) (ArrayId × Nat)) (value : Num) :
    RuntimeState :=
  match ref with
  | .inl (.inl name) => setScalar st name value
  | .inl (.inr v) => assignSpecial st v value
  | .inr (id, idx) => setArrayElem st id idx value

def bumpRef (st : RuntimeState) (ref : Sum (Name ⊕ SpecialVar) (ArrayId × Nat)) (up : Bool) :
    RuntimeState × Num × Num :=
  let old := readRef st ref
  match ref with
  | .inl (.inr .ibase) =>
      let newBase := if up then (if st.ibase < 16 then st.ibase + 1 else st.ibase)
        else (if st.ibase > 2 then st.ibase - 1 else st.ibase)
      let newValue := Num.ofInt (Int.ofNat newBase)
      ({ st with ibase := newBase }, old, newValue)
  | .inl (.inr .obase) =>
      let newBase := if up then (if st.obase < bcBaseMax then st.obase + 1 else st.obase)
        else (if st.obase > 2 then st.obase - 1 else st.obase)
      let newValue := Num.ofInt (Int.ofNat newBase)
      ({ st with obase := newBase }, old, newValue)
  | .inl (.inr .scale) =>
      let newScale := if up then (if st.scale < bcScaleMax then st.scale + 1 else st.scale)
        else (if st.scale > 0 then st.scale - 1 else st.scale)
      let newValue := Num.ofInt (Int.ofNat newScale)
      ({ st with scale := newScale }, old, newValue)
  | _ =>
      let newValue := if up then Num.add old Num.one else Num.sub old Num.one
      (writeRef st ref newValue, old, newValue)

def evalAssign (fuel : Nat) (st : RuntimeState) (lhs : LVal) (op : AssignOp) (rhs : Expr) :
    IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match ← evalLValRef fuel' st lhs with
      | .ok st ref =>
          match ← evalExpr fuel' st rhs with
          | .ok st (.num rhsValue) =>
              let old := readRef st ref
              let result? :=
                match op with
                | .assign => Except.ok rhsValue
                | .addAssign => Except.ok (Num.add old rhsValue)
                | .subAssign => Except.ok (Num.sub old rhsValue)
                | .mulAssign => Except.ok (Num.mulWithScale old rhsValue st.scale)
                | .divAssign => Num.div? old rhsValue st.scale
                | .modAssign => Num.modulo? old rhsValue st.scale
                | .powAssign => Num.pow? old rhsValue st.scale
              match result? with
              | .ok n => return .ok (writeRef st ref n) (.num n)
              | .error msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "Assignment of a void expression"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .outOfFuel st => return .outOfFuel st
      | .runtimeError st msg => return .runtimeError st msg

def evalUnary (fuel : Nat) (st : RuntimeState) (op : UnOp) (arg : Expr) :
    IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match op with
      | .neg =>
          match ← evalExpr fuel' st arg with
          | .ok st (.num n) => return .ok st (.num (Num.neg n))
          | .ok st .void => return .runtimeError st "void expression with unary -"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .not =>
          match ← evalExpr fuel' st arg with
          | .ok st (.num n) => return .ok st (.num (boolNum n.isZero))
          | .ok st .void => return .runtimeError st "void expression with !"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .preIncr | .preDecr | .postIncr | .postDecr =>
          match lvalOfExpr? arg with
          | none => return .runtimeError st "increment/decrement operand is not an lvalue"
          | some lv =>
              match ← evalLValRef fuel' st lv with
              | .ok st ref =>
                  let (st, old, newValue) := bumpRef st ref (op == .preIncr || op == .postIncr)
                  match op with
                  | .preIncr | .preDecr => return .ok st (.num newValue)
                  | .postIncr | .postDecr => return .ok st (.num old)
                  | _ => return .ok st (.num newValue)
              | .outOfFuel st => return .outOfFuel st
              | .runtimeError st msg => return .runtimeError st msg

def evalBuiltin (fuel : Nat) (st : RuntimeState) (fn : Builtin) (arg : Option Expr) :
    IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match fn, arg with
      | .read, none =>
          let input := st.input.dropWhile fun c => c.isWhitespace
          let input ←
            if input.isEmpty then
              let line ← (← IO.getStdin).getLine
              pure line.toList
            else
              pure input
          let input := input.dropWhile fun c => c.isWhitespace
          let token := String.ofList (input.takeWhile fun c => !c.isWhitespace)
          let rest := input.dropWhile fun c => !c.isWhitespace
          let n := Num.ofInputString token st.ibase
          return .ok { st with input := rest } (.num n)
      | .random, none =>
          let r ← IO.rand 0 2147483647
          return .ok st (.num (Num.ofInt (Int.ofNat r)))
      | .length, some e =>
          match ← evalExpr fuel' st e with
          | .ok st (.num n) => return .ok st (.num (Num.ofInt (Int.ofNat n.length)))
          | .ok st .void => return .runtimeError st "void expression in length()"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .scale, some e =>
          match ← evalExpr fuel' st e with
          | .ok st (.num n) => return .ok st (.num (Num.ofInt (Int.ofNat n.scale)))
          | .ok st .void => return .runtimeError st "void expression in scale()"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .sqrt, some e =>
          match ← evalExpr fuel' st e with
          | .ok st (.num n) =>
              match Num.sqrt? n st.scale with
              | .ok r => return .ok st (.num r)
              | .error msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression in sqrt()"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | _, _ => return .runtimeError st "invalid builtin arity"

def evalArgValues (fuel : Nat) (st : RuntimeState) (args : List Arg) :
    IO (Result (List (Sum Num Name))) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match args with
      | [] => return .ok st []
      | arg :: rest =>
          let firstResult : Result (Sum Num Name) ←
            match arg with
            | .expr e =>
                match ← evalExpr fuel' st e with
                | .ok st (.num n) => pure (Result.ok st (Sum.inl n))
                | .ok st .void => pure (Result.runtimeError st "void argument")
                | .outOfFuel st => pure (Result.outOfFuel st)
                | .runtimeError st msg => pure (Result.runtimeError st msg)
            | .arrayRef name =>
                pure (Result.ok st (Sum.inr name))
          match firstResult with
          | .ok st v =>
              match ← evalArgValues fuel' st rest with
              | .ok st vs => return .ok st (v :: vs)
              | .outOfFuel st => return .outOfFuel st
              | .runtimeError st msg => return .runtimeError st msg
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def bindParams (st : RuntimeState) (params : List ParamDecl) (args : List (Sum Num Name)) :
    Except String RuntimeState := do
  if params.length != args.length then
    throw "Parameter number mismatch"
  else
    let mut st := st
    for pair in params.zip args do
      let (param, arg) := pair
      match param, arg with
      | .scalar name, .inl n =>
          match st.frames with
          | frame :: rest =>
              st := { st with frames :=
                { frame with scalars := assocSet frame.scalars name n } :: rest }
          | [] => throw "internal error: missing call frame"
      | .array name, .inr actual =>
          let (st1, srcId) := ensureArrayId st actual
          let (st2, dstId) := freshArray st1
          let copied := getArray st2 srcId
          st := setArray st2 dstId copied
          match st.frames with
          | frame :: rest =>
              st := { st with frames :=
                { frame with arrays := assocSet frame.arrays name dstId } :: rest }
          | [] => throw "internal error: missing call frame"
      | .refArray name, .inr actual | .varArray name, .inr actual =>
          let (st1, srcId) := ensureArrayId st actual
          st := st1
          match st.frames with
          | frame :: rest =>
              st := { st with frames :=
                { frame with arrays := assocSet frame.arrays name srcId } :: rest }
          | [] => throw "internal error: missing call frame"
      | .scalar name, .inr _ => throw s!"Parameter type mismatch, parameter {name}"
      | .array name, .inl _ | .refArray name, .inl _ | .varArray name, .inl _ =>
          throw s!"Parameter type mismatch, parameter {name}"
    return st

def evalCall (fuel : Nat) (st : RuntimeState) (name : Name) (args : List Arg) :
    IO (Result Value) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match lookupFunction st name with
      | none => return .runtimeError st s!"Function {name} not defined"
      | some defn =>
          match ← evalArgValues fuel' st args with
          | .ok st argValues =>
              let frame : Frame := { constBase := st.ibase }
              let stWithFrame := { st with frames := frame :: st.frames }
              match bindParams stWithFrame defn.params argValues with
              | .error msg => return .runtimeError stWithFrame msg
              | .ok st =>
                  let st := bindAutoDecls st (collectAutos defn.body)
                  match ← evalBody fuel' st defn.body with
                  | .ok st .normal =>
                      let value := if defn.void then Value.void else Value.num Num.zero
                      return .ok { st with frames := st.frames.drop 1 } value
                  | .ok st (.return v) =>
                      let value :=
                        match v, defn.void with
                        | .void, true => Value.void
                        | .void, false => Value.num Num.zero
                        | .num n, false => Value.num n
                        | .num _, true => Value.void
                      return .ok { st with frames := st.frames.drop 1 } value
                  | .ok st .break =>
                      return Result.runtimeError { st with frames := st.frames.drop 1 }
                        "Break outside a loop"
                  | .ok st .continue =>
                      return Result.runtimeError { st with frames := st.frames.drop 1 }
                        "Continue outside a loop"
                  | .ok st .stop => return .ok { st with frames := st.frames.drop 1 } .void
                  | .outOfFuel st => return .outOfFuel { st with frames := st.frames.drop 1 }
                  | .runtimeError st msg => return .runtimeError { st with frames := st.frames.drop 1 } msg
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def evalStmt (fuel : Nat) (st : RuntimeState) (stmt : Stmt) : IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match stmt with
      | .expr e =>
          match ← evalExpr fuel' st e with
          | .ok st (.num n) =>
              if isTopAssignment e then return .ok st .normal
              else return .ok (printNumLine st n) .normal
          | .ok st .void => return .ok st .normal
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .str s =>
          return .ok (appendOutput st (decodeBcString s)) .normal
      | .auto _ =>
          return .ok st .normal
      | .if cond thenBranch elseBranch =>
          match ← evalExpr fuel' st cond with
          | .ok st (.num n) =>
              if n.isZero then
                match elseBranch with
                | none => return .ok st .normal
                | some e => evalStmt fuel' st e
              else
                evalStmt fuel' st thenBranch
          | .ok st .void => return .runtimeError st "void expression in if"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .while cond body =>
          match ← evalExpr fuel' st cond with
          | .ok st (.num n) =>
              if n.isZero then
                return .ok st .normal
              else
                match ← evalStmt fuel' st body with
                | .ok st .normal | .ok st .continue => evalStmt fuel' st stmt
                | .ok st .break => return .ok st .normal
                | .ok st c => return .ok st c
                | .outOfFuel st => return .outOfFuel st
                | .runtimeError st msg => return .runtimeError st msg
          | .ok st .void => return .runtimeError st "void expression in while"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .for init cond update body =>
          match init with
          | some initExpr =>
              match ← evalExpr fuel' st initExpr with
              | .ok st _ => evalFor fuel' st cond update body
              | .outOfFuel st => return .outOfFuel st
              | .runtimeError st msg => return .runtimeError st msg
          | none => evalFor fuel' st cond update body
      | .break => return .ok st .break
      | .continue => return .ok st .continue
      | .return none => return .ok st (.return .void)
      | .return (some e) =>
          match ← evalExpr fuel' st e with
          | .ok st v => return .ok st (.return v)
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg
      | .quit | .halt => return .ok { st with halted := true } .stop
      | .print items =>
          evalPrintItems fuel' st items
      | .warranty =>
          return .ok (appendOutput st "GNU bc comes with ABSOLUTELY NO WARRANTY.\n") .normal
      | .limits =>
          let out :=
            s!"BC_BASE_MAX     = {bcBaseMax}\n" ++
            s!"BC_DIM_MAX      = {bcDimMax}\n" ++
            s!"BC_SCALE_MAX    = {bcScaleMax}\n"
          return .ok (appendOutput st out) .normal
      | .block body =>
          evalBody fuel' st body

def evalPrintItems (fuel : Nat) (st : RuntimeState) (items : List PrintItem) :
    IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match items with
      | [] => return .ok st .normal
      | item :: rest =>
          let itemResult : Result Control ←
            match item with
            | .str s => pure (Result.ok (appendOutput st (decodeBcString s)) .normal)
            | .expr e =>
                match ← evalExpr fuel' st e with
                | .ok st (.num n) => pure (Result.ok (printNumNoNewline st n) .normal)
                | .ok st .void => pure (Result.runtimeError st "void expression in print")
                | .outOfFuel st => pure (Result.outOfFuel st)
                | .runtimeError st msg => pure (Result.runtimeError st msg)
          match itemResult with
          | .ok st Control.normal => evalPrintItems fuel' st rest
          | .ok st c => return .ok st c
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def evalFor (fuel : Nat) (st : RuntimeState) (cond update : Option Expr) (body : Stmt) :
    IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      let condExpr := cond.getD (.num "1")
      match ← evalExpr fuel' st condExpr with
      | .ok st (.num n) =>
          if n.isZero then
            return .ok st .normal
          else
            match ← evalStmt fuel' st body with
            | .ok st .normal | .ok st .continue =>
                match update with
                | none => evalFor fuel' st cond update body
                | some upd =>
                    match ← evalExpr fuel' st upd with
                    | .ok st _ => evalFor fuel' st cond update body
                    | .outOfFuel st => return .outOfFuel st
                    | .runtimeError st msg => return .runtimeError st msg
            | .ok st .break => return .ok st .normal
            | .ok st c => return .ok st c
            | .outOfFuel st => return .outOfFuel st
            | .runtimeError st msg => return .runtimeError st msg
      | .ok st .void => return .runtimeError st "void expression in for condition"
      | .outOfFuel st => return .outOfFuel st
      | .runtimeError st msg => return .runtimeError st msg

def evalStmts (fuel : Nat) (st : RuntimeState) (stmts : List Stmt) :
    IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match stmts with
      | [] => return .ok st .normal
      | stmt :: rest =>
          match ← evalStmt fuel' st stmt with
          | .ok st .normal => evalStmts fuel' st rest
          | .ok st c => return .ok st c
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

def evalBody (fuel : Nat) (st : RuntimeState) (body : List BodyItem) :
    IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match body with
      | [] => return .ok st .normal
      | .newline :: rest => evalBody fuel' st rest
      | .stmts ss :: rest =>
          match ← evalStmts fuel' st ss with
          | .ok st .normal => evalBody fuel' st rest
          | .ok st c => return .ok st c
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

end

def evalTopItem (fuel : Nat) (st : RuntimeState) : TopItem → IO (Result Control)
  | .funDef defn => pure (.ok (setFunction st defn) .normal)
  | .stmts ss => evalStmts fuel st ss

def evalProgramItems (fuel : Nat) (st : RuntimeState) (items : Program) :
    IO (Result Control) := do
  match fuel with
  | 0 => return .outOfFuel st
  | fuel' + 1 =>
      match items with
      | [] => return .ok st .normal
      | item :: rest =>
          match ← evalTopItem fuel' st item with
          | .ok st .normal =>
              if st.halted then return .ok st .stop else evalProgramItems fuel' st rest
          | .ok st .stop => return .ok st .stop
          | .ok st .break => return .runtimeError st "Break outside a loop"
          | .ok st .continue => return .runtimeError st "Continue outside a loop"
          | .ok st (.return _) => return .runtimeError st "Return outside of a function"
          | .outOfFuel st => return .outOfFuel st
          | .runtimeError st msg => return .runtimeError st msg

inductive RunResult where
  | success (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

def runProgramWithState (fuel : Nat) (st : RuntimeState) (program : Program) : IO RunResult := do
  match ← evalProgramItems fuel st program with
  | .ok st _ => return .success st
  | .outOfFuel st => return .outOfFuel st
  | .runtimeError st msg => return .runtimeError st msg

def runProgram (fuel : Nat) (input : String) (program : Program) : IO RunResult :=
  runProgramWithState fuel (initialState input) program

end Bc
