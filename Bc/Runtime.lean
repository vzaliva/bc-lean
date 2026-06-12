/-
  Shared runtime state, numeric operations, and helper functions for the
  POSIX bc subset.

  The big-step and small-step modules own their expression and statement
  evaluators separately because bc expressions can update RuntimeState and call
  functions.
-/

import Bc.Num
import Bc.Syntax

namespace Bc

private def bcDimMax : Nat := 16777215
private def bcInputBaseMax : Nat := 16
private def bcBaseMax : Nat := 2147483647
private def bcScaleMax : Nat := 2147483647

abbrev BcArray := List (Nat × Num)
abbrev ArrayId := Nat

inductive LValueTarget where
  | scalar (name : Name)
  | special (var : SpecialVar)
  | arrayElem (id : ArrayId) (index : Nat)
  deriving Repr, BEq, DecidableEq

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
  output : String := ""
  outCol : Nat := 0
  stopped : Bool := false
  deriving Repr

inductive Result (α : Type) where
  | ok (state : RuntimeState) (value : α)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive RunResult where
  | success (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

inductive Control where
  | normal
  | break
  | return (value : Option Num)
  | quit
  deriving Repr

def initialState : RuntimeState := {}

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

def setFunction (st : RuntimeState) (defn : FunDef) : RuntimeState :=
  { st with functions := assocSet st.functions defn.name defn }

def lookupFunction (st : RuntimeState) (name : Name) : Option FunDef :=
  assocGet? st.functions name

def currentConstBase (st : RuntimeState) : Nat :=
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

def lookupScalar (st : RuntimeState) (name : Name) : Num :=
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

def ensureArrayId (st : RuntimeState) (name : Name) : RuntimeState × ArrayId :=
  match lookupArrayInFrames st.frames name with
  | some id => (st, id)
  | none => ensureGlobalArray st name

def getArray (st : RuntimeState) (id : ArrayId) : BcArray :=
  match assocGet? st.arrayStore id with
  | some a => a
  | none => []

def setArray (st : RuntimeState) (id : ArrayId) (a : BcArray) : RuntimeState :=
  { st with arrayStore := assocSet st.arrayStore id a }

def getArrayElem (st : RuntimeState) (id : ArrayId) (idx : Nat) : Num :=
  match assocGet? (getArray st id) idx with
  | some n => n
  | none => Num.zero

private def setArrayElem (st : RuntimeState) (id : ArrayId) (idx : Nat) (value : Num) :
    RuntimeState :=
  setArray st id (assocSet (getArray st id) idx value)

def indexOfNum? (n : Num) : Except String Nat := do
  let idx := n.intPart
  if idx < 0 then
    throw "Array subscript out of bounds"
  else
    let natIdx := idx.natAbs
    if natIdx > bcDimMax || (natIdx == 0 && !n.isZero) then
      throw "Array subscript out of bounds"
    else
      return natIdx

def specialValue (st : RuntimeState) : SpecialVar → Num
  | .ibase => Num.ofInt (Int.ofNat st.ibase)
  | .obase => Num.ofInt (Int.ofNat st.obase)
  | .scale => Num.ofInt (Int.ofNat st.scale)

private def assignSpecial (st : RuntimeState) (v : SpecialVar) (n : Num) : RuntimeState :=
  match v with
  | .ibase =>
      let raw := n.intPart
      let ibase :=
        if raw < 2 then 2
        else if raw.natAbs > bcInputBaseMax then bcInputBaseMax
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

def appendOutputChar (st : RuntimeState) (c : Char) : RuntimeState :=
  if c == '\n' then
    { st with output := st.output ++ "\n", outCol := 0 }
  else
    let nextCol := st.outCol + 1
    if nextCol == 69 then
      { st with output := st.output ++ "\\\n" ++ String.ofList [c], outCol := 1 }
    else
      { st with output := st.output ++ String.ofList [c], outCol := nextCol }

def appendOutput (st : RuntimeState) (s : String) : RuntimeState :=
  s.toList.foldl appendOutputChar st

def printNumNoNewline (st : RuntimeState) (n : Num) : RuntimeState :=
  let s := Num.toBaseString n st.obase
  appendOutput st s

def printNumLine (st : RuntimeState) (n : Num) : RuntimeState :=
  appendOutput (printNumNoNewline st n) "\n"

def decodeStringChars : List Char → List Char
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

def decodeBcString (s : String) : String :=
  String.ofList (decodeStringChars s.toList)

def applyRel (op : RelOp) (a b : Num) : Bool :=
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

def boolNum (b : Bool) : Num :=
  if b then Num.one else Num.zero

/-- Apply a binary arithmetic operator to two evaluated numbers. Shared by both
    semantics so the numeric behaviour cannot drift between them. -/
def applyBin? (op : BinOp) (a b : Num) (scale : Nat) : Except String Num :=
  match op with
  | .add => .ok (Num.add a b)
  | .sub => .ok (Num.sub a b)
  | .mul => .ok (Num.mulWithScale a b scale)
  | .div => Num.div? a b scale
  | .mod => Num.modulo? a b scale
  | .pow => Num.pow? a b scale

/-- Apply a (possibly compound) assignment operator given the old and rhs values. -/
def applyAssign? (op : AssignOp) (old rhs : Num) (scale : Nat) : Except String Num :=
  match op with
  | .assign => .ok rhs
  | .addAssign => .ok (Num.add old rhs)
  | .subAssign => .ok (Num.sub old rhs)
  | .mulAssign => .ok (Num.mulWithScale old rhs scale)
  | .divAssign => Num.div? old rhs scale
  | .modAssign => Num.modulo? old rhs scale
  | .powAssign => Num.pow? old rhs scale

/-- Apply a unary builtin to an evaluated argument value. -/
def applyBuiltin? (fn : Builtin) (value : Num) (scale : Nat) : Except String Num :=
  match fn with
  | .length => .ok (Num.ofInt (Int.ofNat value.length))
  | .scale => .ok (Num.ofInt (Int.ofNat value.scale))
  | .sqrt => Num.sqrt? value scale

/- Source-level `quit` detection. GNU bc acts on `quit` when it is *read*, so a
   top-level item containing `quit` anywhere (even in an unreachable branch) ends
   the program before that item runs. Shared by both semantics. -/
mutual
def Stmt.containsQuit : Stmt → Bool
  | .expr _ => false
  | .str _ => false
  | .auto _ => false
  | .if _ thenBranch => Stmt.containsQuit thenBranch
  | .while _ body => Stmt.containsQuit body
  | .for _ _ _ body => Stmt.containsQuit body
  | .break => false
  | .return _ => false
  | .quit => true
  | .block body => bodyContainsQuit body

def stmtsContainQuit : List Stmt → Bool
  | [] => false
  | stmt :: rest => Stmt.containsQuit stmt || stmtsContainQuit rest

def bodyItemContainsQuit : BodyItem → Bool
  | .stmts ss => stmtsContainQuit ss
  | .newline => false

def bodyContainsQuit : List BodyItem → Bool
  | [] => false
  | item :: rest => bodyItemContainsQuit item || bodyContainsQuit rest
end

def TopItem.containsQuit : TopItem → Bool
  | .funDef defn => bodyContainsQuit defn.body
  | .stmts ss => stmtsContainQuit ss

def lvalOfExpr? : Expr → Option LVal
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

def collectAutos (body : List BodyItem) : List ParamDecl :=
  body.foldr (fun item acc => collectAutosFromBodyItem item ++ acc) []

private def bindAutoDecl (st : RuntimeState) (decl : ParamDecl) : RuntimeState :=
  match st.frames with
  | [] => st
  | frame :: rest =>
      match decl with
      | .scalar n =>
          { st with frames :=
              { frame with scalars := assocSet frame.scalars n Num.zero } :: rest }
      | .array n =>
          let (st, id) := freshArray st
          match st.frames with
          | frame :: rest =>
              { st with frames := { frame with arrays := assocSet frame.arrays n id } :: rest }
          | [] => st

def bindAutoDecls (st : RuntimeState) (decls : List ParamDecl) : RuntimeState :=
  decls.foldl bindAutoDecl st

def isTopAssignment : Expr → Bool
  | .assign _ _ _ => true
  | _ => false

def readLValueTarget (st : RuntimeState) (target : LValueTarget) : Num :=
  match target with
  | .scalar name => lookupScalar st name
  | .special v => specialValue st v
  | .arrayElem id idx => getArrayElem st id idx

def writeLValueTarget (st : RuntimeState) (target : LValueTarget) (value : Num) : RuntimeState :=
  match target with
  | .scalar name => setScalar st name value
  | .special v => assignSpecial st v value
  | .arrayElem id idx => setArrayElem st id idx value

def bumpLValueTarget (st : RuntimeState) (target : LValueTarget) (up : Bool) :
    RuntimeState × Num × Num :=
  let old := readLValueTarget st target
  match target with
  | .special .ibase =>
      let newBase := if up then (if st.ibase < bcInputBaseMax then st.ibase + 1 else st.ibase)
        else (if st.ibase > 2 then st.ibase - 1 else st.ibase)
      let newValue := Num.ofInt (Int.ofNat newBase)
      ({ st with ibase := newBase }, old, newValue)
  | .special .obase =>
      let newBase := if up then (if st.obase < bcBaseMax then st.obase + 1 else st.obase)
        else (if st.obase > 2 then st.obase - 1 else st.obase)
      let newValue := Num.ofInt (Int.ofNat newBase)
      ({ st with obase := newBase }, old, newValue)
  | .special .scale =>
      let newScale := if up then (if st.scale < bcScaleMax then st.scale + 1 else st.scale)
        else (if st.scale > 0 then st.scale - 1 else st.scale)
      let newValue := Num.ofInt (Int.ofNat newScale)
      ({ st with scale := newScale }, old, newValue)
  | _ =>
      let newValue := if up then Num.add old Num.one else Num.sub old Num.one
      (writeLValueTarget st target newValue, old, newValue)

private def bindParam (st : RuntimeState) (param : ParamDecl) (arg : Sum Num Name) :
    Except String RuntimeState :=
  match param, arg with
  | .scalar name, .inl n =>
      match st.frames with
      | frame :: rest =>
          .ok { st with frames :=
            { frame with scalars := assocSet frame.scalars name n } :: rest }
      | [] => .error "internal error: missing call frame"
  | .array name, .inr actual =>
      let (st1, srcId) := ensureArrayId st actual
      let (st2, dstId) := freshArray st1
      let copied := getArray st2 srcId
      let st := setArray st2 dstId copied
      match st.frames with
      | frame :: rest =>
          .ok { st with frames :=
            { frame with arrays := assocSet frame.arrays name dstId } :: rest }
      | [] => .error "internal error: missing call frame"
  | .scalar name, .inr _ => .error s!"Parameter type mismatch, parameter {name}"
  | .array name, .inl _ => .error s!"Parameter type mismatch, parameter {name}"

private def bindParamsLoop (st : RuntimeState)
    (pairs : List (ParamDecl × Sum Num Name)) : Except String RuntimeState :=
  match pairs with
  | [] => .ok st
  | (param, arg) :: rest => do
      let st ← bindParam st param arg
      bindParamsLoop st rest

def bindParams (st : RuntimeState) (params : List ParamDecl) (args : List (Sum Num Name)) :
    Except String RuntimeState :=
  if params.length != args.length then
    .error "Parameter number mismatch"
  else
    bindParamsLoop st (params.zip args)

/-! ### Runtime-state preservation facts used by semantics equivalence proofs -/

private theorem lookupFunction_setArray (st : RuntimeState) (id : ArrayId) (a : BcArray)
    (name : Name) :
    lookupFunction (setArray st id a) name = lookupFunction st name := by
  rfl

private theorem lookupFunction_freshArray (st : RuntimeState) (name : Name) :
    lookupFunction (freshArray st).1 name = lookupFunction st name := by
  rfl

theorem lookupFunction_ensureArrayId (st : RuntimeState) (arrayName name : Name) :
    lookupFunction (ensureArrayId st arrayName).1 name = lookupFunction st name := by
  simp [ensureArrayId, lookupFunction]
  split <;> simp [ensureGlobalArray, freshArray]
  split <;> simp

theorem lookupFunction_writeLValueTarget (st : RuntimeState) (target : LValueTarget)
    (value : Num) (name : Name) :
    lookupFunction (writeLValueTarget st target value) name = lookupFunction st name := by
  cases target with
  | scalar n =>
      simp [writeLValueTarget, setScalar, lookupFunction]
      cases updateScalarInFrames st.frames n value <;> rfl
  | special v =>
      cases v <;> simp [writeLValueTarget, assignSpecial, lookupFunction]
  | arrayElem id idx =>
      simp [writeLValueTarget, setArrayElem, setArray, lookupFunction]

theorem lookupFunction_bumpLValueTarget (st : RuntimeState) (target : LValueTarget)
    (up : Bool) (name : Name) :
    lookupFunction (bumpLValueTarget st target up).1 name = lookupFunction st name := by
  cases target with
  | scalar n => simp [bumpLValueTarget, lookupFunction_writeLValueTarget]
  | special v => cases v <;> simp [bumpLValueTarget, lookupFunction]
  | arrayElem id idx => simp [bumpLValueTarget, lookupFunction_writeLValueTarget]

private theorem lookupFunction_appendOutputChar (st : RuntimeState) (c : Char) (name : Name) :
    lookupFunction (appendOutputChar st c) name = lookupFunction st name := by
  unfold appendOutputChar lookupFunction
  split <;> simp
  split <;> simp

private theorem lookupFunction_foldl_appendOutputChar (chars : List Char)
    (st : RuntimeState) (name : Name) :
    lookupFunction (chars.foldl appendOutputChar st) name = lookupFunction st name := by
  induction chars generalizing st with
  | nil => rfl
  | cons c rest ih => simp [List.foldl, ih, lookupFunction_appendOutputChar]

theorem lookupFunction_appendOutput (st : RuntimeState) (s : String) (name : Name) :
    lookupFunction (appendOutput st s) name = lookupFunction st name := by
  simp [appendOutput, lookupFunction_foldl_appendOutputChar]

theorem lookupFunction_printNumLine (st : RuntimeState) (n : Num) (name : Name) :
    lookupFunction (printNumLine st n) name = lookupFunction st name := by
  simp [printNumLine, printNumNoNewline, lookupFunction_appendOutput]

theorem stopped_setFunction (st : RuntimeState) (defn : FunDef) :
    (setFunction st defn).stopped = st.stopped := by
  rfl

private theorem stopped_setArray (st : RuntimeState) (id : ArrayId) (a : BcArray) :
    (setArray st id a).stopped = st.stopped := by
  rfl

private theorem stopped_freshArray (st : RuntimeState) :
    (freshArray st).1.stopped = st.stopped := by
  rfl

theorem stopped_ensureArrayId (st : RuntimeState) (arrayName : Name) :
    (ensureArrayId st arrayName).1.stopped = st.stopped := by
  simp [ensureArrayId]
  split <;> simp [ensureGlobalArray, freshArray]
  split <;> simp

theorem stopped_writeLValueTarget (st : RuntimeState) (target : LValueTarget)
    (value : Num) :
    (writeLValueTarget st target value).stopped = st.stopped := by
  cases target with
  | scalar n =>
      simp [writeLValueTarget, setScalar]
      cases updateScalarInFrames st.frames n value <;> rfl
  | special v =>
      cases v <;> simp [writeLValueTarget, assignSpecial]
  | arrayElem id idx =>
      simp [writeLValueTarget, setArrayElem, setArray]

theorem stopped_bumpLValueTarget (st : RuntimeState) (target : LValueTarget)
    (up : Bool) :
    (bumpLValueTarget st target up).1.stopped = st.stopped := by
  cases target with
  | scalar n => simp [bumpLValueTarget, stopped_writeLValueTarget]
  | special v => cases v <;> simp [bumpLValueTarget]
  | arrayElem id idx => simp [bumpLValueTarget, stopped_writeLValueTarget]

private theorem stopped_appendOutputChar (st : RuntimeState) (c : Char) :
    (appendOutputChar st c).stopped = st.stopped := by
  unfold appendOutputChar
  split <;> simp
  split <;> simp

private theorem stopped_foldl_appendOutputChar (chars : List Char) (st : RuntimeState) :
    (chars.foldl appendOutputChar st).stopped = st.stopped := by
  induction chars generalizing st with
  | nil => rfl
  | cons c rest ih => simp [List.foldl, ih, stopped_appendOutputChar]

theorem stopped_appendOutput (st : RuntimeState) (s : String) :
    (appendOutput st s).stopped = st.stopped := by
  simp [appendOutput, stopped_foldl_appendOutputChar]

theorem stopped_printNumLine (st : RuntimeState) (n : Num) :
    (printNumLine st n).stopped = st.stopped := by
  simp [printNumLine, printNumNoNewline, stopped_appendOutput]

private theorem stopped_bindAutoDecl (st : RuntimeState) (decl : ParamDecl) :
    (bindAutoDecl st decl).stopped = st.stopped := by
  unfold bindAutoDecl
  cases hframes : st.frames with
  | nil =>
      cases decl <;> simp
  | cons frame rest =>
      cases decl <;> simp [hframes, freshArray]

theorem stopped_bindAutoDecls (decls : List ParamDecl) (st : RuntimeState) :
    (bindAutoDecls st decls).stopped = st.stopped := by
  unfold bindAutoDecls
  induction decls generalizing st with
  | nil => rfl
  | cons decl rest ih =>
      simp [List.foldl]
      exact (ih (bindAutoDecl st decl)).trans (stopped_bindAutoDecl st decl)

private theorem bindParam_lookupFunction {st st' : RuntimeState}
    {param : ParamDecl} {arg : Sum Num Name} {name : Name}
    (h : bindParam st param arg = .ok st') :
    lookupFunction st' name = lookupFunction st name := by
  cases param with
  | scalar paramName =>
      cases arg with
      | inl n =>
          cases hframes : st.frames with
          | nil => simp [bindParam, hframes] at h
          | cons frame frames =>
              simp [bindParam, hframes] at h
              cases h
              rfl
      | inr actual =>
          simp [bindParam] at h
  | array paramName =>
      cases arg with
      | inl n =>
          simp [bindParam] at h
      | inr actual =>
          let arr := ensureArrayId st actual
          let fresh := freshArray arr.1
          let stBound :=
            setArray fresh.1 fresh.2 (getArray fresh.1 arr.2)
          change
            (match stBound.frames with
            | frame :: rest =>
                Except.ok
                  { stBound with frames :=
                    { frame with arrays := assocSet frame.arrays paramName fresh.2 } :: rest }
            | [] => Except.error "internal error: missing call frame") = .ok st' at h
          cases hframes : stBound.frames with
          | nil => simp [hframes] at h
          | cons frame frames =>
              simp [hframes] at h
              cases h
              change lookupFunction stBound name = lookupFunction st name
              simp [stBound, arr, fresh, lookupFunction_ensureArrayId, lookupFunction_setArray,
                lookupFunction_freshArray]

private theorem bindParamsLoop_lookupFunction {pairs : List (ParamDecl × Sum Num Name)}
    {st st' : RuntimeState} {name : Name}
    (h : bindParamsLoop st pairs = .ok st') :
    lookupFunction st' name = lookupFunction st name := by
  induction pairs generalizing st with
  | nil =>
      simp [bindParamsLoop] at h
      cases h
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨param, arg⟩
      cases hparam : bindParam st param arg with
      | error msg =>
          simp [bindParamsLoop, hparam] at h
          cases h
      | ok st₁ =>
          have htail : bindParamsLoop st₁ rest = .ok st' := by
            simpa [bindParamsLoop, hparam] using h
          have hih := ih htail
          have hhead := bindParam_lookupFunction (name := name) hparam
          exact hih.trans hhead

theorem bindParams_lookupFunction {st st' : RuntimeState}
    {params : List ParamDecl} {args : List (Sum Num Name)} {name : Name}
    (h : bindParams st params args = .ok st') :
    lookupFunction st' name = lookupFunction st name := by
  unfold bindParams at h
  by_cases hlen : params.length = args.length
  · simp [hlen] at h
    exact bindParamsLoop_lookupFunction h
  · simp [hlen] at h

private theorem bindParam_stopped {st st' : RuntimeState}
    {param : ParamDecl} {arg : Sum Num Name}
    (h : bindParam st param arg = .ok st') :
    st'.stopped = st.stopped := by
  cases param with
  | scalar paramName =>
      cases arg with
      | inl n =>
          cases hframes : st.frames with
          | nil => simp [bindParam, hframes] at h
          | cons frame frames =>
              simp [bindParam, hframes] at h
              cases h
              rfl
      | inr actual =>
          simp [bindParam] at h
  | array paramName =>
      cases arg with
      | inl n =>
          simp [bindParam] at h
      | inr actual =>
          let arr := ensureArrayId st actual
          let fresh := freshArray arr.1
          let stBound :=
            setArray fresh.1 fresh.2 (getArray fresh.1 arr.2)
          change
            (match stBound.frames with
            | frame :: rest =>
                Except.ok
                  { stBound with frames :=
                    { frame with arrays := assocSet frame.arrays paramName fresh.2 } :: rest }
            | [] => Except.error "internal error: missing call frame") = .ok st' at h
          cases hframes : stBound.frames with
          | nil => simp [hframes] at h
          | cons frame frames =>
              simp [hframes] at h
              cases h
              change stBound.stopped = st.stopped
              calc
                stBound.stopped = fresh.1.stopped := by
                  simp [stBound, stopped_setArray]
                _ = arr.1.stopped := stopped_freshArray arr.1
                _ = st.stopped := stopped_ensureArrayId st actual

private theorem bindParamsLoop_stopped {pairs : List (ParamDecl × Sum Num Name)}
    {st st' : RuntimeState}
    (h : bindParamsLoop st pairs = .ok st') :
    st'.stopped = st.stopped := by
  induction pairs generalizing st with
  | nil =>
      simp [bindParamsLoop] at h
      cases h
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨param, arg⟩
      cases hparam : bindParam st param arg with
      | error msg =>
          simp [bindParamsLoop, hparam] at h
          cases h
      | ok st₁ =>
          have htail : bindParamsLoop st₁ rest = .ok st' := by
            simpa [bindParamsLoop, hparam] using h
          exact (ih htail).trans (bindParam_stopped hparam)

theorem stopped_bindParams {st st' : RuntimeState}
    {params : List ParamDecl} {args : List (Sum Num Name)}
    (h : bindParams st params args = .ok st') :
    st'.stopped = st.stopped := by
  unfold bindParams at h
  by_cases hlen : params.length = args.length
  · simp [hlen] at h
    exact bindParamsLoop_stopped h
  · simp [hlen] at h

private theorem lookupFunction_bindAutoDecl (st : RuntimeState) (decl : ParamDecl) (name : Name) :
    lookupFunction (bindAutoDecl st decl) name = lookupFunction st name := by
  unfold bindAutoDecl
  cases decl with
  | scalar n =>
      cases hframes : st.frames <;> simp [lookupFunction]
  | array n =>
      cases hframes : st.frames <;> simp [hframes, freshArray, lookupFunction]

theorem lookupFunction_bindAutoDecls (st : RuntimeState) (decls : List ParamDecl)
    (name : Name) :
    lookupFunction (bindAutoDecls st decls) name = lookupFunction st name := by
  unfold bindAutoDecls
  induction decls generalizing st with
  | nil => rfl
  | cons decl rest ih =>
      simp [List.foldl]
      rw [ih, lookupFunction_bindAutoDecl]

end Bc
