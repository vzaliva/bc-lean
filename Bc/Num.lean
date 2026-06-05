/-
  Numeric representation and metatheory for bc values.

  bc numbers are intentionally non-canonical: the presentation scale is
  observable through `scale`, `length`, printing, and truncating arithmetic.
  Structural equality of `coeff` and `scale` is therefore distinct from numeric
  equivalence.  This module exposes the executable representation together with
  a rational denotation for proofs.
-/

namespace Bc

structure Num where
  coeff : Int
  scale : Nat
  deriving Repr, DecidableEq

namespace Num

def zero : Num := { coeff := 0, scale := 0 }
def one : Num := { coeff := 1, scale := 0 }
def onePointZero : Num := { coeff := 10, scale := 1 }

def pow10Nat (n : Nat) : Nat :=
  10 ^ n

def pow10Int (n : Nat) : Int :=
  Int.ofNat (pow10Nat n)

def pow10Rat (n : Nat) : Rat :=
  (10 : Rat) ^ n

def pow10 : Nat → Int :=
  pow10Int

theorem pow10Rat_ne_zero (n : Nat) : pow10Rat n ≠ 0 := by
  unfold pow10Rat
  induction n with
  | zero => decide
  | succ n ih =>
      intro h
      have hm : (10 : Rat) ^ n * 10 = 0 := by
        simpa [Rat.pow_succ] using h
      have hz := Rat.mul_eq_zero.mp hm
      cases hz with
      | inl h0 => exact ih h0
      | inr h0 => exact (by decide : (10 : Rat) ≠ 0) h0

/-- Canonical mathematical value denoted by a bc number presentation. -/
def value (n : Num) : Rat :=
  (n.coeff : Rat) / pow10Rat n.scale

/-- Numeric equivalence: same rational value, ignoring presentation scale. -/
def equiv (a b : Num) : Prop :=
  a.value = b.value

instance equivSetoid : Setoid Num where
  r := equiv
  iseqv := {
    refl := by intro _; rfl
    symm := by intro _ _ h; exact h.symm
    trans := by intro _ _ _ hab hbc; exact hab.trans hbc
  }

theorem eq_implies_equiv {a b : Num} (h : a = b) : equiv a b := by
  cases h
  rfl

theorem one_ne_onePointZero : one ≠ onePointZero := by
  intro h
  cases h

theorem one_equiv_onePointZero : equiv one onePointZero := by
  unfold equiv value one onePointZero pow10Rat
  native_decide

def isZero (n : Num) : Bool :=
  n.coeff == 0

theorem isZero_eq_true_iff (n : Num) : n.isZero = true ↔ n.coeff = 0 := by
  unfold isZero
  exact beq_iff_eq

theorem value_eq_zero_iff_coeff_eq_zero (n : Num) : n.value = 0 ↔ n.coeff = 0 := by
  unfold value
  have hden : pow10Rat n.scale ≠ 0 := pow10Rat_ne_zero n.scale
  constructor
  · intro h
    have _hmul := congrArg (fun x => x * pow10Rat n.scale) h
    have hz : (n.coeff : Rat) = 0 := by
      grind
    exact Rat.intCast_inj.mp hz
  · intro h
    rw [h]
    grind

theorem isZero_eq_true_iff_value_eq_zero (n : Num) : n.isZero = true ↔ n.value = 0 := by
  rw [isZero_eq_true_iff, value_eq_zero_iff_coeff_eq_zero]

def alignCoeff (n : Num) (s : Nat) : Int :=
  n.coeff * pow10 (s - n.scale)

def commonScale (a b : Num) : Nat :=
  max a.scale b.scale

def alignedEquiv (a b : Num) : Prop :=
  alignCoeff a (commonScale a b) = alignCoeff b (commonScale a b)

inductive Rel where
  | eq
  | ne
  | le
  | ge
  | lt
  | gt
  deriving Repr, DecidableEq

def applyRel (op : Rel) (a b : Num) : Bool :=
  let x := alignCoeff a (commonScale a b)
  let y := alignCoeff b (commonScale a b)
  match op with
  | .eq => x == y
  | .ne => x != y
  | .le => x <= y
  | .ge => x >= y
  | .lt => x < y
  | .gt => x > y

theorem applyRel_eq_iff_alignedEquiv (a b : Num) :
    applyRel .eq a b = true ↔ alignedEquiv a b := by
  unfold applyRel alignedEquiv
  exact beq_iff_eq

theorem applyRel_ne_iff_not_alignedEquiv (a b : Num) :
    applyRel .ne a b = true ↔ ¬ alignedEquiv a b := by
  unfold applyRel alignedEquiv
  simp [bne]

theorem applyRel_le_iff_alignedLe (a b : Num) :
    applyRel .le a b = true ↔
      alignCoeff a (commonScale a b) ≤ alignCoeff b (commonScale a b) := by
  unfold applyRel
  simp

theorem applyRel_ge_iff_alignedGe (a b : Num) :
    applyRel .ge a b = true ↔
      alignCoeff a (commonScale a b) ≥ alignCoeff b (commonScale a b) := by
  unfold applyRel
  simp

theorem applyRel_lt_iff_alignedLt (a b : Num) :
    applyRel .lt a b = true ↔
      alignCoeff a (commonScale a b) < alignCoeff b (commonScale a b) := by
  unfold applyRel
  simp

theorem applyRel_gt_iff_alignedGt (a b : Num) :
    applyRel .gt a b = true ↔
      alignCoeff a (commonScale a b) > alignCoeff b (commonScale a b) := by
  unfold applyRel
  simp

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
  let s := commonScale a b
  { coeff := alignCoeff a s + alignCoeff b s, scale := s }

def neg (a : Num) : Num :=
  { a with coeff := -a.coeff }

def sub (a b : Num) : Num :=
  add a (neg b)

theorem value_alignCoeff (n : Num) {s : Nat} (h : n.scale ≤ s) :
    ((alignCoeff n s : Rat) / pow10Rat s) = value n := by
  unfold alignCoeff value pow10 pow10Int pow10Nat pow10Rat
  have hs : s - n.scale + n.scale = s := Nat.sub_add_cancel h
  rw [← hs]
  have hleft : (10 : Rat) ^ (s - n.scale) ≠ 0 := by
    exact pow10Rat_ne_zero (s - n.scale)
  have hden : (10 : Rat) ^ n.scale ≠ 0 := by
    exact pow10Rat_ne_zero n.scale
  have hmul : (10 : Rat) ^ (s - n.scale + n.scale) =
      (10 : Rat) ^ (s - n.scale) * (10 : Rat) ^ n.scale := by
    grind
  rw [hmul]
  grind

theorem alignedEquiv_iff_equiv (a b : Num) : alignedEquiv a b ↔ equiv a b := by
  unfold alignedEquiv equiv
  let s := commonScale a b
  have ha : a.scale ≤ s := by
    unfold s commonScale
    exact Nat.le_max_left a.scale b.scale
  have hb : b.scale ≤ s := by
    unfold s commonScale
    exact Nat.le_max_right a.scale b.scale
  constructor
  · intro h
    have hrat : (alignCoeff a s : Rat) / pow10Rat s =
        (alignCoeff b s : Rat) / pow10Rat s := by
      rw [h]
    rw [← value_alignCoeff a ha, ← value_alignCoeff b hb]
    exact hrat
  · intro h
    have hrat : (alignCoeff a s : Rat) / pow10Rat s =
        (alignCoeff b s : Rat) / pow10Rat s := by
      rw [value_alignCoeff a ha, value_alignCoeff b hb]
      exact h
    have _hmul := congrArg (fun x => x * pow10Rat s) hrat
    have hcast : (alignCoeff a s : Rat) = (alignCoeff b s : Rat) := by
      have hden : pow10Rat s ≠ 0 := pow10Rat_ne_zero s
      grind
    exact Rat.intCast_inj.mp hcast

theorem applyRel_eq_iff_equiv (a b : Num) : applyRel .eq a b = true ↔ equiv a b := by
  rw [applyRel_eq_iff_alignedEquiv, alignedEquiv_iff_equiv]

theorem value_neg (a : Num) : value (neg a) = - value a := by
  unfold value neg pow10Rat
  grind

private theorem rat_add_div_same (x y d : Rat) : (x + y) / d = x / d + y / d := by
  grind

/-- Addition preserves the rational denotation even when presentations differ. -/
theorem value_add (a b : Num) :
    value (add a b) = value a + value b := by
  unfold add
  let s := commonScale a b
  have ha : a.scale ≤ s := by
    unfold s commonScale
    exact Nat.le_max_left a.scale b.scale
  have hb : b.scale ≤ s := by
    unfold s commonScale
    exact Nat.le_max_right a.scale b.scale
  unfold value
  simp only [Rat.intCast_add]
  rw [rat_add_div_same]
  rw [value_alignCoeff a ha, value_alignCoeff b hb]
  unfold value
  rfl

theorem value_sub (a b : Num) :
    value (sub a b) = value a - value b := by
  unfold sub
  rw [value_add, value_neg]
  grind

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

end Bc
