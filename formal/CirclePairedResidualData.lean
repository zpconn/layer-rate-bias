module

public import CirclePairedData
public meta import CirclePairedData
public meta import Lean
import Lean.Elab.BuiltinTerm

/-! Exact checks on the reported residuals, scaled continuation allowances,
and observation and theorem clocks of the primary paired numerical runs. -/
@[expose] public section
namespace CirclePairedResidualData

/-- Numeric fields are exact rationals parsed from the stored CSV decimals. -/
structure Row where
  n : Nat
  step : Rat
  observedTime : Rat
  theoremTime : Nat
  rmsSlow : Rat
  rmsFast : Rat
  tailSlow : Rat
  tailFast : Rat
  deriving Repr, DecidableEq

/-- Read a signed integer exponent, including an explicit leading plus sign. -/
private meta def exponent (cs : List Char) : Option Int := do
  match cs with
  | '-' :: tail => return -(Int.ofNat (← CirclePairedData.digits tail))
  | '+' :: tail => return Int.ofNat (← CirclePairedData.digits tail)
  | _ => return Int.ofNat (← CirclePairedData.digits cs)

/-- Combine the signed integer mantissa, the decimal denominator and the
optional base-ten exponent using rational arithmetic throughout. -/
private meta def scientific (cs : List Char) : Option Rat := do
  let (mantissa, e) ← match (cs.map Char.toLower).splitOn 'e' with
    | [a] => some (a,0)
    | [a,b] => (exponent b).map fun e => (a,e)
    | _ => none
  let (negative, unsigned) := match mantissa with
    | '-' :: rest => (true,rest)
    | '+' :: rest => (false,rest)
    | _ => (false,mantissa)
  let (digits,places) ← match unsigned.splitOn '.' with
    | [a] => (CirclePairedData.digits a).map fun n => (n,0)
    | [a,b] => do
      let whole ← CirclePairedData.digits a
      let fraction ← CirclePairedData.digits b
      pure (whole * 10^b.length + fraction,b.length)
    | _ => none
  let numerator : Int := if negative then -(Int.ofNat digits) else Int.ofNat digits
  let scale := e-(places:Int)
  if 0≤scale then return (numerator*(10^scale.toNat):Int)
  return Rat.divInt numerator (10^(-scale).toNat)

private meta def parseRow (fields : List (List Char)) : Option Row := do
  let [n,step,observed,theoremTime,rmsSlow,rmsFast,tailSlow,tailFast] := fields | none
  return ⟨← CirclePairedData.digits n,← scientific step,← scientific observed,
    ← CirclePairedData.digits theoremTime,← scientific rmsSlow,← scientific rmsFast,
    ← scientific tailSlow,← scientific tailFast⟩

open Lean Elab Term in
elab "pairedResidualRows " csv:term : term => do
  let e ← elabTerm csv (some (mkConst ``String))
  let some key := e.constName? | throwError "expected a source definition"
  let some (.lit (.strVal text)) := (← getConstInfo key).value? | throwError "expected a literal source string"
  let keys := ["n","step","observed_time","theorem_time","rms_slow","rms_fast","tail_slow","tail_fast"]
  let .ok fields := CirclePairedData.columnsFromLiteral text keys | throwError "invalid paired CSV structure"
  let some rows := fields.mapM parseRow | throwError "invalid decimal in a residual or time column"
  let expressions := rows.map fun r => mkAppN (mkConst ``Row.mk) #[
    toExpr r.n, toExpr r.step, toExpr r.observedTime, toExpr r.theoremTime,
    toExpr r.rmsSlow, toExpr r.rmsFast, toExpr r.tailSlow, toExpr r.tailFast]
  Meta.mkListLit (mkConst ``Row) expressions

set_option maxRecDepth 200000 in
/-- All 472 archived rows with named columns selected before filtering by step. -/
def archivedRows : List Row := pairedResidualRows CirclePairedData.source

def primaryRows : List Row := archivedRows.filter (fun r => r.step == (1/4:Rat))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Count and comparisons on the exact rational fields are executed by the kernel. -/
theorem primary_residuals_tails_times :
    archivedRows.length = 472 ∧ primaryRows.length = 384 ∧ ∀ r ∈ primaryRows,
      0≤r.rmsSlow ∧ r.rmsSlow < (143/10^14:Rat) ∧
      0≤r.rmsFast ∧ r.rmsFast < (143/10^14:Rat) ∧
      0≤r.tailSlow ∧ 0≤r.tailFast ∧
      (r.n:Rat)^2*(r.tailSlow+r.tailFast) < (8/10^10:Rat) ∧
      ((r.n=3 ∧ r.observedTime=160 ∧ r.theoremTime=1027) ∨
       (r.n=5 ∧ r.observedTime=512 ∧ r.theoremTime=3735)) := by
  decide +kernel

end CirclePairedResidualData
