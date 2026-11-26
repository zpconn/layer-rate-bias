module

public import Init.Data.List.SplitOn.Basic
import all Init.Data.List.SplitOn.Basic
public meta import Lean
import Lean.Elab.BuiltinTerm

/-! Exact decimal comparisons on the frozen unquoted, comma-separated paired-run table. -/
@[expose] public section
namespace CirclePairedData

/-- The repository copy of the full paired-run CSV, including the smaller-step reruns. -/
def source : String := include_str "../layer-rates/paired-runs.csv"

def digits (cs : List Char) : Option Nat := do
  guard (!cs.isEmpty)
  cs.foldlM (fun n c => do
    let k := c.toNat
    guard (48 ≤ k && k ≤ 57)
    return 10*n+(k-48)) 0

/-- Signed decimal numerator and power-of-ten denominator. No floating-point conversion. -/
def decimal (cs : List Char) : Option (Int × Nat) := do
  let negative := cs.head? == some '-'
  let [a,b] := (if negative then cs.tail else cs).splitOn '.' | none
  let x ← digits a
  let y ← digits b
  let denominator : Nat := 10^b.length
  let numerator : Int := x*denominator+y
  return (if negative then -numerator else numerator,denominator)

def compareDecimal (a b : Int × Nat) : Ordering := compare (a.1*b.2) (b.1*a.2)

/-- The seed index is verified as the next index in the corresponding cell. -/
structure Cell where
  rows : Nat := 0
  ruleSlow : Nat := 0
  slowWins : Nat := 0
  correct : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Ordered by design `(3,512), (3,8192), (3,32768), (5,8192)`, each with
ordinary initialization followed by the `above` stratum. -/
structure Report where
  cells : List Cell := List.replicate 8 {}
  eighthSteps : Nat := 0
  sixteenthSteps : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def addRow (r : Report) (fields : List (List Char)) : Option Report := do
  let [n,m,seed,stratum,step,grid,slow,fast] := fields | none
  if step == ['0','.','1','2','5'] then return {r with eighthSteps := r.eighthSteps+1}
  if step == ['0','.','0','6','2','5'] then return {r with sixteenthSteps := r.sixteenthSteps+1}
  guard (step == ['0','.','2','5'])
  let group ← match ← digits n, ← digits m with
    | 3,512 => some 0 | 3,8192 => some 1 | 3,32768 => some 2 | 5,8192 => some 3 | _,_ => none
  let conditional ← if stratum == ['n','a','t','u','r','a','l'] then some false
    else if stratum == ['a','b','o','v','e'] then some true else none
  let index := 2*group+conditional.toNat
  let c ← r.cells[index]?
  guard ((← digits seed) == c.rows)
  let prediction := compareDecimal (← decimal grid) (1,1)
  let observation := compareDecimal (← decimal slow) (← decimal fast)
  guard (prediction != .eq && observation != .eq)
  let ruleSlow := prediction == .lt
  let slowWins := observation == .gt
  guard (!conditional || !ruleSlow)
  let updated : Cell := ⟨c.rows+1,c.ruleSlow+ruleSlow.toNat,c.slowWins+slowWins.toNat,
    c.correct+(ruleSlow == slowWins).toNat⟩
  return {r with cells := r.cells.set index updated}

/-- At elaboration the CSV is split into raw character tokens. The header locates the
columns, each row must have precisely the header width, and splitting must round-trip
byte for byte. Every primary numerical comparison and every count runs in the kernel. -/
meta def columnsFromLiteral (csv : String)
    (keys : List String := ["n","m","seed","stratum","step","grid0","slow","fast"]) :
    Except String (List (List (List Char))) := do
  let lines := csv.splitOn "\r\n"
  unless String.intercalate "\r\n" lines == csv && lines.getLast? == some "" do
    throw "expected CRLF-terminated paired CSV"
  let header::rows := lines.dropLast | throw "empty CSV"
  let names := header.splitOn ","
  let positions ← keys.mapM fun key => do
    unless names.count key == 1 do throw s!"expected unique column {key}"
    return names.idxOf key
  rows.mapM fun line => do
    let fields := line.splitOn ","
    unless fields.length == names.length && String.intercalate "," fields == line do
      throw "invalid column count or separator"
    positions.mapM fun k => do
      let some field := fields[k]? | throw "missing field"
      return field.toList

open Lean Elab Term in
elab "pairedColumns " csv:term : term => do
  let e ← elabTerm csv (some (mkConst ``String))
  let some key := e.constName? | throwError "expected a source definition"
  let some (.lit (.strVal text)) := (← getConstInfo key).value? | throwError "expected a literal source string"
  match columnsFromLiteral text with
  | .error why => throwError why
  | .ok rows => return toExpr rows

set_option maxRecDepth 200000 in
/-- Full literal contents of the eight named columns of all 472 source rows, in source order. -/
def archivedColumns : List (List (List Char)) := pairedColumns source

/-- The kernel parses each decimal and compares exact integer products. -/
def tabulate (rows : List (List (List Char))) : Option Report := rows.foldlM addRow {}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All 384 primary rows, in eight 48-seed cells, and the 88 additional step-size rows.
Within each cell the columns are total, rule calls slow, trained slow wins, and rule correct. -/
theorem archived_primary_counts : tabulate archivedColumns = some
    ⟨[⟨48,47,46,47⟩,⟨48,0,9,39⟩,⟨48,47,47,48⟩,⟨48,0,2,46⟩,
      ⟨48,45,45,48⟩,⟨48,0,2,46⟩,⟨48,47,48,47⟩,⟨48,0,4,44⟩],64,24⟩ := by
  decide +kernel

/-- The widest above-baseline cell in the primary run; record every seed for
which the measured ordering disagrees and test its decimal margin exactly. -/
def widestMiss (row : List (List Char)) : Option (List (Nat × Bool)) := do
  let [n,m,seed,stratum,step,grid,slow,fast] := row | none
  if n != ['3'] || m != "32768".toList || stratum != "above".toList || step != "0.25".toList then return []
  let g ← decimal grid
  guard (compareDecimal g (1,1) == .gt)
  let order := compareDecimal (← decimal slow) (← decimal fast)
  guard (order != .eq)
  if order == .lt then return []
  return [(← digits seed, compareDecimal g (201,200) == .lt)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The only two exceptions were above one by strictly less than 0.005. -/
theorem widest_exceptions :
    (archivedColumns.mapM widestMiss).map List.flatten = some [(5,true),(31,true)] := by
  decide +kernel

end CirclePairedData
