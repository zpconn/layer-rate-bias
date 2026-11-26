module

public import CircleSevenDesign
public import CircleGroupedResidual
import all CircleSevenDesign
import all CircleSevenSpectrum
import all CircleGroupedResidual
import all CircleSpectralPathLength
import Mathlib.Tactic

/-! The four conjugate residue classes produce the actual seven-point grouped path constant. -/
@[expose] public section
noncomputable section
namespace CircleSevenGrouped
open Real CircleSevenSpectrum CircleSevenDesign CircleGroupedResidual CircleSpectralPathLength CircleFlowPath

def sevenLevel (r : ZMod 7) := fold7 r.val
def sevenRate (d : ℕ) := mode 1 (fold7 d)

theorem level_le (r : ZMod 7) : sevenLevel r ≤ 3 := fold_small _

private theorem fold_id (k : ℕ) (h : k≤3) : fold7 k=k := by
  unfold fold7;rw [Nat.mod_eq_of_lt (by omega),min_eq_left (by omega)]

private theorem mode_level (τ : ℝ) (r : ZMod 7) : mode τ (sevenLevel r)=mode τ r.val := by
  have a : ∀ s : ZMod 7, fold7 (2*(sevenLevel s))=fold7 (2*s.val) := by decide
  have b : ∀ s : ZMod 7, fold7 (3*(sevenLevel s))=fold7 (3*s.val) := by decide
  simp only [mode]
  rw [fold_id _ (level_le r),a,b]
  rfl

theorem rate_bounds (d : ℕ) : 0<sevenRate d ∧ sevenRate d≤1 := by
  obtain ⟨_,_,_,_,a,b,c,e⟩ := spectral_inputs
  have h := fold_small d
  unfold sevenRate
  generalize fold7 d=k at h ⊢
  interval_cases k <;> constructor <;> linarith

theorem rate_pos (d : ℕ) : 0<sevenRate d := (rate_bounds d).1
theorem rate_le_one (d : ℕ) : sevenRate d≤1 := (rate_bounds d).2

theorem rate_eigen (r : ZMod 7) : sevenRate (sevenLevel r)=eigen 1 r := by
  rw [sevenRate,fold_id _ (level_le r),mode_level];exact mode_alias _ (by norm_num) (by norm_num) r

private theorem cov_mode (r : ZMod 7) : eigen 0 r=mode 0 (sevenLevel r) := by
  rw [mode_level];exact (mode_alias _ (by norm_num) (by norm_num) r).symm

private theorem teacher_sq (r : ZMod 7) : ‖normalizedCoeff (circleLabel 7) r‖^2 =
    if sevenLevel r=0 then 1 else if sevenLevel r=1 then 1/4 else 0 := by
  rw [normalized_teacher]
  have a : ∀ s : ZMod 7, (0:ZMod 7)=s ↔ sevenLevel s=0 := by decide
  have b : ∀ s : ZMod 7, ((1:ZMod 7)=s ∨ (-1:ZMod 7)=s) ↔ sevenLevel s=1 := by decide
  have dis : ∀ s : ZMod 7, (1:ZMod 7)=s → (-1:ZMod 7) ≠ s := by decide
  by_cases h0 : (0:ZMod 7)=r
  · have n1 : (1:ZMod 7)≠r := h0 ▸ (by decide : (1:ZMod 7)≠0)
    have nn : (-1:ZMod 7)≠r := h0 ▸ (by decide : (-1:ZMod 7)≠0)
    simp only [ite_eq_left h0,ite_eq_right n1,ite_eq_right nn,ite_eq_left ((a r).mp h0)]
    norm_num
  · have n0 := (a r).not.mp h0
    simp only [ite_eq_right h0,ite_eq_right n0,zero_add]
    by_cases h1 : (1:ZMod 7)=r
    · have yes := (b r).mp (Or.inl h1)
      simp only [ite_eq_left h1,ite_eq_right (dis r h1),ite_eq_left yes,add_zero,mul_one,norm_inv]
      norm_num
    · by_cases hn : (-1:ZMod 7)=r
      · have yes := (b r).mp (Or.inr hn)
        simp only [ite_eq_right h1,ite_eq_left hn,ite_eq_left yes,zero_add,mul_one,norm_inv]
        norm_num
      · have no := (b r).not.mp (not_or.mpr ⟨h1,hn⟩)
        simp [h1,hn,no]

private def seedMass (d : ℕ) := mode 0 d + (if d=0 then 1 else if d=1 then 1/4 else 0)

private theorem grouped_sum (d : ℕ) :
    (∑ r ∈ bandSet sevenLevel d,(eigen 0 r+‖normalizedCoeff (circleLabel 7) r‖^2)) =
      ((bandSet sevenLevel d).card:ℝ)*seedMass d := by
  simp_rw [cov_mode,teacher_sq]
  rw [show ((bandSet sevenLevel d).card:ℝ)*seedMass d=∑ _r ∈ bandSet sevenLevel d,seedMass d by simp]
  apply Finset.sum_congr rfl
  intro r hr
  have eq := (Finset.mem_filter.mp hr).2
  change sevenLevel r=d at eq;rw [eq];rfl

/-- The true grouped Gaussian L² movement bound equals the quantity enclosed by interval arithmetic. -/
theorem cost_eq : groupCost 7 3 sevenLevel sevenRate=groupedF := by
  unfold groupCost
  simp_rw [grouped_sum]
  have c0 : (bandSet sevenLevel 0).card=1 := by decide
  have c1 : (bandSet sevenLevel 1).card=2 := by decide
  have c2 : (bandSet sevenLevel 2).card=2 := by decide
  have c3 : (bandSet sevenLevel 3).card=2 := by decide
  rw [show 3+1=4 by decide]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,c0,c1,c2,c3,Nat.cast_one,Nat.cast_ofNat]
  norm_num only [seedMass,OfNat.ofNat_ne_zero,OfNat.one_ne_ofNat,reduceCtorEq,
    one_mul,ite_true,ite_false,sevenRate,show fold7 0=0 from rfl,show fold7 1=1 from rfl,
    show fold7 2=2 from rfl,show fold7 3=3 from rfl,add_zero]
  unfold groupedF
  congr 1 <;> ring_nf

end CircleSevenGrouped
