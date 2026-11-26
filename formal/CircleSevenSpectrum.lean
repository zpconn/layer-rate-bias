module

public import CircleSevenTrig
public import CircleGridSpectrum
import all CircleSevenTrig
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleSpectrum
import Mathlib.Tactic

/-! The finite cosine transform of the actual seven-point circle kernel. -/
@[expose] public section
noncomputable section
namespace CircleSevenSpectrum
open Real CircleSevenTrig CircleGridSpectrum CircleKernelIdentification CircleSpectrum

def sample (τ : ℝ) (j : ℕ) :=
  (sin (angle j)+(1+τ)*(π-angle j)*cos (angle j))/(2*π)

def fold7 (j : ℕ) := min (j%7) (7-j%7)

def mode (τ : ℝ) (r : ℕ) :=
  (sample τ 0+2*(sample τ 1*cos (angle (fold7 r))+
    sample τ 2*cos (angle (fold7 (2*r)))+sample τ 3*cos (angle (fold7 (3*r)))))/7


local instance : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩

private theorem fold_small (j : ℕ) : fold7 j≤3 := by
  unfold fold7
  have := Nat.mod_lt j (by decide : 0<7)
  omega

private theorem cos_fold (j : ℕ) (hj : j<7) : cos (angle j)=cos (angle (fold7 j)) := by
  unfold fold7;rw [Nat.mod_eq_of_lt hj]
  by_cases h : j≤7-j
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega)]
    rw [show angle (7-j)=2*π-angle j by
      unfold angle; rw [Nat.cast_sub (by omega : j≤7)];push_cast;ring,cos_two_pi_sub]

/-- Each actual circulant sample equals the closed angular formula in its principal semicircle. -/
theorem periodic_sample (τ : ℝ) (j : ZMod 7) :
    periodicTangent τ (gridAngle j) = (sample τ (fold7 j.val):ℂ) := by
  let t := angle (fold7 j.val)
  let a := if j.val≤3 then t else -t
  have hsmall : 0≤t ∧ t<π := by
    have d : ((fold7 j.val:ℕ):ℝ) ≤ 3 := by exact_mod_cast fold_small _
    dsimp [t,angle];exact ⟨by positivity,by nlinarith [mul_le_mul_of_nonneg_left d pi_pos.le,pi_pos]⟩
  have ha : a∈Set.Ioc (-π) (-π+(π- -π)) := by
    dsimp [a]; split <;> constructor <;> linarith [hsmall.1,hsmall.2]
  have grid : gridAngle j=(a:AddCircle (π- -π)) := by
    unfold gridAngle
    have hj := j.val_lt
    dsimp [a,t,fold7]
    rw [Nat.mod_eq_of_lt hj]
    split_ifs with small
    · rw [min_eq_left (by omega)];congr 1;dsimp [angle];ring
    · rw [min_eq_right (by omega)]
      have id : (π- -π)*(j.val:ℝ)/7 = -(angle (7-j.val))+(π- -π) := by
        unfold angle;rw [Nat.cast_sub hj.le];push_cast;ring
      rw [id,AddCircle.coe_add,AddCircle.coe_period,add_zero]
  rw [grid]
  change AddCircle.liftIoc (π- -π) (-π) (fun x => (polarNTK τ |x|:ℂ)) (a:ℝ) = _
  rw [AddCircle.liftIoc_coe_apply ha]
  have habs : |a|=t := by unfold a;split <;> simp [abs_of_nonneg hsmall.1]
  rw [habs,angular_tangent τ t hsmall.1 hsmall.2.le]
  rfl

private theorem char_cos (r j : ZMod 7) : (char r j).re = cos (angle (fold7 (r*j).val)) := by
  have h := ZMod.stdAddChar_coe (N:=7) (((r*j).val:ℕ):ℤ)
  rw [Int.cast_natCast,ZMod.natCast_zmod_val] at h
  rw [char,h,←cos_fold _ (r*j).val_lt]
  rw [show (2*↑π*Complex.I*↑((r*j).val:ℤ)/(7:ℕ):ℂ) = (angle (r*j).val:ℝ)*Complex.I by
    unfold angle; push_cast;ring,Complex.exp_ofReal_mul_I_re]

private theorem alias_finite (τ : ℝ) (ht : 0≤τ) (hu : τ≤2) (r : ZMod 7) :
    aliasValue (tangentCoeff τ) r =
      (∑ j : ZMod 7, sample τ (fold7 (-j).val) * cos (angle (fold7 (r*j).val)))/7 := by
  have h := congrArg Complex.re (sampled_character_eigenvalue τ ht hu r 0)
  have zero : char r 0 = 1 := by simp [char,AddChar.map_zero_eq_one]
  simp only [convolution,zero_sub,periodic_sample,Complex.div_natCast_re,Complex.re_sum,
    Complex.re_ofReal_mul,char_cos,zero,mul_one,Complex.ofReal_re] at h
  exact h.symm

/-- Finite cosine transform of the seven sampled Jacobian products. The covariance
and equal-rate tangent are the cases τ=0 and τ=1. -/
theorem mode_alias (τ : ℝ) (ht : 0≤τ) (hu : τ≤2) (r : ZMod 7) :
    mode τ r.val = aliasValue (tangentCoeff τ) r := by
  rw [alias_finite τ ht hu r]
  let F := fun j : ZMod 7 => sample τ (fold7 (-j).val)*cos (angle (fold7 (r*j).val))
  change mode τ r.val=(∑ j, F j)/7
  rw [←fin_sum F]
  have negidx : ∀ j : Fin 7, fold7 (-(ZMod.finEquiv 7 j)).val=fold7 j.val := by decide
  have prodidx : ∀ (s : ZMod 7) (j : Fin 7),
    fold7 (s*(ZMod.finEquiv 7 j)).val=fold7 (fold7 j.val*s.val) := by decide
  dsimp only [F]
  simp_rw [negidx,prodidx,Fin.sum_univ_succ]
  change mode τ r.val = (sample τ 0*cos (angle (fold7 (0*r.val))) +
    (sample τ 1*cos (angle (fold7 (1*r.val))) +
    (sample τ 2*cos (angle (fold7 (2*r.val))) +
    (sample τ 3*cos (angle (fold7 (3*r.val))) +
    (sample τ 3*cos (angle (fold7 (3*r.val))) +
    (sample τ 2*cos (angle (fold7 (2*r.val))) +
    (sample τ 1*cos (angle (fold7 (1*r.val))) + 0)))))))/7
  simp only [mode,Nat.zero_mul,Nat.one_mul,show fold7 0=0 from rfl,show angle 0=0 by simp [angle],cos_zero,mul_one]
  ring

/-- The normalized mathlib DFT of the seven actual circle kernel samples. -/
theorem normalized_dft (τ : ℝ) (ht : 0≤τ) (hu : τ≤2) (r : ZMod 7) :
    (ZMod.dft (fun j => periodicTangent τ (gridAngle j)) r)/(7:ℂ) = (mode τ r.val:ℂ) := by
  rw [mode_alias τ ht hu r,ZMod.dft_apply]
  have h := sampled_character_eigenvalue τ ht hu r 0
  have zero : char r 0 = 1 := by simp [char,AddChar.map_zero_eq_one]
  rw [zero,mul_one] at h
  apply Eq.trans _ h
  unfold convolution
  congr 1
  rw [← (Equiv.sum_comp (Equiv.neg (ZMod 7))) (fun j => periodicTangent τ (gridAngle (0-j))*char r j)]
  apply Finset.sum_congr rfl
  intro j _
  simp [char,mul_comm]

theorem weight_one : weight 1 6 = (3/π^2)/mode 1 0 := by
  rw [weight_from_grid_alias 6 (by decide) (by decide) 1 (by norm_num) (by norm_num)]
  have h := mode_alias 1 (by norm_num) (by norm_num) (0:ZMod 7)
  rw [ZMod.val_zero] at h
  rw [h,k0];norm_num

end CircleSevenSpectrum
