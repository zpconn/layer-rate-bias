module

public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Certified enclosures of the angles in the seven-point real Fourier transform.
The three cosines are isolated as roots of the same integer polynomial. -/
@[expose] public section
noncomputable section
namespace CircleSevenTrig
open Real Set

def angle (j : ℕ) : ℝ := 2*π*j/7
private def P (x : ℝ) := 8*x^3+4*x^2-4*x-1

private theorem root (j : ℕ) (j0 : 0<j) (j3 : j≤3) : P (cos (angle j))=0 := by
  let t := angle j
  have jlo : (0:ℝ)<j := Nat.cast_pos.mpr j0
  have jhi : (j:ℝ)≤3 := by exact_mod_cast j3
  have ht : 0<t := by dsimp [t,angle];positivity
  have ht' : t≤π := by dsimp [t,angle];nlinarith only [mul_le_mul_of_nonneg_left jhi pi_pos.le,pi_pos]
  have neq : cos t≠1 := ne_of_lt (cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) ht' ht |>.trans_eq cos_zero)
  have h4 : cos (4*t)=cos (3*t) := by
    rw [show 4*t= -(3*t)+(j:ℝ)*(2*π) by dsimp [t,angle];ring,cos_add_nat_mul_two_pi,cos_neg]
  rw [show 4*t=2*(2*t) by ring,cos_two_mul,cos_two_mul,cos_three_mul] at h4
  change P (cos t)=0
  apply (mul_eq_zero.mp (show (cos t-1)*P (cos t)=0 by unfold P;nlinarith only [h4])).resolve_left
  exact sub_ne_zero.mpr neq

private theorem mono_right : MonotoneOn P (Icc (1/2) 1) := by
  intro x hx y hy hxy
  have coeff : 0≤8*(y*y+x*y+x*x)+4*(y+x)-4 := by
    nlinarith only [hx.1,hy.1,sq_nonneg x,sq_nonneg y,mul_nonneg (by linarith only [hx.1] : 0≤x) (by linarith only [hy.1] : 0≤y)]
  unfold P
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) coeff]
private theorem mono_mid : AntitoneOn P (Icc (-(1/2)) 0) := by
  intro x hx y hy hxy
  have coeff : 8*(y*y+x*y+x*x)+4*(y+x)-4≤0 := by
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (by linarith only [hx.1] : 0≤x+1/2) hx.2,
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [hy.1] : 0≤y+1/2) hy.2,
      mul_nonneg (by linarith only [hx.1] : 0≤x+1/2) (by linarith only [hy.2] : 0≤-y), hy.1]
  unfold P
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) coeff]
private theorem mono_left : MonotoneOn P (Icc (-1) (-(3/4))) := by
  intro x hx y hy hxy
  have coeff : 0≤8*(y*y+x*y+x*x)+4*(y+x)-4 := by
    nlinarith only [sq_nonneg (x+3/4),sq_nonneg (y+3/4),hx.1,hy.1,hx.2,hy.2,
      mul_nonneg (by linarith only [hx.2] : 0≤-x-3/4) (by linarith only [hy.2] : 0≤-y-3/4)]
  unfold P
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) coeff]

private theorem isolate {F : ℝ→ℝ} {s : Set ℝ} {x l h : ℝ} (mon : MonotoneOn F s)
    (hx : x∈s) (hl : l∈s) (hh : h∈s) (r : F x=0) (left : F l<0) (right : 0<F h) :
    l≤x ∧ x≤h := by
  constructor
  · by_contra! contra
    linarith only [mon hx hl contra.le,left,r]
  · by_contra! contra
    linarith only [mon hh hx contra.le,right,r]

theorem cos_one : 0.62348980185873352≤cos (angle 1) ∧ cos (angle 1)≤0.62348980185873354 := by
  have lo : 1/2≤cos (angle 1) := by
    rw [← cos_pi_div_three]
    apply cos_le_cos_of_nonneg_of_le_pi (by dsimp [angle];positivity) (by linarith [pi_pos])
    dsimp [angle];linarith [pi_pos]
  apply isolate mono_right ⟨lo,cos_le_one _⟩ (by constructor <;> norm_num) (by constructor <;> norm_num) (root 1 (by decide) (by decide)) <;> norm_num [P]
theorem cos_two : -0.22252093395631442≤cos (angle 2) ∧ cos (angle 2)≤ -0.22252093395631439 := by
  have lo : -(1/2)≤cos (angle 2) := by
    have val : cos (π-π/3)= -(1/2) := by rw [cos_pi_sub,cos_pi_div_three]
    rw [←val]
    apply cos_le_cos_of_nonneg_of_le_pi (by dsimp [angle];positivity) (by linarith [pi_pos])
    dsimp [angle];linarith [pi_pos]
  have hi : cos (angle 2) ≤ 0 := by
    rw [←cos_pi_div_two]
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity) (by dsimp [angle]; linarith [pi_pos])
    dsimp [angle];linarith [pi_pos]
  apply isolate (F:=fun x => -P x) (fun _ hx _ hy h => neg_le_neg (mono_mid hx hy h)) ⟨lo,hi⟩ (by constructor <;> norm_num) (by constructor <;> norm_num)
    (by rw [root 2 (by decide) (by decide),neg_zero]) <;> norm_num [P]
theorem cos_three : -0.90096886790241914≤cos (angle 3) ∧ cos (angle 3)≤ -0.90096886790241911 := by
  have hi : cos (angle 3)≤ -(3/4) := by
    calc _ ≤ cos (π-π/6) := by
           apply cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) (by dsimp [angle];linarith [pi_pos])
           dsimp [angle];linarith [pi_pos]
         _ ≤ _ := by rw [cos_pi_sub,cos_pi_div_six];nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤3),sqrt_nonneg (3:ℝ)]
  exact isolate mono_left ⟨neg_one_le_cos _,hi⟩ (by constructor <;> norm_num) (by constructor <;> norm_num) (root 3 (by decide) (by decide)) (by norm_num [P]) (by norm_num [P])

theorem halfCell_values : sin (π/14)= -cos (angle 2) ∧ cos (π/14)=sin (angle 2) := by
  have eq : angle 2=π/2+π/14 := by dsimp [angle];ring
  rw [eq,add_comm (π/2),cos_add_pi_div_two,sin_add_pi_div_two,neg_neg]
  exact ⟨rfl,rfl⟩
end CircleSevenTrig
