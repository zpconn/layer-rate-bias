module

public import CirclePairedGDTail
import all CircleSynchronizedWidth
import all CirclePairedGDTail
import all CirclePairedCoefficient
import all CircleEscapeBridge
import Mathlib.Tactic

/-! A finite-grid lower bound for the unconditional squared prediction error.
The contrast and the predicted contrast use the same Gaussian seed. -/

@[expose] public section
noncomputable section
namespace CirclePairedGDFiniteTail

open Real MeasureTheory CircleEscapeBridge CirclePairedCoefficient CirclePairedGDEndpoint
  CirclePairedGDIntegrable CircleSynchronizedEscape CircleSynchronizedWidth

private theorem box_score {N m T : ℕ} {R : ℝ} (hn : 0<N) (hm : 0<m) (hR : 32≤R)
    {z : Seed m} (hz : z ∈ syncBox N m T 1 (R/2)) :
    |score N m z| ≤ sqrt (m:ℝ)*(2+64*(R/2)^2) := by
  have lo := ref_cap N m T hn hm (R/2) 0 (by linarith) (by norm_num) (by norm_num) z hz
  have hi := ref_cap N m T hn hm (R/2) 1 (by linarith) (by norm_num) (by norm_num) z hz
  have sub : score N m z = reference N m 1 z - reference N m 0 z := by
    unfold score reference
    ring
  rw [sub]
  have root : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  exact (abs_sub _ _).trans (by linarith only [hi, lo, root])

/-- Explicit lower bound for any finite grid and horizon satisfying the displayed
size conditions. The factor `cost` is the negative log-probability bound
for one common Gaussian initialization box. -/
theorem finite_mse_lower {N m t : ℕ} {η R d D : ℝ} (hN : 3≤N) (odd : Odd N) (hm : 0<m)
    (hη : 0<η) (hR : 32≤R) (hlarge : 16*(32/η+32)≤R^2) (ht : 1≤t)
    (hd : |d|≤D) (grid : D*(2+64*(R/2)^2) ≤ (N:ℝ)^2) :
    exp ((2*log 2/3)*(3:ℝ)^(t+1) - cost N m (2*(t+1)) (R/2)) / 4 ≤
      ∫ z, (contrast N m (t+1) η z - (d/(N:ℝ)^2)*score N m z)^2 ∂seedLaw m := by
  let q := (2:ℝ)^(3^t : ℕ)
  have q2 : 2≤q := by
    simpa only [pow_one] using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num)
      (show 1≤3^t from Nat.one_le_pow _ _ (by decide))
  have root : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  have hn : 0<N := by omega
  have denom : 0<(N:ℝ)^2 := by exact pow_pos (by exact_mod_cast hn) 2
  have positive : 0≤2+64*(R/2)^2 := by positivity
  have term : |d| *(2+64*(R/2)^2) ≤ (N:ℝ)^2 :=
    (mul_le_mul_of_nonneg_right hd positive).trans grid
  have ref {z : Seed m} (hz : z ∈ syncBox N m (2*(t+1)) 1 (R/2)) :
      |(d/(N:ℝ)^2)*score N m z| ≤ sqrt (m:ℝ) := by
    rw [abs_mul, abs_div, abs_of_nonneg denom.le]
    apply (mul_le_mul_of_nonneg_left (box_score hn hm hR hz) (by positivity)).trans
    calc
      _ = sqrt (m:ℝ) * ((|d| *(2+64*(R/2)^2))/(N:ℝ)^2) := by ring
      _ ≤ sqrt (m:ℝ) := mul_le_of_le_one_right (sqrt_nonneg _) ((div_le_one₀ denom).mpr term)
  have mass := gaussian_box_probability N m (2*(t+1)) hn (R/2) 1 (by linarith) (by norm_num)
  have hF : MemLp (contrast N m (t+1) η) 2 (seedLaw m) :=
    contrast_memLp _ _ _ _ _ _ 2 (by norm_num)
  have hG := scaledScore_memLp d N m 2 (by norm_num)
  have bound := CircleEscapeMoment.paired_second_moment_of_escape hF hG
    (measurable_syncBox ..) mass (fun _ h => CirclePairedGDBox.box_contrast_scaled hN odd hm hη hR hlarge ht h)
    (fun _ h => ref h)
  have hq : q/2 ≤ sqrt (m:ℝ)*q - sqrt (m:ℝ) := by
    have h := mul_le_mul_of_nonneg_right root (show 0≤q-1 by linarith)
    nlinarith only [h,q2]
  have hmax := pow_le_pow_left₀ (by dsimp [q]; positivity : 0≤q/2)
    (hq.trans (le_max_left _ 0)) 2
  refine le_trans ?_ bound
  rw [sub_eq_add_neg, exp_add,show (2*log 2/3) = CirclePairedGDTail.gain by rfl,
    CirclePairedGDTail.amplification]
  calc
    _ = exp (-cost N m (2*(t+1)) (R/2)) * (q/2)^2 := by dsimp [q]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax (exp_pos _).le

end CirclePairedGDFiniteTail
