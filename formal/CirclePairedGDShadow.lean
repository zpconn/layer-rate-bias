module

public import CirclePairedGDCenter
public import CirclePairedGDTube
import all CirclePairedGDCenter
import all CirclePairedGDGeometry
import all CircleWeightedStep
import Mathlib.Tactic

/-! A common neighborhood of Gaussian initializations tracks the synchronized
trajectory up to a prescribed finite step. The neighborhood radius pays for
the worst possible relative error growth at every step. -/

@[expose] public section
noncomputable section

namespace CirclePairedGDShadow

open Real CircleFlowPath CircleWeightedStep CirclePairedGDCenter CirclePairedGDTube

/-- A coordinate error of order `1024⁻ᵀ/N` at initialization is sufficient
for relative coordinate control after `T` actual simultaneous updates. -/
theorem shadow {N m : ℕ} {τ η R : ℝ}
    (hN : 3≤N) (hm : 0<m) (odd : Odd N) (hτ : 1/2≤τ) (hη : 0<η)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (T : ℕ) {z : State m}
    (hz : Near z R R (1/(8*(N:ℝ)*1024^T))) :
    Near (iterate τ η N z T) (sign T * (orbit N m τ η R T).1)
      (sign T * (orbit N m τ η R T).2) (1/(8*(N:ℝ))) := by
  let o := orbit N m τ η R
  let e (t : ℕ) : ℝ := (1024:ℝ)^t / 1024^T / (8*N)
  have ep (t : ℕ) : 0 ≤ e t := by dsimp [e]; positivity
  have e0 : e 0 = 1/(8*(N:ℝ)*1024^T) := by dsimp [e]; rw [pow_zero,div_div]; ring
  have es (t : ℕ) : e (t+1) = 1024*e t := by dsimp [e]; rw [pow_succ]; ring
  have ec (t : ℕ) (ht : t≤T) : e t ≤ 1/(8*(N:ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (div_le_one₀ (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) ht)
  have en : e T = 1/(8*(N:ℝ)) := by simp [e]
  have large := orbit_large hN hm hτ hη hR hlarge
  have hr (t : ℕ) : 1 ≤ (o t).1 ∧ 1 ≤ (o t).2 := ⟨hR.trans (large t).1,hR.trans (large t).2⟩
  have ax (t : ℕ) : Axial (state N m τ η R t) (sign t*(o t).1) (sign t*(o t).2) :=
    fun _ => ⟨rfl,rfl,rfl⟩
  have ax_next (t : ℕ) : Axial (segment τ N (state N m τ η R t) η)
      (sign (t+1)*(o (t+1)).1) (sign (t+1)*(o (t+1)).2) := by
    rw [state_step hN hm hτ hη hR hlarge t]
    exact ax (t+1)
  have hA (t : ℕ) : |sign t*(o t).1|=(o t).1 := by
    rw [abs_mul,abs_sign,one_mul,abs_of_nonneg ((zero_le_one' ℝ).trans (hr t).1)]
  have hW (t : ℕ) : |sign t*(o t).2|=(o t).2 := by
    rw [abs_mul,abs_sign,one_mul,abs_of_nonneg ((zero_le_one' ℝ).trans (hr t).2)]
  have tracked (t : ℕ) (ht : t≤T) : Near (iterate τ η N z t) (sign t*(o t).1) (sign t*(o t).2) (e t) := by
    induction t with
    | zero =>
      rw [e0,sign_zero]
      simpa [o,orbit_zero,iterate] using hz
    | succ t ih =>
      have hs := orbit_scale hN hm hτ hη hR hlarge t
      have hl := orbit_step_lower hN hm hτ hη hR hlarge t
      have ht0 : 0≤τ := by linarith only [hτ]
      rw [iterate,es]
      apply step_near (N:=N) (by omega) hm odd (ax t) (ax_next t) (ih (by omega)) ht0 hη.le
        (ep t) (ec t (by omega))
      · rw [hW]; linarith only [(hr t).2]
      · rw [hA,hW]
        exact one_le_mul_of_one_le_of_one_le (one_le_sqrt.mpr (by exact_mod_cast hm))
          (one_le_mul_of_one_le_of_one_le (hr t).1 (hr t).2)
      · rw [hW]
        exact hs.1
      · rw [hA]
        exact hs.2
      · rw [hA,hW,hA]
        have term : 0 ≤ η*(o t).1*(o t).2^2 :=
          mul_nonneg (mul_nonneg hη.le ((zero_le_one' ℝ).trans (hr t).1)) (sq_nonneg _)
        have ha : (15/256)*η*(o t).1*(o t).2^2 ≤ (o (t+1)).1 := hl.1
        linarith only [ha,term]
      · rw [hW,hA,hW]
        have term : 0 ≤ η*τ*(o t).1^2*(o t).2 := by
          exact mul_nonneg (mul_nonneg (mul_nonneg hη.le ht0) (sq_nonneg _))
            ((zero_le_one' ℝ).trans (hr t).2)
        have bound : (15/256)*η*τ*(o t).2*(o t).1^2 ≤ (o (t+1)).2 := hl.2
        linarith only [bound,term]
  simpa only [en] using tracked T le_rfl

end CirclePairedGDShadow
