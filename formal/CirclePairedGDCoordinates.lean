module

public import CircleSynchronizedWidth
import all CircleSynchronizedEscape
import Mathlib.Tactic

/-! A synchronized Gaussian box contained in the initial neighborhood of both
layer-rate trajectories. The doubled box index accommodates the larger
error amplification factor for unequal layer rates. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDCoordinates
open Set CircleEscapeBridge CircleSynchronizedEscape CircleSeedIntegrability

theorem coordinate {N m T : ℕ} {R : ℝ} (hN : 0<N) (hR : 1≤R)
    {z : Seed m} (hz : z ∈ syncBox N m (2*T) 1 (R/2))
    (j : Fin m) (k : Fin 3) :
    |z (j,k) - (if k=2 then 0 else R)| ≤ (1/(8*(N:ℝ)*1024^T))*R := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hk := hz (j,k) (mem_univ _)
  change location 1 (R/2) k ≤ z (j,k) ∧
    z (j,k) ≤ location 1 (R/2) k + side N (2*T) at hk
  have loc : location 1 (R/2) k = (if k=2 then 0 else R) := by
    fin_cases k <;> norm_num [location] <;> ring
  rw [loc] at hk
  have width : side N (2*T) ≤ 1/(8*(N:ℝ)*1024^T) := by
    unfold side
    apply one_div_le_one_div_of_le (by positivity)
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num)
      (by norm_num : (1024:ℝ)≤512^2) T) (by positivity)
  exact (abs_le.mpr ⟨by linarith [hk.1, show 0 ≤ side N (2*T) by unfold side; positivity],
    by linarith [hk.2]⟩).trans (width.trans (le_mul_of_one_le_right (by positivity) hR))

end CirclePairedGDCoordinates
