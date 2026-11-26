module

public import CirclePathSelection
import Mathlib.Tactic

/-! Global measurable selection from unrelated finite-horizon witnesses.
Beyond each witness's horizon we hold its last state fixed. On a fixed time
interval this construction only needs a finite maximum of local speed bounds. -/
public section
noncomputable section
open Set Metric
open scoped NNReal

namespace CircleGlobalGluing
variable {E : Type*} [MetricSpace E] [ProperSpace E]

def stopAt (k : ℕ) (p : C(ℝ≥0,E)) : C(ℝ≥0,E) :=
  ⟨fun t => p (min t k), p.continuous.comp (continuous_id.min continuous_const)⟩

omit [ProperSpace E] in
theorem stopAt_agrees (k : ℕ) (p : C(ℝ≥0,E)) : EqOn p (stopAt k p) (Iic (k:ℝ≥0)) := by
  intro t ht
  exact congrArg p (min_eq_left (show t ≤ (k:ℝ≥0) from ht)).symm

private theorem nonexpansive_stop (k : ℝ≥0) (s t : ℝ≥0) :
    dist (min s k) (min t k) ≤ dist s t := by
  have h := (NNReal.isometry_coe.lipschitzWith.min_const (k:ℝ)).dist_le_mul s t
  simpa only [NNReal.dist_eq, Real.dist_eq, NNReal.coe_min, NNReal.coe_one,one_mul] using h

/-- If the finite-horizon conditions are local, closed and nested, existence
at each finite horizon with locally uniform Lipschitz bounds supplies a
single Borel selection of solutions on the entire positive time axis. -/
theorem measurable_of_prefixes [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace C(ℝ≥0,E)] [BorelSpace C(ℝ≥0,E)] (o : E)
    (P : ℕ → Set C(ℝ≥0,E)) (closed : ∀ k, IsClosed (P k))
    (nested : ∀ k, P (k+1) ⊆ P k)
    (locality : ∀ (k : ℕ) (p q : C(ℝ≥0,E)), EqOn p q (Iic (k:ℝ≥0)) → p ∈ P k → q ∈ P k)
    (finite_solution : ∀ x k, ∃ p ∈ P k, p 0 = x)
    (speed : ∀ n k : ℕ, ∃ L : ℝ≥0, ∀ p ∈ P k, p 0 ∈ closedBall o (n:ℝ) →
      LipschitzOnWith L p (Iic (k:ℝ≥0))) :
    ∃ f : E → C(ℝ≥0,E), Measurable f ∧ ∀ x, f x 0 = x ∧ ∀ k, f x ∈ P k := by
  classical
  choose L hL using speed
  have nest : Antitone P := antitone_nat_of_succ_le nested
  have exists_global (x : E) : ∃ p : C(ℝ≥0,E), p 0 = x ∧ ∀ k, p ∈ P k := by
    obtain ⟨n,hn⟩ := exists_nat_ge (dist x o)
    let M (T : ℝ≥0) := (Finset.range (⌈T⌉₊+1)).sup (L n)
    apply CirclePathSelection.exists_global_of_finite_horizons x P closed nested M
    intro k
    obtain ⟨p,hp,hx⟩ := finite_solution x k
    refine ⟨stopAt k p, locality _ _ _ (stopAt_agrees k p) hp, by simpa [stopAt] using hx, ?_⟩
    intro T
    let j := min k ⌈T⌉₊
    have hj : j ∈ Finset.range (⌈T⌉₊+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right ..))
    have hs := (hL n j p (nest (min_le_left ..) hp) (hx ▸ hn)).weaken (Finset.le_sup hj)
    have hmem (t : ℝ≥0) (ht : t ∈ Iic T) : min t (k:ℝ≥0) ∈ Iic (j:ℝ≥0) := by
      change min t (k:ℝ≥0) ≤ ((min k ⌈T⌉₊ : ℕ):ℝ≥0)
      rw [Nat.cast_min]
      exact le_min (min_le_right ..) ((min_le_left ..).trans (ht.trans (Nat.le_ceil T)))
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs' t ht
    exact (hs.dist_le_mul _ (hmem s hs') _ (hmem t ht)).trans
      (mul_le_mul_of_nonneg_left (nonexpansive_stop k s t) (M T).2)
  obtain ⟨f,hf,h⟩ := CirclePathSelection.exists_measurable_global_trajectory o (⋂ k, P k)
    (isClosed_iInter closed) (fun x => by
      obtain ⟨p,hx,hp⟩ := exists_global x
      exact ⟨p,mem_iInter.mpr hp,hx⟩) (fun n T => by
        refine ⟨L n ⌈T⌉₊, fun p hp hseed => ?_⟩
        exact (hL _ _ p (mem_iInter.mp hp _) hseed).mono (Iic_subset_Iic.mpr (Nat.le_ceil T)))
  exact ⟨f,hf,fun x => ⟨(h x).2,mem_iInter.mp (h x).1⟩⟩
end CircleGlobalGluing
