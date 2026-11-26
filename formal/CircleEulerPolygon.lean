module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

/-! Euler polygons with anchors in the actual velocity fibers. The slope only
requires a choice at countably many states. Integrating the step function gives
the same interpolation at the lattice times and a uniform Lipschitz bound. -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology

namespace CircleEulerPolygon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def vertex (v : E → E) (x : E) (h : ℝ) : ℕ → E
  | 0 => x
  | k+1 => vertex v x h k + h • v (vertex v x h k)

/-- A bounded nonempty velocity field has Euler polygons on the positive real
half-line. At a.e. time they follow a velocity in the fiber of their preceding
mesh vertex. The velocity choice need not be measurable as a function of state. -/
theorem polygons (F : E → Set E) (exists_mem : ∀ y, (F y).Nonempty)
    (L : ℝ≥0) (bound : ∀ y, ∀ v ∈ F y, ‖v‖ ≤ L) (x : E) :
    ∃ (p : ℕ → C(ℝ≥0,E)) (anchor : ℕ → ℝ≥0 → E),
      (∀ n, p n 0 = x) ∧ (∀ n, LipschitzWith L (p n)) ∧
      (∀ n t, dist (anchor n t) (p n t) ≤ (L:ℝ)/(n+1)) ∧
      ∀ n, ∀ᵐ t : ℝ, 0 < t → ∃ v ∈ F (anchor n t.toNNReal),
        HasDerivAt (fun s : ℝ => p n s.toNNReal) v t := by
  classical
  choose v hv using exists_mem
  have oneMesh (h : ℝ) (hh : 0 < h) : ∃ (p : C(ℝ≥0,E)) (q : ℝ≥0 → E),
      p 0 = x ∧ LipschitzWith L p ∧ (∀ t, dist (q t) (p t) ≤ (L:ℝ)*h) ∧
      ∀ᵐ t : ℝ, 0 < t → ∃ w ∈ F (q t.toNNReal),
        HasDerivAt (fun s : ℝ => p s.toNNReal) w t := by
    let z := vertex v x h
    let idx (t : ℝ) := ⌊t/h⌋₊
    let speed (t : ℝ) := v (z (idx t))
    have hs : Measurable speed :=
      (measurable_from_nat (f := fun k : ℕ => v (z k))).comp (Nat.measurable_floor.comp (measurable_id.div_const h))
    have hb (t : ℝ) : ‖speed t‖ ≤ L := bound _ _ (hv _)
    have hint (a b : ℝ) : IntervalIntegrable speed volume a b :=
      (intervalIntegrable_const (c := (L:ℝ))).mono_fun' hs.aestronglyMeasurable
        (Eventually.of_forall hb)
    let P (t : ℝ) := x + ∫ s in (0:ℝ)..t, speed s
    have inc (a b : ℝ) : P b - P a = ∫ s in a..b, speed s := by
      dsimp only [P]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)]
      abel
    have lip : LipschitzWith L P := by
      apply LipschitzWith.of_dist_le_mul
      intro b a
      rw [dist_eq_norm, inc, Real.dist_eq]
      exact intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hb s
    have lattice (k : ℕ) : P ((k:ℝ)*h) = z k := by
      induction k with
      | zero => simp [P, z, vertex]
      | succ k ih =>
        let a := (k:ℝ)*h
        let b := ((k:ℝ)+1)*h
        have hab : a ≤ b := by dsimp [a,b]; linarith
        have hconst : (∫ t in a..b, speed t) = (∫ _ in a..b, v (z k)) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [volume.ae_ne b] with t ht hI
          rw [uIoc_of_le hab] at hI
          have hlo : (k:ℝ) ≤ t/h := (le_div_iff₀ hh).mpr hI.1.le
          have hhi : t/h < (k:ℝ)+1 := (div_lt_iff₀ hh).mpr (lt_of_le_of_ne hI.2 ht)
          have hi : idx t = k := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) hlo)).mpr ⟨hlo,hhi⟩
          simp [speed, hi]
        rw [intervalIntegral.integral_const] at hconst
        have d := inc a b
        have ba : b - a = h := by dsimp [b,a]; ring
        rw [hconst, ba] at d
        have : P b = P a + h • v (z k) := by rw [← d]; abel
        simpa [b,a,ih,z,vertex] using this
    let p : C(ℝ≥0,E) := ⟨fun t => P t, lip.continuous.comp NNReal.continuous_coe⟩
    let q (t : ℝ≥0) := z (idx t)
    refine ⟨p,q,?_,?_,?_,?_⟩
    · change P 0 = x
      simp [P]
    · exact LipschitzWith.of_dist_le_mul fun a b => lip.dist_le_mul a.val b.val
    · intro t
      let k := idx t
      have hlo : (k:ℝ)*h ≤ t := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg t.2 hh.le))
      have hu : (t:ℝ) < ((k:ℝ)+1)*h := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one _)
      change dist (z k) (P t) ≤ _
      rw [← lattice]
      refine (lip.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.2)
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith
    · have localI : LocallyIntegrable speed volume := by
        intro t
        exact ⟨Ioc (t-1) (t+1), Ioc_mem_nhds (by linarith) (by linarith),
          (hint (t-1) (t+1)).1⟩
      filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral localI] with t ht pos
      refine ⟨speed t, ?_, ((ht 0).const_add x).congr_of_eventuallyEq ?_⟩
      · simpa only [q,Real.coe_toNNReal _ pos.le] using hv (z (idx t))
      · filter_upwards [Ioi_mem_nhds pos] with s hs'
        change P (s.toNNReal : ℝ) = P s
        rw [Real.coe_toNNReal _ hs'.le]
  choose p q hp hl hq hd using (fun n : ℕ => oneMesh (1/((n:ℝ)+1)) (by positivity))
  exact ⟨p,q,hp,hl,fun n t => (hq n t).trans_eq (by ring),hd⟩
end CircleEulerPolygon
