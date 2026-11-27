module
public import CircleWeightedStep
import all CircleWeightedStep
import all CircleTangentDrift
import all CircleFlowPath
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Changing hidden coordinates by a positive multiplier conjugates ordinary
descent for the rescaled network to layer-weighted descent in physical coordinates. -/
@[expose] public section
noncomputable section
namespace CircleReparametrization
open CircleFlowPath CircleTangentDrift CircleWeightedStep
open MeasureTheory Set
variable {N m : ℕ}

def physical (b : ℝ) (z : State m) : State m := fun p => rate b p * z p

private theorem pre_physical (b : ℝ) (z : State m) (j : Fin m) (x : ℝ × ℝ) :
    pre (physical b z) j x = b * pre z j x := by
  simp [pre, physical, rate]; ring

private theorem relu_mul {b : ℝ} (hb : 0 < b) (v : ℝ) : max (b*v) 0 = b*max v 0 := by
  simpa using (mul_max_of_nonneg v 0 hb.le).symm

theorem output_physical {b : ℝ} (hb : 0 < b) (c : ℝ) (z : State m) (x : ℝ × ℝ) :
    output c (physical b z) x = output (b*c) z x := by
  rw [output, output, mul_comm b c, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pre_physical, relu_mul hb]
  simp [physical, rate]; ring

private theorem row_physical {b : ℝ} (hb : 0 < b) (c : ℝ) (z : State m) (x : ℝ × ℝ)
    (g : Fin m → ℝ) (p : Coord m) :
    row (b*c) z x g p = rate b p * row c (physical b z) x g p := by
  rcases p with ⟨j,k⟩
  fin_cases k <;> simp [row, pre_physical, relu_mul hb, rate, physical] <;> ring

private theorem velocity_physical {b : ℝ} (hb : 0 < b) (c : ℝ) (z : State m)
    (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (g : Fin N → Fin m → ℝ) :
    physical b (velocity 1 (fun i => row (b*c) z (x i) (g i)) (residual x y (b*c) z)) =
      velocity (b^2) (fun i => row c (physical b z) (x i) (g i)) (residual x y c (physical b z)) := by
  funext p
  simp only [physical, velocity, gradient, CircleFlowPath.residual, output_physical hb, row_physical hb,
    rate, ite_self, neg_one_mul]
  split <;> simp_all [← Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc, sq]

/-- One plain GD update in (a,v), with normalization b/√m, gives the
weighted physical step with hidden multiplier b² under w=bv. -/
theorem gd_step {b : ℝ} (hb : 0 < b) (η : ℝ) (N : ℕ) (z : State m) :
    let c := 1/Real.sqrt m
    let v := velocity 1 (fun i => row (b*c) z (circleInput N i) (startGates z i))
      (residual (circleInput N) (circleLabel N) (b*c) z)
    physical b (fun p => z p + η*v p) = segment (b^2) N (physical b z) η := by
  intro c v
  have gate : startGates (N := N) (physical b z) = startGates z := by
    funext i j
    simp [startGates, actualGate, pre_physical, mul_pos_iff_of_pos_left hb]
  have vel : physical b v = direction (b^2) N (physical b z) := by
    rw [direction, gate]
    exact velocity_physical hb c z _ _ _
  funext p
  rw [CircleWeightedStep.segment, ← vel]
  simp [physical]; ring

/-- The same transformation carries the admissible gate velocities on
almost every time slice of a solution to the physical flow. -/
theorem flow {b : ℝ} (hb : 0 < b) {c T : ℝ} {z : ℝ → State m}
    {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ} (F : IsFlow x y (b*c) 1 T z) :
    IsFlow x y c (b^2) T (fun t => physical b (z t)) := by
  refine ⟨fun p => (F.ac p).const_mul (rate b p), ?_⟩
  filter_upwards [F.compatible] with t ht mem
  obtain ⟨g, hg, hd⟩ := ht mem
  refine ⟨g, ?_, ?_⟩
  · intro i j
    simpa [Admissible, pre_physical, mul_pos_iff_of_pos_left hb, mul_neg_iff, hb, hb.not_gt] using hg i j
  · intro p
    rw [← velocity_physical hb]
    exact (hd p).const_mul (rate b p)

private theorem inverse_physical {b : ℝ} (hb : b ≠ 0) (z : State m) :
    physical b⁻¹ (physical b z) = z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [physical, rate, h, hb]

/-- Positive scaling gives a one-to-one correspondence of admissible gate flows. -/
theorem flow_iff {b : ℝ} (hb : 0 < b) {c T : ℝ} {z : ℝ → State m}
    {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ} :
    IsFlow x y (b*c) 1 T z ↔ IsFlow x y c (b^2) T (fun t => physical b (z t)) := by
  refine ⟨flow hb, fun F => ?_⟩
  constructor
  · intro p
    have a := (F.ac p).const_mul (rate b⁻¹ p)
    change AbsolutelyContinuousOnInterval (fun t => physical b⁻¹ (physical b (z t)) p) 0 T at a
    simpa only [inverse_physical hb.ne'] using a
  · filter_upwards [F.compatible] with t ht mem
    obtain ⟨g, hg, hd⟩ := ht mem
    refine ⟨g, ?_, ?_⟩
    · intro i j
      simpa [Admissible, pre_physical, mul_pos_iff_of_pos_left hb, mul_neg_iff, hb, hb.not_gt] using hg i j
    · intro p
      have h := (hd p).const_mul (rate b⁻¹ p)
      rw [← velocity_physical hb] at h
      change HasDerivAt (fun t => physical b⁻¹ (physical b (z t)) p)
        (physical b⁻¹ (physical b _) p) t at h
      simpa only [inverse_physical hb.ne'] using h

/-- Undoing the coordinate transformation maps standard Gaussian coordinates to
independent Gaussians with variance one for readouts and 1/b² for hidden coordinates. -/
theorem initialization (m : ℕ) (b : ℝ) :
    (CircleEscapeBridge.seedLaw m).map (physical b⁻¹) =
      Measure.pi (fun p : Coord m => ProbabilityTheory.gaussianReal 0
        (if p.2 = 0 then 1 else ⟨(b⁻¹)^2, sq_nonneg _⟩)) := by
  let f (p : Coord m) : ℝ → ℝ := fun u => rate b⁻¹ p * u
  have hf (p : Coord m) : Measurable (f p) := by unfold f; fun_prop
  have hmap (p : Coord m) : (ProbabilityTheory.gaussianReal 0 1).map (f p) =
      ProbabilityTheory.gaussianReal 0 (if p.2 = 0 then 1 else ⟨(b⁻¹)^2, sq_nonneg _⟩) := by
    rw [show f p = (rate b⁻¹ p * ·) by rfl, ProbabilityTheory.gaussianReal_map_const_mul]
    by_cases h : p.2 = 0
    · simp [rate, h]
    · simp [rate, h]
      rfl
  let (p : Coord m) : IsProbabilityMeasure ((ProbabilityTheory.gaussianReal 0 1).map (f p)) := by
    rw [hmap]; infer_instance
  change (Measure.pi (fun _ : Coord m => ProbabilityTheory.gaussianReal 0 1)).map
    (fun z p => f p (z p)) = _
  exact (Measure.pi_map_pi (fun i => (hf i).aemeasurable)).trans (by simp_rw [hmap])

end CircleReparametrization
