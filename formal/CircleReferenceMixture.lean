module

public import CircleReferenceMoments
import all CircleGaussianTracking
import all CircleReferenceMoments
import all CircleInitializationConcentration
import all CircleKernelIdentification
import Mathlib.Tactic

/-! Distribution of the finite-width interpolation reference with Gaussian
readout. Disintegrating over the hidden weights gives an exact variance
mixture, including hidden configurations with zero conditional variance. -/
public section
noncomputable section
namespace CircleReferenceMixture
open MeasureTheory ProbabilityTheory Real CircleEscapeBridge CircleInitializationConcentration
  CircleReferenceMoments CircleKernelIdentification Set
open scoped ENNReal

/-- Readout coefficient of one neuron after projecting the interpolation
reference onto the population mean. -/
def loading (N m : ℕ) (b : ℝ) (h : Hidden m) (j : Fin m) :=
  (sqrt m)*(m:ℝ)⁻¹ * CircleReferenceMoments.coeff N b (h 0 j,h 1 j)

def mixingVariance (N m : ℕ) (b : ℝ) (h : Hidden m) :=
  ∑ j, (loading N m b h j)^2

private theorem loading_meas (N m : ℕ) (b : ℝ) (j : Fin m) :
    Measurable fun h => loading N m b h j := by
  unfold loading CircleReferenceMoments.coeff CircleReferenceMoments.gridFeature
    CircleReferenceMoments.phi populationFeature projection
  fun_prop

theorem centered_reference (N m : ℕ) (hm : 0<m) (b : ℝ) (ω : Seed m) :
    reference N m b ω - b =
      linearReadout (loading N m b ((splitLayer m ω).2)) ((splitLayer m ω).1) := by
  rw [CircleReferenceMoments.reference_average _ _ hm b]
  dsimp only
  rw [add_sub_cancel_left]
  unfold sampleAverage linearReadout loading
  rw [← mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (ω (j,0) * _) = (_ * CircleReferenceMoments.coeff N b (ω (j,1),ω (j,2))) * ω (j,0)
  ring

/-- Equality of the two probability measures on every Borel event, under
the original Gaussian seed law, at every positive width. -/
theorem mixture (N m : ℕ) (hm : 0<m) (b : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    seedLaw m {ω | reference N m b ω-b ∈ A} =
      ∫⁻ h, gaussianReal 0 (mixingVariance N m b h).toNNReal A ∂hiddenLaw m := by
  let B := {p : Layer m × Hidden m | linearReadout (loading N m b p.2) p.1 ∈ A}
  have hB : MeasurableSet B :=
    hA.preimage (Finset.measurable_fun_sum _ fun j _ =>
      ((loading_meas N m b j).comp measurable_snd).mul ((measurable_pi_apply j).comp measurable_fst))
  have pre : {ω | reference N m b ω-b ∈ A} = (splitLayer m) ⁻¹' B := by
    ext ω
    simpa only [mem_ofPred_eq,mem_preimage,B] using
      (show reference N m b ω - b ∈ A ↔ _ from (centered_reference N m hm b ω) ▸ Iff.rfl)
  rw [pre,(CircleInitializationConcentration.split_preserving m).measure_preimage hB.nullMeasurableSet,
      Measure.prod_apply_symm hB]
  apply lintegral_congr
  intro h
  exact (linearReadout_law (loading N m b h)).measure_eq (p:=fun x => x ∈ A) hA

/-- Pull the conditional variance back to the full seed space to express its
fluctuation as an iid empirical variance. -/
def squaredFeature (N : ℕ) (b : ℝ) (z : Atom) := (CircleReferenceMoments.coeff N b (z 1,z 2))^2

private theorem squared_mem (N : ℕ) (b : ℝ) : MemLp (squaredFeature N b) 2 atomLaw := by
  have h := (CircleReferenceMoments.coeff_mem N b 4).comp_measurePreserving
    (measurePreserving_snd.comp CircleReferenceMoments.split_preserving)
  norm_num at h
  exact CircleGaussianTracking.square_mem h

theorem variance_as_average (N m : ℕ) (hm : 0<m) (b : ℝ) (ω : Seed m) :
    mixingVariance N m b (splitLayer m ω).2 = sampleAverage (squaredFeature N b) ω := by
  unfold mixingVariance loading sampleAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (sqrt (m:ℝ)*(m:ℝ)⁻¹*CircleReferenceMoments.coeff N b (ω (j,1),ω (j,2)))^2 = _*(_^2)
  rw [mul_pow,mul_pow,sq_sqrt (Nat.cast_nonneg m)]
  field_simp

/-- The conditional variance of the unscaled reference concentrates at the
exact inverse-width rate; the numerator is a single-neuron constant. -/
theorem variance_of_mixing (N m : ℕ) (hm : 0<m) (b : ℝ) :
    variance (fun ω => mixingVariance N m b (splitLayer m ω).2) (seedLaw m) =
      variance (squaredFeature N b) atomLaw / m := by
  simp_rw [variance_as_average N m hm b]
  exact average_variance hm (squared_mem N b)

end CircleReferenceMixture
