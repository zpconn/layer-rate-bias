module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleEscapeBridge
import Mathlib.MeasureTheory.Integral.Prod

/-! Three independent Gaussian readout layers can share one hidden layer.
Mixing readouts along any unit direction has the original full Gaussian seed law. -/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set
open CircleEscapeBridge CircleInitializationConcentration
open scoped ENNReal

set_option maxHeartbeats 1200000

namespace CircleReadoutMixing

abbrev Triple (m : ℕ) := (Fin 3 → Layer m) × Hidden m

def tripleLaw (m : ℕ) : Measure (Triple m) :=
  (Measure.pi (fun _ : Fin 3 => layerLaw m)).prod (hiddenLaw m)

instance (m : ℕ) : IsProbabilityMeasure (tripleLaw m) := by
  unfold tripleLaw hiddenLaw
  infer_instance

def mixedSeed {m : ℕ} (u : Atom) (p : Triple m) : Seed m :=
  (splitLayer m).symm ((fun j => ∑ i, u i * p.1 i j), p.2)

@[simp] theorem split_mixedSeed {m : ℕ} (u : Atom) (p : Triple m) :
    splitLayer m (mixedSeed u p) = ((fun j => ∑ i, u i * p.1 i j), p.2) :=
  (splitLayer m).apply_symm_apply _

@[simp] theorem mixedSeed_zero {m : ℕ} (u : Atom) (p : Triple m) (j : Fin m) :
    mixedSeed u p (j,0) = ∑ i, u i * p.1 i j := by
  exact congrArg (fun s : Layer m × Hidden m => s.1 j) (split_mixedSeed u p)

@[simp] theorem mixedSeed_one {m : ℕ} (u : Atom) (p : Triple m) (j : Fin m) :
    mixedSeed u p (j,1) = p.2 0 j := by
  exact congrArg (fun s : Layer m × Hidden m => s.2 0 j) (split_mixedSeed u p)

@[simp] theorem mixedSeed_two {m : ℕ} (u : Atom) (p : Triple m) (j : Fin m) :
    mixedSeed u p (j,2) = p.2 1 j := by
  exact congrArg (fun s : Layer m × Hidden m => s.2 1 j) (split_mixedSeed u p)

private def layers (m : ℕ) : Seed m ≃ᵐ (Fin 3 → Layer m) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 × Fin m => ℝ)
    (Equiv.prodComm (Fin m) (Fin 3))).trans (MeasurableEquiv.curry (Fin 3) (Fin m) ℝ)

private theorem layers_preserving (m : ℕ) : MeasurePreserving (layers m) (seedLaw m)
    (Measure.pi (fun _ : Fin 3 => layerLaw m)) := by
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin 3) (Fin m) ℝ)
      (Measure.pi (fun _ : Fin 3 × Fin m => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin 3 => layerLaw m)) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable,?_⟩
    simpa [Measure.infinitePi_eq_pi, layerLaw] using
      Measure.infinitePi_map_curry (fun (_ : Fin 3) (_ : Fin m) => gaussianReal 0 1)
  exact hc.comp (measurePreserving_piCongrLeft (fun _ : Fin 3 × Fin m => gaussianReal 0 1)
    (Equiv.prodComm (Fin m) (Fin 3)))

theorem mixedSeed_measurable (m : ℕ) :
    Measurable (fun q : Atom × Triple m => mixedSeed q.1 q.2) := by
  apply (splitLayer m).symm.measurable.comp
  exact (measurable_pi_iff.2 fun _ => by fun_prop).prodMk (measurable_snd.comp measurable_snd)

/-- A fixed unit direction preserves the joint law of every readout and hidden coordinate. -/
theorem mixed_preserving (m : ℕ) (u : Atom) (hu : ∑ i, u i^2 = 1) :
    MeasurePreserving (mixedSeed u) (tripleLaw m) (seedLaw m) := by
  have row : MeasurePreserving (linearReadout u) atomLaw (gaussianReal 0 1) := by
    refine ⟨by unfold linearReadout; fun_prop, ?_⟩
    simpa only [atomLaw,layerLaw,hu, Real.toNNReal_one] using (linearReadout_law u).map_eq
  have push := measurePreserving_pi (fun _ : Fin m => atomLaw)
    (fun _ : Fin m => gaussianReal 0 1) (fun _ => row)
  have h : MeasurePreserving (fun p : Fin 3 → Layer m => fun j => ∑ i, u i * p i j)
      (Measure.pi (fun _ : Fin 3 => layerLaw m)) (layerLaw m) :=
    push.comp ((curry_preserving m).comp ((layers_preserving m).symm (layers m)))
  exact ((split_preserving m).symm (splitLayer m)).comp (h.prod (MeasurePreserving.id (hiddenLaw m)))

/-- Average first over three Gaussian readouts with a shared hidden layer, then
over the independent mixing direction. The direction law may be any probability law. -/
theorem mix_fubini {Ω : Type*} [MeasurableSpace Ω] (m : ℕ) (σ : Measure Ω)
    [IsProbabilityMeasure σ] (u : Ω → Atom) (hu : Measurable u)
    (unit : ∀ x, ∑ i, u x i^2 = 1) (A : Set (Seed m)) (hA : MeasurableSet A) :
    seedLaw m A = ∫⁻ p, σ {x | mixedSeed (u x) p ∈ A} ∂tripleLaw m := by
  let B : Set (Triple m × Ω) := {q | mixedSeed (u q.2) q.1 ∈ A}
  have hm : Measurable (fun q : Triple m × Ω => (u q.2,q.1)) :=
    (hu.comp measurable_snd).prodMk measurable_fst
  have hB : MeasurableSet B := ((mixedSeed_measurable m).comp hm) hA
  change seedLaw m A = ∫⁻ p, σ ((Prod.mk p) ⁻¹' B) ∂tripleLaw m
  rw [← Measure.prod_apply hB, Measure.prod_apply_symm hB]
  have sec (x : Ω) : tripleLaw m ((fun p => (p,x)) ⁻¹' B) = seedLaw m A :=
    (mixed_preserving m (u x) (unit x)).measure_preimage hA.nullMeasurableSet
  simp_rw [sec]
  simp

theorem mix_fubini_real {Ω : Type*} [MeasurableSpace Ω] (m : ℕ) (σ : Measure Ω)
    [IsProbabilityMeasure σ] (u : Ω → Atom) (hu : Measurable u)
    (unit : ∀ x, ∑ i, u x i^2 = 1) (A : Set (Seed m)) (hA : MeasurableSet A) :
    (seedLaw m).real A = ∫ p, σ.real {x | mixedSeed (u x) p ∈ A} ∂tripleLaw m := by
  let B : Set (Triple m × Ω) := {q | mixedSeed (u q.2) q.1 ∈ A}
  have hm : Measurable (fun q : Triple m × Ω => (u q.2,q.1)) :=
    (hu.comp measurable_snd).prodMk measurable_fst
  have hB : MeasurableSet B := ((mixedSeed_measurable m).comp hm) hA
  have h := (measurable_measure_prodMk_left (ν := σ) hB).aemeasurable (μ := tripleLaw m)
  change (seedLaw m A).toReal = ∫ p, (σ ((Prod.mk p) ⁻¹' B)).toReal ∂tripleLaw m
  rw [integral_toReal h (ae_of_all _ fun _ => measure_lt_top _ _), mix_fubini m σ u hu unit A hA]
  rfl

end CircleReadoutMixing
