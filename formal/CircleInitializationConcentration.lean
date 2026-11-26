module

public import CircleSeedIntegrability
public import CircleGaussianMargin
import all CircleGaussianMargin
public import CircleGridSpectrum
import all CircleKernelIdentification
import all CircleGridSpectrum
public import CircleTangentDrift
import all CircleTangentDrift
public import CircleFlowPath
import all CircleFlowPath
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.ProductMeasure
import all CircleEscape
import all CircleEscapeBridge
import all CircleSeedIntegrability
import Mathlib.Tactic

/-! Actual finite-width Gaussian tangent Gram concentration for simultaneous
training of the output and input weights on the circle. All expectations use
the original three independent standard normal coordinates per neuron. -/

public section
noncomputable section
namespace CircleInitializationConcentration
open MeasureTheory ProbabilityTheory CircleEscape CircleEscapeBridge

abbrev Atom := Fin 3 → ℝ

def atomLaw : Measure Atom := Measure.pi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure atomLaw := by unfold atomLaw; infer_instance

def tangentAtom (x y : ℂ) (z : Atom) : ℝ :=
  let w : ℂ := ⟨z 1, z 2⟩
  feature w x * feature w y + z 0 ^ 2 * gate w x * gate w y * inner ℝ x y

def populationEntry (x y : ℂ) : ℝ := ∫ z, tangentAtom x y z ∂atomLaw

def gramEntry {m : ℕ} (x y : ℂ) (ω : Seed m) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, tangentAtom x y (fun k => ω (j,k))

theorem gramEntry_initial {m : ℕ} (x y : ℂ) (ω : Seed m) :
    gramEntry x y ω = (m : ℝ)⁻¹ * ∑ j,
      (feature ((initial ω).w j) x * feature ((initial ω).w j) y +
       ((initial ω).a j)^2 * gate ((initial ω).w j) x * gate ((initial ω).w j) y *
         inner ℝ x y) := by rfl

theorem tangentAtom_measurable (x y : ℂ) : Measurable (tangentAtom x y) := by
  let w : Atom → ℂ := fun z => ⟨z 1, z 2⟩
  have hw : Measurable w := by
    have h : Measurable (fun z : Atom => (z 1,z 2)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact Complex.equivRealProdCLM.symm.continuous.measurable.comp h
  apply ((CircleSeedIntegrability.feature_meas hw x).mul
    (CircleSeedIntegrability.feature_meas hw y)).add
  exact ((((measurable_pi_apply 0).pow_const 2).mul
    (CircleSeedIntegrability.gate_meas hw x)).mul
    (CircleSeedIntegrability.gate_meas hw y)).mul measurable_const

private theorem gate_cap (w x : ℂ) : |gate w x| ≤ 1 := by unfold gate; split <;> norm_num

private theorem atom_cap (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (z : Atom) :
    |tangentAtom x y z| ≤ z 0^2 + z 1^2 + z 2^2 := by
  let w : ℂ := ⟨z 1, z 2⟩
  have h₁ := CircleSeedIntegrability.feature_cap w x hx
  have h₂ := CircleSeedIntegrability.feature_cap w y hy
  have hf : |feature w x * feature w y| ≤ ‖w‖^2 := by
    rw [abs_mul, sq]; exact mul_le_mul h₁ h₂ (abs_nonneg _) (norm_nonneg _)
  have hxy : |inner ℝ x y| ≤ 1 := (abs_real_inner_le_norm x y).trans (by
    simpa using mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  have hg : |z 0^2 * gate w x * gate w y * inner ℝ x y| ≤ z 0^2 := by
    simp only [abs_mul, abs_of_nonneg (sq_nonneg (z 0))]
    calc
      _ ≤ z 0^2 * 1 * 1 * 1 := by gcongr <;> exact gate_cap _ _
      _ = _ := by ring
  apply (abs_add_le _ _).trans
  have hn : ‖w‖^2 = z 1^2 + z 2^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; dsimp [w]; ring
  change |feature w x * feature w y| + |z 0 ^ 2 * gate w x * gate w y * inner ℝ x y| ≤ _
  linarith

private theorem coord_pow (k : Fin 3) (n : ℕ) :
    Integrable (fun z : Atom => z k ^ n) atomLaw := by
  have h : MemLp (fun z : Atom => z k) (n : ENNReal) atomLaw :=
    (memLp_id_gaussianReal' (μ:=0) (v:=1) n (by simp)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) k)
  apply h.integrable_norm_pow'.mono' ((measurable_pi_apply k).pow_const n).aestronglyMeasurable
  exact ae_of_all _ fun z => by simp [Real.norm_eq_abs]

private theorem envelope_integrable : Integrable
    (fun z : Atom => 3 * (z 0 ^ 4 + z 1 ^ 4 + z 2 ^ 4)) atomLaw :=
  (((coord_pow 0 4).add (coord_pow 1 4)).add (coord_pow 2 4)).const_mul 3

private theorem atom_sq_cap (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (z : Atom) :
    tangentAtom x y z ^ 2 ≤ 3 * (z 0^4 + z 1^4 + z 2^4) := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (atom_cap x y hx hy z) 2
  rw [sq_abs] at h
  nlinarith [sq_nonneg (z 0^2-z 1^2),sq_nonneg (z 0^2-z 2^2),sq_nonneg (z 1^2-z 2^2)]

theorem tangentAtom_memLp (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    MemLp (tangentAtom x y) 2 atomLaw := by
  apply (memLp_two_iff_integrable_sq (tangentAtom_measurable x y).aestronglyMeasurable).2
  refine envelope_integrable.mono' ?_ (ae_of_all _ fun z => ?_)
  · exact ((tangentAtom_measurable x y).pow_const 2).aestronglyMeasurable
  · change ‖tangentAtom x y z ^ 2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact atom_sq_cap x y hx hy z

/-- Fourth moment from the standard Gaussian moment generating function. -/
theorem gaussian_fourth : ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1 = 3 := by
  let g : ℝ → ℝ := fun t => Real.exp (t^2/2)
  have dg (t : ℝ) : HasDerivAt g (t*g t) t := by
    have h := (((hasDerivAt_id t).pow 2).div_const 2).exp
    convert h using 1 <;> dsimp [g]; ring
  have d1 : deriv g = fun t => t*g t := funext fun t => (dg t).deriv
  have d2 : deriv (fun t => t*g t) = fun t => (1+t^2)*g t := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (dg t).differentiableAt, deriv_id'', (dg t).deriv]; ring
  have d3 : deriv (fun t : ℝ => (1+t^2)*g t) = fun t => (3*t+t^3)*g t := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (dg t).differentiableAt, deriv_fun_add (by fun_prop) (by fun_prop),
      deriv_fun_pow (by fun_prop), (dg t).deriv]; simp; ring
  have d4 := ((((hasDerivAt_const (0:ℝ) (3:ℝ)).mul (hasDerivAt_id (0:ℝ))).add
    ((hasDerivAt_id (0:ℝ)).pow 3)).mul (dg 0)).deriv
  have hm : mgf (fun z : ℝ => z) (gaussianReal 0 1) = g := by
    rw [mgf_fun_id_gaussianReal]; ext t; simp [g]
  change ∫ z, ((fun t : ℝ => t)^4) z ∂gaussianReal 0 1 = 3
  rw [← iteratedDeriv_mgf_zero (X := fun z : ℝ => z) (by simp), hm, iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv (deriv g))) 0 = 3
  rw [d1,d2,d3]
  change deriv (((fun _ : ℝ => 3) * id + id^3) * g) 0 = 3
  simpa [g] using d4

private theorem coord_fourth (k : Fin 3) : ∫ z : Atom, z k ^ 4 ∂atomLaw = 3 := by
  have h := (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) k).map_eq
  rw [← gaussian_fourth, ← h, integral_map (measurable_pi_apply k).aemeasurable (by fun_prop)]
  rfl

theorem tangentAtom_variance_le (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    variance (tangentAtom x y) atomLaw ≤ 27 := by
  apply (variance_le_expectation_sq (tangentAtom_measurable x y).aestronglyMeasurable).trans
  have h := integral_mono (tangentAtom_memLp x y hx hy).integrable_sq
    envelope_integrable (atom_sq_cap x y hx hy)
  have h01 : Integrable (fun z : Atom => z 0 ^ 4 + z 1 ^ 4) atomLaw := (coord_pow 0 4).add (coord_pow 1 4)
  rw [integral_const_mul,integral_add h01 (coord_pow 2 4),
    integral_add (coord_pow 0 4) (coord_pow 1 4),coord_fourth,coord_fourth,coord_fourth] at h
  norm_num at h
  exact h

private def currySeed (m : ℕ) := MeasurableEquiv.curry (Fin m) (Fin 3) ℝ

private theorem curry_preserving (m : ℕ) : MeasurePreserving (currySeed m) (seedLaw m)
    (Measure.pi (fun _ : Fin m => atomLaw)) := by
  refine ⟨(currySeed m).measurable, ?_⟩
  simpa [Measure.infinitePi_eq_pi,seedLaw,atomLaw,currySeed] using
    Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : Fin 3) => gaussianReal 0 1)

private theorem neuron_preserving (m : ℕ) (j : Fin m) :
    MeasurePreserving (fun (ω : Seed m) k => ω (j,k)) (seedLaw m) atomLaw :=
  (measurePreserving_eval (fun _ : Fin m => atomLaw) j).comp (curry_preserving m)

private theorem neuron_mem {m : ℕ} (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (j : Fin m) :
    MemLp (fun ω : Seed m => tangentAtom x y (fun k => ω (j,k))) 2 (seedLaw m) :=
  (tangentAtom_memLp x y hx hy).comp_measurePreserving (neuron_preserving m j)

theorem gramEntry_mem {m : ℕ} (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    MemLp (gramEntry (m:=m) x y) 2 (seedLaw m) :=
  (memLp_finsetSum _ (fun j _ => neuron_mem x y hx hy j)).const_mul _

theorem gramEntry_expectation {m : ℕ} (hm : 0 < m) (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∫ ω : Seed m, gramEntry x y ω ∂seedLaw m = populationEntry x y := by
  simp only [gramEntry, integral_const_mul, integral_finsetSum _
    (fun j _ => (neuron_mem x y hx hy j).integrable (by norm_num))]
  have hi (j : Fin m) : ∫ ω : Seed m, tangentAtom x y (fun k => ω (j,k)) ∂seedLaw m = populationEntry x y := by
    rw [populationEntry, ← (neuron_preserving m j).map_eq, integral_map
      (neuron_preserving m j).aemeasurable (tangentAtom_measurable x y).aestronglyMeasurable]
  simp [hi, hm.ne']

theorem gramEntry_variance {m : ℕ} (hm : 0 < m) (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    variance (gramEntry (m:=m) x y) (seedLaw m) = variance (tangentAtom x y) atomLaw / m := by
  let F : (Fin m → Atom) → ℝ := ∑ j, fun ω => tangentAtom x y (ω j)
  have hF (ω : Fin m → Atom) : F ω = ∑ j, tangentAtom x y (ω j) := by simp [F,Finset.sum_apply]
  have hs : Measurable F := by
    simp_rw [show F = _ from funext hF]
    exact Finset.measurable_fun_sum _ fun j _ => (tangentAtom_measurable x y).comp (measurable_pi_apply j)
  have hf := (curry_preserving m).variance_fun_comp hs.aemeasurable
  have hv := variance_sum_pi (μ := fun _ : Fin m => atomLaw)
    (X := fun _ => tangentAtom x y) (fun _ => tangentAtom_memLp x y hx hy)
  rw [show gramEntry (m:=m) x y = (fun ω => (m:ℝ)⁻¹ * F ((currySeed m) ω)) by
    ext ω; rw [hF]; rfl]
  rw [variance_const_mul,hf,show variance F _ = _ from hv]
  simp [div_eq_mul_inv]
  field_simp

/-- Expected squared error about the population entry, with the actual neuron law. -/
theorem entry_mse {m : ℕ} (hm : 0 < m) (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∫ ω : Seed m, (gramEntry x y ω - populationEntry x y)^2 ∂seedLaw m ≤ 27 / m := by
  rw [← gramEntry_expectation hm x y hx hy,
    ← variance_eq_integral (gramEntry_mem (m:=m) x y hx hy).aestronglyMeasurable.aemeasurable,
    gramEntry_variance hm x y hx hy]
  exact div_le_div_of_nonneg_right (tangentAtom_variance_le x y hx hy) (Nat.cast_nonneg _)

/-- Squared Frobenius norm of the fluctuation of the normalized training
operator, whose (i,j) entry is the neuron-average Gram entry divided by N. -/
def normalizedFrobeniusSq (N m : ℕ) (ω : Seed m) : ℝ :=
  ((N:ℝ)^2)⁻¹ * ∑ q : Fin N × Fin N,
    (gramEntry (gridPoint N q.1) (gridPoint N q.2) ω -
      populationEntry (gridPoint N q.1) (gridPoint N q.2))^2

private theorem grid_sq_integrable (N m : ℕ) (q : Fin N × Fin N) :
    Integrable (fun ω : Seed m => (gramEntry (gridPoint N q.1) (gridPoint N q.2) ω -
      populationEntry (gridPoint N q.1) (gridPoint N q.2))^2) (seedLaw m) :=
  ((gramEntry_mem _ _ (grid_norm _ _).le (grid_norm _ _).le).sub (memLp_const _)).integrable_sq

theorem frobenius_integrable (N m : ℕ) : Integrable (normalizedFrobeniusSq N m) (seedLaw m) :=
  (integrable_finsetSum _ (fun q _ => grid_sq_integrable N m q)).const_mul _

theorem frobenius_mse {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    ∫ ω, normalizedFrobeniusSq N m ω ∂seedLaw m ≤ 27 / m := by
  unfold normalizedFrobeniusSq
  rw [integral_const_mul, integral_finsetSum _ (fun q _ => grid_sq_integrable N m q)]
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ =>
    entry_mse hm _ _ (grid_norm N q.1).le (grid_norm N q.2).le)) (by positivity)).trans_eq ?_
  simp [Fintype.card_prod, sq]
  field_simp [hN.ne']

/-- Width-only tail probability for the full, normalized initialization Gram
on every finite nonempty equispaced grid, under the flattened Gaussian seed law. -/
theorem frobenius_concentration {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    (seedLaw m).real {ω | ε^2 ≤ normalizedFrobeniusSq N m ω} ≤ 27 / (m * ε^2) := by
  have hn : 0 ≤ᵐ[seedLaw m] normalizedFrobeniusSq N m := ae_of_all _ fun ω => by
    unfold normalizedFrobeniusSq; positivity
  have h := (mul_meas_ge_le_integral_of_nonneg hn (frobenius_integrable N m) (ε^2)).trans
    (frobenius_mse hN hm)
  rw [← div_div]
  exact (le_div_iff₀ (sq_pos_of_pos hε)).2 (by simpa [mul_comm] using h)


abbrev Layer (m : ℕ) := Fin m → ℝ
def layerLaw (m : ℕ) : Measure (Layer m) := Measure.pi (fun _ => gaussianReal 0 1)
instance (m : ℕ) : IsProbabilityMeasure (layerLaw m) := by unfold layerLaw; infer_instance

def standardEighth : ℝ := ∫ z : ℝ, z^8 ∂gaussianReal 0 1

private theorem gaussian_even_moment_succ (n : ℕ) :
    (∫ z : ℝ, z^(n+2) ∂gaussianReal 0 1) = (n+1:ℕ) * ∫ z : ℝ, z^n ∂gaussianReal 0 1 := by
  let g : ℝ → ℝ := fun t => Real.exp (t^2/2)
  have dg : deriv g = fun t => t*g t := by
    ext t
    have h := (((hasDerivAt_id t).pow 2).div_const 2).exp
    apply HasDerivAt.deriv
    convert h using 1 <;> dsimp [g]; ring
  have hm : mgf (fun z : ℝ => z) (gaussianReal 0 1) = g := by
    rw [mgf_fun_id_gaussianReal]; ext t; simp [g]
  have moment (r : ℕ) : (∫ z : ℝ, z^r ∂gaussianReal 0 1) = iteratedDeriv r g 0 := by
    rw [← hm, iteratedDeriv_mgf_zero (by simp)]
    rfl
  rw [moment,moment,iteratedDeriv_succ',dg,
    iteratedDeriv_fun_mul (by fun_prop) (show ContDiffAt ℝ (n+1) g 0 by dsimp [g]; fun_prop)]
  simp_rw [iteratedDeriv_fun_id_zero]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem standardEighth_eq : standardEighth = 105 := by
  change (∫ z : ℝ, z^(6+2) ∂gaussianReal 0 1) = 105
  rw [gaussian_even_moment_succ, show 6 = 4+2 by decide, gaussian_even_moment_succ,gaussian_fourth]
  norm_num

theorem standardEighth_nonneg : 0 ≤ standardEighth := integral_nonneg fun _ => by positivity

def linearReadout {m : ℕ} (b : Fin m → ℝ) (a : Layer m) := ∑ j, b j * a j

/-- The Gaussian conditional distribution for every deterministic feature vector,
including the zero vector. -/
theorem linearReadout_law {m : ℕ} (b : Fin m → ℝ) :
    HasLaw (linearReadout b) (gaussianReal 0 (∑ j, b j^2).toNNReal) (layerLaw m) := by
  let X (j : Fin m) (a : Layer m) := b j * a j
  have hi (j : Fin m) := gaussianReal_const_mul (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) j).hasLaw (b j)
  have hg : HasGaussianLaw (linearReadout b) (layerLaw m) :=
    iIndepFun.hasGaussianLaw_fun_sum (fun j => (hi j).hasGaussianLaw)
      (iIndepFun_pi (X := fun j (x : ℝ) => b j * x) (fun j => by fun_prop))
  have h₀ (j : Fin m) : ∫ a, X j a ∂layerLaw m = 0 := by
    have he := (hi j).integral_eq
    simpa [X, Function.eval, layerLaw] using he
  have hs (j : Fin m) : Integrable (X j) (layerLaw m) :=
    (hi j).integrable ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
  have mean : ∫ a, linearReadout b a ∂layerLaw m = 0 := by
    change ∫ a, ∑ j, X j a ∂layerLaw m = 0
    rw [integral_finsetSum _ (fun j _ => hs j)]
    simp [h₀]
  have var : variance (linearReadout b) (layerLaw m) = ∑ j, b j^2 := by
    have ht := variance_sum_pi (μ:=fun _ : Fin m => gaussianReal 0 1)
      (X := fun j (u:ℝ) => b j*u) (fun j => (memLp_id_gaussianReal' 2 (by norm_num)).const_mul (b j))
    have eq : linearReadout b = ∑ j, X j := by ext a; simp [linearReadout, X, Finset.sum_apply]
    rw [eq]
    have hv (j : Fin m) : variance (fun u : ℝ => b j*u) (gaussianReal 0 1) = b j ^ 2 := by
      simpa using (variance_const_mul (b j) id (gaussianReal 0 1))
    simpa only [X, hv,layerLaw] using ht
  exact ⟨hg.aemeasurable, by rw [hg.map_eq_gaussianReal,mean,var]⟩

theorem linearReadout_eighth {m : ℕ} (b : Fin m → ℝ) :
    ∫ a, (linearReadout b a)^8 ∂layerLaw m = (∑ j, b j^2)^4 * standardEighth := by
  let v : ℝ := ∑ j, b j^2
  have hv : 0 ≤ v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let c := Real.sqrt v
  have hc : c^2=v := Real.sq_sqrt hv
  have hl : HasLaw (fun z : ℝ => c*z) (gaussianReal 0 v.toNNReal) (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext; simp [hc, Real.toNNReal_of_nonneg hv]
  have h := (linearReadout_law b).integral_comp (f:=fun u : ℝ => u^8) (by fun_prop)
  have h' := hl.integral_comp (f:=fun u : ℝ => u^8) (by fun_prop)
  change (∫ a, (linearReadout b a)^8 ∂layerLaw m) = _ at h
  change (∫ z : ℝ, (c*z)^8 ∂gaussianReal 0 1) = _ at h'
  rw [h, ← h']
  simp_rw [mul_pow,integral_const_mul]
  change c^8 * standardEighth = v^4 * standardEighth
  rw [← hc]; ring

abbrev Hidden (m : ℕ) := Fin 2 → Layer m
def hiddenLaw (m : ℕ) := Measure.pi (fun _ : Fin 2 => layerLaw m)
private instance (m : ℕ) : IsProbabilityMeasure (hiddenLaw m) := by unfold hiddenLaw; infer_instance

def splitLayer (m : ℕ) : Seed m ≃ᵐ (Layer m × Hidden m) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 3 × Fin m => ℝ) (Equiv.prodComm (Fin m) (Fin 3))).trans
    (MeasurableEquiv.curry (Fin 3) (Fin m) ℝ)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Layer m) 0)

theorem split_preserving (m : ℕ) : MeasurePreserving (splitLayer m) (seedLaw m)
    ((layerLaw m).prod (hiddenLaw m)) := by
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin 3) (Fin m) ℝ)
      (Measure.pi (fun _ : Fin 3 × Fin m => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin 3 => layerLaw m)) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable,?_⟩
    simpa [Measure.infinitePi_eq_pi,layerLaw] using
      Measure.infinitePi_map_curry (fun (_ : Fin 3) (_ : Fin m) => gaussianReal 0 1)
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => layerLaw m) 0).comp
    (hc.comp (measurePreserving_piCongrLeft (fun _ : Fin 3 × Fin m => gaussianReal 0 1)
      (Equiv.prodComm (Fin m) (Fin 3))))

def hiddenFeature {m : ℕ} (x : ℝ × ℝ) (h : Hidden m) (j : Fin m) :=
  max (x.1 * h 0 j + x.2 * h 1 j) 0

def splitOutput {m : ℕ} (x : ℝ × ℝ) (p : Layer m × Hidden m) :=
  linearReadout (fun j => (1/Real.sqrt m)*hiddenFeature x p.2 j) p.1

theorem output_split {m : ℕ} (x : ℝ × ℝ) (z : Seed m) :
    CircleFlowPath.output (1/Real.sqrt m) z x = splitOutput x (splitLayer m z) := by
  unfold CircleFlowPath.output CircleFlowPath.pre splitOutput linearReadout
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _ = 1/Real.sqrt m * max (x.1*z (j,1) + x.2*z (j,2)) 0 * z (j,0)
  ring

theorem output_memLp_eight (m : ℕ) (x : ℝ × ℝ) :
    MemLp (fun z : Seed m => CircleFlowPath.output (1/Real.sqrt m) z x) 8 (seedLaw m) := by
  have hc (i : Fin m × Fin 3) : MemLp (fun z : Seed m => z i) 16 (seedLaw m) :=
    (memLp_id_gaussianReal' 16 (by norm_num)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m × Fin 3 => gaussianReal 0 1) i)
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro j _
  have hp : MemLp (fun z : Seed m => CircleFlowPath.pre z j x) 16 (seedLaw m) :=
    ((hc (j,1)).const_mul x.1).add ((hc (j,2)).const_mul x.2)
  have hf : MemLp (fun z : Seed m => max (CircleFlowPath.pre z j x) 0) 16 (seedLaw m) := by
    apply hp.of_le (hp.aestronglyMeasurable.sup aestronglyMeasurable_const)
    exact ae_of_all _ fun z => by
      change |max (CircleFlowPath.pre z j x) 0| ≤ |CircleFlowPath.pre z j x|
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  let _ : ENNReal.HolderTriple 16 16 8 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]; norm_num⟩
  exact (hc (j,0)).mul hf


private theorem layer_eval (m : ℕ) (j : Fin m) :
    MeasurePreserving (fun (h : Hidden m) k => h k j) (hiddenLaw m) (layerLaw 2) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) j)

private theorem hidden_eighth {m : ℕ} (x : ℝ × ℝ) (j : Fin m) :
    Integrable (fun h => hiddenFeature x h j ^ 8) (hiddenLaw m) ∧
    ∫ h, hiddenFeature x h j ^ 8 ∂hiddenLaw m ≤ (x.1^2+x.2^2)^4 * standardEighth := by
  let b : Fin 2 → ℝ := ![x.1,x.2]
  let f : Hidden m → ℝ := fun h => linearReadout b (fun k => h k j)
  have hl := (linearReadout_law b).comp (layer_eval m j).hasLaw
  have hm : MemLp f (8 : ℕ) (hiddenLaw m) := hl.memLp (memLp_id_gaussianReal' _ (by norm_num))
  have rawint : Integrable (fun h => f h ^ 8) (hiddenLaw m) := by
    simpa [Real.norm_eq_abs, (by decide : Even 8).pow_abs] using hm.integrable_norm_pow'
  have hf (h : Hidden m) : f h = x.1 * h 0 j + x.2 * h 1 j := by
    simp [f,linearReadout,b,Fin.sum_univ_two]
  have hb (h : Hidden m) : hiddenFeature x h j^8 ≤ f h^8 := by
    rw [hiddenFeature,hf]
    cases le_total (x.1 * h 0 j + x.2 * h 1 j) 0 with
    | inl he => rw [max_eq_right he, zero_pow (by decide : 8 ≠ 0)]; positivity
    | inr he => rw [max_eq_left he]
  have hk : Integrable (fun h => hiddenFeature x h j^8) (hiddenLaw m) := by
    refine rawint.mono' ?_ (ae_of_all _ fun h => ?_)
    · change AEStronglyMeasurable (fun h : Hidden m => max (x.1*h 0 j+x.2*h 1 j) 0 ^8) _
      have ev (k : Fin 2) : Measurable fun h : Hidden m => h k j :=
        (measurable_pi_apply j).comp (measurable_pi_apply k)
      exact (((((ev 0).const_mul _).add ((ev 1).const_mul _)).sup measurable_const).pow_const 8).aestronglyMeasurable
    · change ‖hiddenFeature x h j^8‖ ≤ f h^8
      rw [Real.norm_eq_abs, abs_of_nonneg ((by decide : Even 8).pow_nonneg _)]
      exact hb h
  refine ⟨hk,(integral_mono hk rawint hb).trans_eq ?_⟩
  have hd := (layer_eval m j).hasLaw.integral_comp (f:=fun a => linearReadout b a ^8)
    (show AEStronglyMeasurable _ (layerLaw 2) by
      unfold linearReadout
      exact ((Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _).pow_const 8).aestronglyMeasurable)
  change ∫ h, f h^8 ∂hiddenLaw m = _ at hd
  rw [hd, linearReadout_eighth]
  simp [b, Fin.sum_univ_two]

/-- Uniform in width. The factor preceding the universal Gaussian eighth moment
is exactly the fourth power of the squared input length. -/
theorem output_eighth_moment {m : ℕ} (hm : 0 < m) (x : ℝ × ℝ) :
    ∫ z : Seed m, (CircleFlowPath.output (1/Real.sqrt m) z x)^8 ∂seedLaw m ≤
      (x.1^2+x.2^2)^4 * standardEighth^2 := by
  let g := fun p : Layer m × Hidden m => splitOutput x p ^8
  have hi : Integrable g ((layerLaw m).prod (hiddenLaw m)) := by
    apply ((split_preserving m).integrable_comp_emb (splitLayer m).measurableEmbedding).1
    have h : MemLp (fun z : Seed m => CircleFlowPath.output (1/Real.sqrt m) z x)
        (8:ℕ) (seedLaw m) := output_memLp_eight m x
    simpa [Function.comp_def,g,← output_split,Real.norm_eq_abs,(by decide : Even 8).pow_abs]
      using h.integrable_norm_pow'
  have eq : ∫ z : Seed m, (CircleFlowPath.output (1/Real.sqrt m) z x)^8 ∂seedLaw m =
      ∫ h, ∫ a, g (a,h) ∂layerLaw m ∂hiddenLaw m := by
    rw [← integral_prod_symm g hi, ← (split_preserving m).integral_comp' g]
    exact integral_congr_ae (ae_of_all _ fun z => by exact congrArg (fun t : ℝ => t^8) (output_split x z))
  let V (h : Hidden m) := ∑ j, ((1/Real.sqrt m)*hiddenFeature x h j)^2
  have hs : 0 < (m:ℝ) := by exact_mod_cast hm
  have hnorm : (1/Real.sqrt m)^2 = (m:ℝ)⁻¹ := by rw [div_pow, Real.sq_sqrt hs.le]; simp
  have jensen (h : Hidden m) : V h^4 ≤ ∑ j, (m:ℝ)⁻¹ * hiddenFeature x h j ^ 8 := by
    have hav := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : Fin m => (m:ℝ)⁻¹)
      (fun j => hiddenFeature x h j ^ 2) (by intros; positivity)
      (by simp [hm.ne']) (fun _ _ => sq_nonneg _) 4
    simpa only [V, mul_pow, hnorm, ←pow_mul] using hav
  have hint (j : Fin m) := (hidden_eighth x j).1.const_mul (m:ℝ)⁻¹
  have hdom : Integrable (fun h => (∑ j, (m:ℝ)⁻¹ * hiddenFeature x h j ^8)*standardEighth)
      (hiddenLaw m) := (integrable_finsetSum _ (fun j _ => hint j)).mul_const _
  rw [eq]
  refine (integral_mono (hi.integral_prod_right) hdom (fun h => ?_)).trans ?_
  · change (∫ a, (linearReadout (fun j => (1/Real.sqrt m)*hiddenFeature x h j) a)^8 ∂layerLaw m) ≤ _
    rw [linearReadout_eighth]
    exact mul_le_mul_of_nonneg_right (jensen h) standardEighth_nonneg
  · rw [integral_mul_const,integral_finsetSum _ (fun j _ => hint j)]
    simp_rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hidden_eighth x j).2 (by positivity : 0 ≤ (m:ℝ)⁻¹))) standardEighth_nonneg).trans_eq
    simp [hm.ne']
    ring

theorem output_lpNorm_eight {m : ℕ} (hm : 0 < m) (x : ℝ × ℝ) :
    lpNorm (fun z : Seed m => CircleFlowPath.output (1/Real.sqrt m) z x) 8 (seedLaw m) ≤
      ((x.1^2+x.2^2)^4 * standardEighth^2) ^ (8:ℝ)⁻¹ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (output_memLp_eight m x).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [show (8:ℝ) = (8:ℕ) by norm_num,Real.rpow_natCast,Real.norm_eq_abs,(by decide : Even 8).pow_abs]
  exact Real.rpow_le_rpow (integral_nonneg fun z => by positivity) (output_eighth_moment hm x) (by positivity)


/-- Work with one Cartesian neuron while placing its first hidden coordinate
first for spherical integration. The resulting order is (w₁,(a,w₂)). -/
def alignedSplit : Atom ≃ᵐ (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.finTwoArrow (α:=ℝ)))

theorem alignedSplit_apply (z : Atom) : alignedSplit z = (z 1,(z 0,z 2)) := by rfl

theorem alignedSplit_preserving : MeasurePreserving alignedSplit atomLaw
    ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
  ((MeasurePreserving.id (gaussianReal 0 1)).prod
    (measurePreserving_finTwoArrow (gaussianReal 0 1))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 1)

def atomEnergy (z : Atom) : ℝ := z 0^2 + z 1^2 + z 2^2

/-- Rotating any unit hidden direction to the aligned coordinate preserves the
joint law with the energy. The indicator convention at equality is arbitrary
because the identity applies to all radial/projection tests. -/
theorem radial_projection_integral (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) (Φ : ℝ → ℝ → ℝ) :
    ∫ z, Φ (atomEnergy z) (x.1*z 1 + x.2*z 2) ∂atomLaw =
    ∫ z, Φ (atomEnergy z) (z 1) ∂atomLaw := by
  let E := EuclideanSpace ℝ (Fin 3)
  let e : E := WithLp.toLp 2 ![0,1,0]
  let v : E := WithLp.toLp 2 ![0,x.1,x.2]
  have hn : ‖e‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa [e,v,Fin.sum_univ_three] using hx.symm
  let R := (ℝ ∙ (e-v))ᗮ.reflection
  have hR : R e = v := Submodule.reflection_sub hn
  let toE := MeasurableEquiv.toLp 2 Atom
  have ht : MeasurePreserving toE atomLaw (stdGaussian E) :=
    ⟨toE.measurable, map_pi_eq_stdGaussian⟩
  let r := R.symm.toHomeomorph.toMeasurableEquiv
  have hr : MeasurePreserving r (stdGaussian E) (stdGaussian E) :=
    ⟨r.measurable, stdGaussian_map R.symm⟩
  have en (z : Atom) : ‖toE z‖^2 = atomEnergy z := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, toE, atomEnergy]
  have hcoord (z : Atom) : inner ℝ e (toE z) = z 1 := by
    change z ⬝ᵥ (star (![0,1,0] : Fin 3 → ℝ)) = _
    simp [dotProduct,Fin.sum_univ_three]
  have hproj (z : Atom) : inner ℝ v (toE z) = x.1*z 1 + x.2*z 2 := by
    change z ⬝ᵥ (star (![0,x.1,x.2] : Fin 3 → ℝ)) = _
    simp [dotProduct,Fin.sum_univ_three,mul_comm]
  have iso (u : E) : inner ℝ e (r u) = inner ℝ v u := by
    change inner ℝ e (R.symm u) = _
    rw [← hR, ← R.inner_map_map e (R.symm u), R.apply_symm_apply]
  let test : E → ℝ := fun u => Φ (‖u‖^2) (inner ℝ e u)
  have rot (z : Atom) : test (r (toE z)) = Φ (atomEnergy z) (x.1*z 1+x.2*z 2) := by
    change Φ (‖R.symm (toE z)‖^2) (inner ℝ e (r (toE z))) = _
    rw [R.symm.norm_map,en,iso,hproj]
  have al (z : Atom) : test (toE z) = Φ (atomEnergy z) (z 1) := by simp [test,en,hcoord]
  simp_rw [← rot, ← al]
  rw [ht.integral_comp' (fun u => test (r u)), ht.integral_comp' test, hr.integral_comp' test]

def sampleAverage {m : ℕ} (f : Atom → ℝ) (ω : Seed m) :=
  (m:ℝ)⁻¹ * ∑ j : Fin m, f (fun k => ω (j,k))

theorem average_mem {m : ℕ} {f : Atom → ℝ} (hf : MemLp f 2 atomLaw) :
    MemLp (sampleAverage (m:=m) f) 2 (seedLaw m) :=
  (memLp_finsetSum _ (fun j _ => hf.comp_measurePreserving (neuron_preserving m j))).const_mul _

theorem average_mean {m : ℕ} (hm : 0 < m) {f : Atom → ℝ} (hf : MemLp f 2 atomLaw) :
    ∫ ω, sampleAverage (m:=m) f ω ∂seedLaw m = ∫ z, f z ∂atomLaw := by
  have h (j : Fin m) : ∫ ω, f (fun k => ω (j,k)) ∂seedLaw m = ∫ z, f z ∂atomLaw :=
    (neuron_preserving m j).hasLaw.integral_comp hf.aestronglyMeasurable
  unfold sampleAverage
  have hint (j : Fin m) : Integrable (fun ω : Seed m => f (fun k => ω (j,k))) (seedLaw m) :=
    (hf.comp_measurePreserving (neuron_preserving m j)).integrable (by norm_num)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
  simp [h, hm.ne']

theorem average_variance {m : ℕ} (hm : 0 < m) {f : Atom → ℝ} (hf : MemLp f 2 atomLaw) :
    variance (sampleAverage (m:=m) f) (seedLaw m) = variance f atomLaw / m := by
  let F : (Fin m → Atom) → ℝ := ∑ j, fun ω => f (ω j)
  have hF (ω : Fin m → Atom) : F ω = ∑ j, f (ω j) := by simp [F,Finset.sum_apply]
  have hs : MemLp F 2 (Measure.pi (fun _ : Fin m => atomLaw)) := by
    rw [show F = _ from funext hF]
    exact memLp_finsetSum _ (fun j _ => hf.comp_measurePreserving (measurePreserving_eval _ j))
  have h := (curry_preserving m).variance_fun_comp hs.aestronglyMeasurable.aemeasurable
  have hv := variance_sum_pi (μ := fun _ : Fin m => atomLaw) (X := fun _ => f) (fun _ => hf)
  rw [show sampleAverage (m:=m) f = (fun ω => (m:ℝ)⁻¹ * F ((currySeed m) ω)) by
    ext ω; rw [hF]; rfl, variance_const_mul,h,show variance F _ = _ from hv]
  simp [div_eq_mul_inv]; field_simp

/-- Chebyshev for any one-neuron observable under the original flat parameter law. -/
theorem average_concentration {m : ℕ} (hm : 0 < m) {f : Atom → ℝ} (hf : MemLp f 2 atomLaw)
    {v u : ℝ} (hv : variance f atomLaw ≤ v) (hu : 0 < u) :
    (seedLaw m).real {ω | u ≤ |sampleAverage f ω - ∫ z, f z ∂atomLaw|} ≤ v/(m*u^2) := by
  have h := meas_ge_le_variance_div_sq (average_mem (m:=m) hf) hu
  rw [average_mean hm hf, average_variance hm hf] at h
  have hn := variance_nonneg f atomLaw
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht.trans (by rw [← div_div]; gcongr)


theorem atomEnergy_nonneg (z : Atom) : 0 ≤ atomEnergy z := by unfold atomEnergy; positivity

theorem energy_mem (p : ℕ) : MemLp atomEnergy (p : ENNReal) atomLaw := by
  have sqk (k : Fin 3) : MemLp (fun z : Atom => z k^2) (p : ENNReal) atomLaw := by
    have h := (memLp_id_gaussianReal' (μ:=0) (v:=1) ((p:ENNReal)*2) (by finiteness)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) k)
    have h' := h.norm_rpow_div 2
    rw [ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)] at h'
    simpa [atomLaw, ENNReal.toReal_ofNat, Real.norm_eq_abs] using h'
  exact ((sqk 0).add (sqk 1)).add (sqk 2)

theorem energy_pow_integrable (k : ℕ) : Integrable (fun z => atomEnergy z ^k) atomLaw := by
  simpa [Real.norm_eq_abs,abs_of_nonneg (atomEnergy_nonneg _)] using (energy_mem k).integrable_norm_pow'

theorem atomEnergy_mean : ∫ z, atomEnergy z ∂atomLaw = 3 := by
  have hq (k : Fin 3) : ∫ z : Atom, z k ^ 2 ∂atomLaw = 1 := by
    have h := (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) k).hasLaw.integral_comp
      (f:=fun t : ℝ => t^2) (by fun_prop)
    have hs := gaussian_even_moment_succ 0
    norm_num at hs
    exact h.trans hs
  have h : Integrable (fun z : Atom => z 0 ^ 2 + z 1 ^ 2) atomLaw := (coord_pow 0 2).add (coord_pow 1 2)
  change (∫ z : Atom, z 0^2 + z 1^2 + z 2^2 ∂atomLaw) = 3
  rw [integral_add h (coord_pow 2 2), integral_add (coord_pow 0 2) (coord_pow 1 2)]
  norm_num [hq]

theorem atomEnergy_variance : variance atomEnergy atomLaw = 6 := by
  have hz : MemLp (fun t : ℝ => t^2) 2 (gaussianReal 0 1) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have h : MemLp id (4:ℕ) (gaussianReal 0 1) := memLp_id_gaussianReal' 4 (by norm_num)
    simpa [Real.norm_eq_abs, (by decide : Even 4).pow_abs, ← pow_mul] using h.integrable_norm_pow'
  have hs := gaussian_even_moment_succ 0
  norm_num at hs
  have hv : variance (fun t : ℝ => t^2) (gaussianReal 0 1) = 2 := by
    rw [variance_eq_sub hz]
    change (∫ z : ℝ, (z^2)^2 ∂gaussianReal 0 1) - (∫ z : ℝ, z^2 ∂gaussianReal 0 1)^2 = 2
    simp_rw [←pow_mul]
    rw [hs,gaussian_fourth]; norm_num
  have he : atomEnergy = ∑ k : Fin 3, (fun z : Atom => z k^2) := by
    ext z; simp [Fin.sum_univ_three,atomEnergy]
  rw [he]
  have h := variance_sum_pi (μ:=fun _ : Fin 3 => gaussianReal 0 1)
    (X:=fun _ (u:ℝ) => u^2) (fun _ => hz)
  simpa [hv,atomLaw,show (3:ℝ)*2=6 by norm_num] using h

theorem atomEnergy_second : ∫ z, atomEnergy z^2 ∂atomLaw = 15 := by
  have h := variance_eq_sub (energy_mem 2)
  rw [atomEnergy_variance,atomEnergy_mean] at h
  change 6 = (∫ z, atomEnergy z^2 ∂atomLaw) - 3^2 at h
  linarith

theorem energy_dominated {f : Atom → ℝ} {k : ℝ} (hf : Measurable f)
    (h : ∀ z, |f z| ≤ k*atomEnergy z) :
    MemLp f 2 atomLaw ∧ variance f atomLaw ≤ 15*k^2 := by
  have hmem : MemLp f 2 atomLaw := ((energy_mem 2).const_mul k).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun z => h z)
  refine ⟨hmem,(variance_le_expectation_sq hf.aestronglyMeasurable).trans ?_⟩
  have hb z := pow_le_pow_left₀ (abs_nonneg _) (h z) 2
  simp only [sq_abs,mul_pow] at hb
  have he := integral_mono hmem.integrable_sq ((energy_pow_integrable 2).const_mul (k^2)) hb
  rw [integral_const_mul,atomEnergy_second] at he
  simpa [mul_comm] using he

/-- One-neuron contribution to the weighted initial tangent on Cartesian
inputs, using the same gate convention as the actual flow. -/
def weightedAtom (τ : ℝ) (x y : ℝ × ℝ) (z : Atom) :=
  let p := x.1*z 1 + x.2*z 2
  let q := y.1*z 1 + y.2*z 2
  max p 0 * max q 0 +
    τ*(z 0*z 0)*(CircleTangentDrift.actualGate p*CircleTangentDrift.actualGate q)*
      CircleTangentDrift.dot x y

theorem weightedAtom_initial {m : ℕ} (hm : 0 < m) (τ : ℝ) (x y : ℝ × ℝ) (ω : Seed m) :
    CircleTangentDrift.entry τ ω ω x y
      (fun j => CircleTangentDrift.actualGate (CircleFlowPath.pre ω j x))
      (fun j => CircleTangentDrift.actualGate (CircleFlowPath.pre ω j y)) =
    sampleAverage (weightedAtom τ x y) ω := by
  rw [CircleTangentDrift.entry_sum hm, sampleAverage,← div_eq_inv_mul]
  rfl

theorem weightedAtom_cap (τ : ℝ) (x y : ℝ × ℝ)
    (hx : CircleTangentDrift.UnitInput x) (hy : CircleTangentDrift.UnitInput y) (z : Atom) :
    |weightedAtom τ x y z| ≤ (1+|τ|) * atomEnergy z := by
  let s : CircleFlowPath.State 1 := fun p => z p.2
  let l := CircleTangentDrift.length s 0
  have hl : l^2 = atomEnergy z := CircleTangentDrift.length_sq s 0
  have ha : |z 0| ≤ l := CircleTangentDrift.readout_bound s 0
  have hp (v : ℝ × ℝ) (hv : CircleTangentDrift.UnitInput v) :
      |max (v.1*z 1+v.2*z 2) 0| ≤ l := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (CircleTangentDrift.pre_bound s 0 v hv)) (Real.sqrt_nonneg _)
  have gbound (t : ℝ) : |CircleTangentDrift.actualGate t| ≤ 1 := by
    unfold CircleTangentDrift.actualGate; split <;> norm_num
  let p := x.1*z 1 + x.2*z 2
  let q := y.1*z 1 + y.2*z 2
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have hab : |z 0| * |z 0| ≤ l*l := mul_le_mul ha ha (abs_nonneg _) (Real.sqrt_nonneg _)
  have hg : |CircleTangentDrift.actualGate p| * |CircleTangentDrift.actualGate q| ≤ 1 :=
    (mul_le_mul (gbound p) (gbound q) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hd := CircleTangentDrift.dot_bound hx hy
  have h₁ := mul_le_mul (hp x hx) (hp y hy) (abs_nonneg _) (Real.sqrt_nonneg _)
  have ll : 0 ≤ l := Real.sqrt_nonneg _
  have h₂ : |τ| * (|z 0| * |z 0|) * (|CircleTangentDrift.actualGate p| * |CircleTangentDrift.actualGate q|) *
      |CircleTangentDrift.dot x y| ≤ |τ| * (l*l) * 1 * 1 := by gcongr
  change _ + |τ| * (|z 0| * |z 0|) * (|CircleTangentDrift.actualGate p| * |CircleTangentDrift.actualGate q|) * _ ≤ _
  exact (add_le_add h₁ h₂).trans_eq (by rw [←hl]; ring)



open CircleTangentDrift CircleFlowPath

theorem length_pos_ae (m : ℕ) : ∀ᵐ z ∂seedLaw m, ∀ j, 0 < length z j := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [ae_all_iff]; intro j
  have h := (measurePreserving_eval (fun _ : Fin m × Fin 3 => gaussianReal 0 1) (j,0)).quasiMeasurePreserving.ae
    (show ∀ᵐ t ∂gaussianReal 0 1, t ≠ 0 by rw [ae_iff]; simp)
  filter_upwards [h] with z hz
  apply lt_of_lt_of_le _ (CircleTangentDrift.readout_bound z j)
  exact abs_pos.mpr hz

def marginAtom (ρ : ℝ) (x : ℝ × ℝ) (z : Atom) :=
  if |x.1*z 1+x.2*z 2| ≤ ρ*Real.sqrt (atomEnergy z) then atomEnergy z else 0

private theorem margin_cap (ρ : ℝ) (x : ℝ × ℝ) (z : Atom) : |marginAtom ρ x z| ≤ atomEnergy z := by
  unfold marginAtom; split <;> simp [abs_of_nonneg (atomEnergy_nonneg z),atomEnergy_nonneg z]

private theorem margin_meas {Ω : Type*} [MeasurableSpace Ω] {x : Ω → ℝ × ℝ} {z : Ω → Atom}
    (ρ : ℝ) (hx : Measurable x) (hz : Measurable z) : Measurable fun ω => marginAtom ρ (x ω) (z ω) := by
  unfold marginAtom atomEnergy
  have a (k : Fin 3) := (measurable_pi_apply k).comp hz
  apply Measurable.ite (measurableSet_le _ _) _ measurable_const <;> fun_prop

private theorem weighted_meas {Ω : Type*} [MeasurableSpace Ω] (τ : ℝ) {x y : Ω → ℝ × ℝ} {z : Ω → Atom}
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) : Measurable fun ω => weightedAtom τ (x ω) (y ω) (z ω) := by
  have gateM : Measurable actualGate := by
    unfold actualGate
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const
  have a (k : Fin 3) := (measurable_pi_apply k).comp hz
  unfold weightedAtom dot
  fun_prop

private theorem margin_initial {m : ℕ} (ρ : ℝ) (x : ℝ × ℝ) (ω : Seed m) :
    marginMass ω ρ x = sampleAverage (marginAtom ρ x) ω := by
  rw [marginMass,sampleAverage,← div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [marginFlag,length_sq]
  have hl : length ω j = Real.sqrt (atomEnergy (fun k => ω (j,k))) := by
    rw [← Real.sqrt_sq (show 0 ≤ length ω j from Real.sqrt_nonneg _), length_sq]; rfl
  rw [hl]
  unfold marginAtom pre atomEnergy
  split <;> simp


theorem marked_energy (ρ : ℝ) (p : ℕ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1)
    (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) :
    ∫ z, CircleGaussianMargin.mark ρ p (x.1*z 1+x.2*z 2) (atomEnergy z) ∂atomLaw =
    ρ * ∫ z, atomEnergy z^p ∂atomLaw := by
  have hr := radial_projection_integral x hx (fun E t => CircleGaussianMargin.mark ρ p t E)
  rw [hr]
  have E (z : Atom) : CircleGaussianMargin.energy (alignedSplit z) = atomEnergy z := by
    rw [alignedSplit_apply]; unfold CircleGaussianMargin.energy atomEnergy; ring
  have J := CircleGaussianMargin.aligned_energy_mark ρ p hρ hu
  have h := alignedSplit_preserving.integral_comp' (fun q => CircleGaussianMargin.mark ρ p q.1 (CircleGaussianMargin.energy q))
  have h' := alignedSplit_preserving.integral_comp' (fun q => CircleGaussianMargin.energy q^p)
  change (∫ z, CircleGaussianMargin.mark ρ p (alignedSplit z).1
    (CircleGaussianMargin.energy (alignedSplit z)) ∂atomLaw) = _ at h
  simp_rw [E] at h h'
  simp only [alignedSplit_apply] at h
  exact h.trans (J.trans (congrArg (ρ*·) h'.symm))

theorem margin_moments (ρ : ℝ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) :
    (∫ z, marginAtom ρ x z ∂atomLaw) = 3*ρ ∧
    (∫ z, marginAtom ρ x z^2 ∂atomLaw) = 15*ρ := by
  have h₁ := marked_energy ρ 1 hρ hu x hx
  have h₂ := marked_energy ρ 2 hρ hu x hx
  constructor
  · simpa [CircleGaussianMargin.mark,marginAtom,atomEnergy_mean,mul_comm] using h₁
  · have eq (z : Atom) : marginAtom ρ x z^2 = CircleGaussianMargin.mark ρ 2 (x.1*z 1+x.2*z 2) (atomEnergy z) := by
      unfold marginAtom CircleGaussianMargin.mark; split <;> simp
    simp_rw [eq]
    simpa [atomEnergy_second,mul_comm] using h₂

/-- Angular averages of one-neuron observables commute with empirical averaging. -/
private theorem angle_average {m : ℕ} (f : ℝ → Atom → ℝ)
    (meas : Measurable (Function.uncurry f)) (k : ℝ) (cap : ∀ t z, |f t z| ≤ k*atomEnergy z) (ω : Seed m) :
    (∫ t, sampleAverage (f t) ω ∂angularLaw) =
      sampleAverage (fun z => ∫ t, f t z ∂angularLaw) ω := by
  have hi j : Integrable (fun t => f t (fun l => ω (j,l))) angularLaw := by
    refine (integrable_const (k*atomEnergy (fun l => ω (j,l)))).mono' ?_ (ae_of_all _ fun t => cap t _)
    exact (meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  unfold sampleAverage
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)]

private theorem angle_test_meas {f : ℝ → Atom → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun z => ∫ t, f t z ∂angularLaw) := hf.stronglyMeasurable.integral_prod_left.measurable

private theorem angle_cap {f : ℝ → Atom → ℝ} {k : ℝ} (hf : ∀ t z, |f t z| ≤ k*atomEnergy z) (z : Atom) :
    |∫ t, f t z ∂angularLaw| ≤ k*atomEnergy z := by
  simpa using norm_integral_le_of_norm_le_const (μ:=angularLaw) (f:=fun t => f t z) (ae_of_all _ fun t => hf t z)

private theorem phase_meas : Measurable phase := by
  unfold phase; fun_prop

def populationGram (N : ℕ) (τ : ℝ) (i j : Fin N) := ∫ z,
  weightedAtom τ (circleInput N i) (circleInput N j) z ∂atomLaw

def populationMeanRow (N : ℕ) (τ : ℝ) (i : Fin N) := ∫ z, ∫ t,
  weightedAtom τ (phase t) (circleInput N i) z ∂angularLaw ∂atomLaw

private theorem angle_weighted_meas (τ : ℝ) (y : ℝ × ℝ) :
    Measurable (Function.uncurry (fun t z => weightedAtom τ (phase t) y z)) :=
  weighted_meas _ (phase_meas.comp measurable_fst) measurable_const measurable_snd

private theorem angle_margin_meas (ρ : ℝ) :
    Measurable (Function.uncurry (fun t z => marginAtom ρ (phase t) z)) :=
  margin_meas _ (phase_meas.comp measurable_fst) measurable_snd

private theorem unit_grid_eq {N : ℕ} (i : Fin N) :
    (circleInput N i).1^2+(circleInput N i).2^2=1 := by
  have hn := CircleEscape.grid_norm N i
  have hh : (circleInput N i).1^2+(circleInput N i).2^2=‖gridPoint N i‖^2 := by
    change (gridPoint N i).re^2+(gridPoint N i).im^2 = _
    rw [Complex.sq_norm,Complex.normSq_apply]; ring
  rw [hh,hn]; norm_num

private theorem avg_angular_margin_mean (ρ : ℝ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) :
    (∫ z, ∫ t, marginAtom ρ (phase t) z ∂angularLaw ∂atomLaw) = 3*ρ := by
  let f := fun (p : ℝ × Atom) => marginAtom ρ (phase p.1) p.2
  have he : Integrable f (angularLaw.prod atomLaw) :=
    ((energy_pow_integrable 1).comp_snd angularLaw).mono' (angle_margin_meas ρ).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa using margin_cap ρ (phase p.1) p.2)
  rw [show (∫ z, ∫ t, marginAtom ρ (phase t) z ∂angularLaw ∂atomLaw) =
    ∫ t, ∫ z, marginAtom ρ (phase t) z ∂atomLaw ∂angularLaw from (integral_integral_swap he).symm]
  simp_rw [(margin_moments ρ hρ hu (phase _) (Real.cos_sq_add_sin_sq _)).1]
  simp


/-- Each index identifies one quantity in the deterministic tracking hypothesis:
total energy, a grid or angular margin, or a grid or angular tangent entry. -/
abbrev InitIndex (N : ℕ) := Unit ⊕ (Option (Fin N) ⊕ (Fin N × Option (Fin N)))

def initTest (N : ℕ) (τ ρ : ℝ) : InitIndex N → Atom → ℝ
  | .inl _ => atomEnergy
  | .inr (.inl none) => fun z => ∫ t, marginAtom ρ (phase t) z ∂angularLaw
  | .inr (.inl (some i)) => marginAtom ρ (circleInput N i)
  | .inr (.inr (j, none)) => fun z => ∫ t, weightedAtom τ (phase t) (circleInput N j) z ∂angularLaw
  | .inr (.inr (j, some i)) => weightedAtom τ (circleInput N i) (circleInput N j)

theorem initTest_meas (N : ℕ) (τ ρ : ℝ) (q : InitIndex N) : Measurable (initTest N τ ρ q) := by
  rcases q with _ | (i | ⟨j,i⟩)
  · unfold initTest atomEnergy; fun_prop
  · cases i with
    | none => exact angle_test_meas (angle_margin_meas ρ)
    | some i => exact margin_meas _ measurable_const measurable_id
  · cases i with
    | none => exact angle_test_meas (angle_weighted_meas τ _)
    | some i => exact weighted_meas _ measurable_const measurable_const measurable_id

theorem initTest_cap (N : ℕ) (τ ρ : ℝ) (hτ : |τ| ≤ 2) (q : InitIndex N) (z : Atom) :
    |initTest N τ ρ q z| ≤ 3*atomEnergy z := by
  have hm (t : ℝ) (a : Atom) : |marginAtom ρ (phase t) a| ≤ 1*atomEnergy a := by
    simpa using margin_cap ρ (phase t) a
  have h3 := mul_le_mul_of_nonneg_right (by linarith : 1+|τ| ≤ 3) (atomEnergy_nonneg z)
  rcases q with _ | (i | ⟨j,i⟩)
  · change |atomEnergy z| ≤ _; rw [abs_of_nonneg (atomEnergy_nonneg _)]; linarith [atomEnergy_nonneg z]
  · cases i with
    | none => exact (angle_cap hm z).trans (by linarith [atomEnergy_nonneg z])
    | some i => exact (margin_cap ρ _ z).trans (by linarith [atomEnergy_nonneg z])
  · cases i with
    | none => exact (angle_cap (fun t a => weightedAtom_cap τ _ _ (phase_unit t) (grid_unit j) a) z).trans h3
    | some i => exact (weightedAtom_cap τ _ _ (grid_unit i) (grid_unit j) z).trans h3

private theorem angle_margin_initial {m : ℕ} (ρ : ℝ) (ω : Seed m) :
    angularMargin ω ρ = sampleAverage (fun z => ∫ t, marginAtom ρ (phase t) z ∂angularLaw) ω := by
  unfold angularMargin
  simp_rw [margin_initial]
  exact angle_average _ (angle_margin_meas ρ) 1 (fun t z => by simpa using margin_cap ρ (phase t) z) ω

private theorem angular_entry_initial {N m : ℕ} (hm : 0 < m) (τ : ℝ) (j : Fin N) (ω : Seed m) :
    populationRow τ ω (startGates ω) j =
      sampleAverage (fun z => ∫ t, weightedAtom τ (phase t) (circleInput N j) z ∂angularLaw) ω := by
  change (∫ t, entry τ ω ω (phase t) (circleInput N j)
    (fun k => actualGate (pre ω k (phase t))) (fun k => actualGate (pre ω k (circleInput N j))) ∂angularLaw) = _
  simp_rw [weightedAtom_initial hm]
  exact angle_average _ (angle_weighted_meas τ _) _ (fun t z => weightedAtom_cap τ _ _ (phase_unit t) (grid_unit j) z) ω

/-- Convert simultaneous one-neuron concentration to every assumption of
the deterministic tangent drift theorem, for the actual strict-positive gates. -/
theorem goodInit_of_tests {m N : ℕ} (hm : 0 < m) {τ ρ u : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (ω : Seed m)
    (h : ∀ q : InitIndex N, |sampleAverage (initTest N τ ρ q) ω - ∫ z, initTest N τ ρ q z ∂atomLaw| ≤ u) :
    GoodInit τ ρ u (populationGram N τ) (populationMeanRow N τ) ω := by
  constructor
  · have ht := (abs_le.mp (h (.inl ()))).2
    change sampleAverage atomEnergy ω - (∫ z, atomEnergy z ∂atomLaw) ≤ u at ht
    rw [atomEnergy_mean] at ht
    have he : meanEnergy ω = sampleAverage atomEnergy ω := by
      rw [meanEnergy,sampleAverage,← div_eq_inv_mul]; simp_rw [length_sq]; rfl
    rw [he]; linarith
  · intro i
    have ht := (abs_le.mp (h (.inr (.inl (some i))))).2
    change sampleAverage (marginAtom ρ (circleInput N i)) ω - (∫ z, marginAtom ρ (circleInput N i) z ∂atomLaw) ≤ u at ht
    rw [← margin_initial,(margin_moments ρ hρ hρ' _ (unit_grid_eq i)).1] at ht; linarith
  · have ht := (abs_le.mp (h (.inr (.inl none)))).2
    change sampleAverage (fun z => ∫ t, marginAtom ρ (phase t) z ∂angularLaw) ω - (∫ z, ∫ t, marginAtom ρ (phase t) z ∂angularLaw ∂atomLaw) ≤ u at ht
    rw [← angle_margin_initial, avg_angular_margin_mean ρ hρ hρ'] at ht; linarith
  · intro i j
    have ht := h (.inr (.inr (j,some i)))
    change |sampleAverage (weightedAtom τ (circleInput N i) (circleInput N j)) ω - populationGram N τ i j| ≤ u at ht
    rw [← weightedAtom_initial hm] at ht
    exact ht.trans (by linarith)
  · intro j
    have ht := h (.inr (.inr (j,none)))
    change |sampleAverage (fun z => ∫ t, weightedAtom τ (phase t) (circleInput N j) z ∂angularLaw) ω - populationMeanRow N τ j| ≤ u at ht
    rw [← angular_entry_initial hm] at ht
    exact ht.trans (by linarith)

theorem goodInit_failure_of_tests {m N : ℕ} (hm : 0 < m) {τ ρ u p : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ 1)
    (tails : ∀ q : InitIndex N, (seedLaw m).real {ω | u ≤ |sampleAverage (initTest N τ ρ q) ω -
      ∫ z, initTest N τ ρ q z ∂atomLaw|} ≤ p) :
    (seedLaw m).real {ω | ¬GoodInit τ ρ u (populationGram N τ) (populationMeanRow N τ) ω} ≤
      ((N+1:ℝ)^2+1)*p := by
  let bad (q : InitIndex N) := {ω : Seed m | u ≤ |sampleAverage (initTest N τ ρ q) ω -
    ∫ z, initTest N τ ρ q z ∂atomLaw|}
  have sub : {ω : Seed m | ¬GoodInit τ ρ u (populationGram N τ) (populationMeanRow N τ) ω} ⊆
      ⋃ q, bad q := by
    intro ω h
    by_contra h'
    apply h
    apply goodInit_of_tests hm hρ hρ' hu hu' ω
    intro q
    exact (lt_of_not_ge (fun hq => h' (Set.mem_iUnion_of_mem q hq))).le
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun q _ => tails q)).trans_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, InitIndex,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_option,Fintype.card_unit,Fintype.card_fin, nsmul_eq_mul,Nat.cast_add, Nat.cast_one,Nat.cast_mul]
  ring

/-- For m=N³² and u=N⁻⁷ this is O(N⁻¹⁶); a union of the two rates doubles the bound.
Both centering arrays are actual population expectations under the three-coordinate seed. -/
theorem goodInit_failure {m N : ℕ} (hm : 0 < m) {τ ρ u : ℝ} (hτ : |τ| ≤ 2)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hu : 0 < u) (hu' : u ≤ 1) :
    (seedLaw m).real {ω | ¬GoodInit τ ρ u (populationGram N τ) (populationMeanRow N τ) ω} ≤
      ((N+1:ℝ)^2+1) * (135/(m*u^2)) := by
  apply goodInit_failure_of_tests hm hρ hρ' hu.le hu'
  intro q
  have he := energy_dominated (initTest_meas N τ ρ q) (initTest_cap N τ ρ hτ q)
  exact average_concentration hm he.1 (by norm_num at he; exact he.2) hu



open CircleKernelIdentification CircleGridSpectrum

private def readoutSplit : Atom ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

private theorem readoutSplit_preserving : MeasurePreserving readoutSplit atomLaw
    ((gaussianReal 0 1).prod standardPair) :=
  ((MeasurePreserving.id _).prod (measurePreserving_finTwoArrow _)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 0)

/-- The expectation measured by the Cartesian sample concentration is exactly
the kernel whose grid spectrum and angular average are computed in CircleGridSpectrum. -/
theorem weightedAtom_cartesian (τ a b : ℝ) :
    ∫ z, weightedAtom τ (Real.cos a,Real.sin a) (Real.cos b,Real.sin b) z ∂atomLaw =
      cartesianKernel τ a b := by
  let x := (Real.cos a,Real.sin a)
  let y := (Real.cos b,Real.sin b)
  let r := fun (w : ℝ × ℝ) => max (projection a w) 0 * max (projection b w) 0
  let gateProd := fun w => scalarGate (projection a w) * scalarGate (projection b w) * Real.cos (b-a)
  let A := fun z : Atom => r (z 1,z 2)
  let B := fun z : Atom => z 0^2 * gateProd (z 1,z 2)
  have eq (c : ℝ) (z : Atom) : weightedAtom c x y z = A z + c*B z := by
    unfold weightedAtom A B r gateProd projection x y dot
    simp only [CircleKernelIdentification.scalarGate,CircleTangentDrift.actualGate,Real.cos_sub]
    simp only [mul_comm (z 1), mul_comm (z 2)]
    ring
  have hi (t : ℝ) : Integrable (weightedAtom t x y) atomLaw :=
    (energy_dominated (weighted_meas t measurable_const measurable_const measurable_id)
      (weightedAtom_cap t x y (Real.cos_sq_add_sin_sq a).le (Real.cos_sq_add_sin_sq b).le)).1.integrable (by norm_num)
  have hA : Integrable A atomLaw := by simpa only [funext (eq 0),zero_mul,add_zero] using hi 0
  have hB : Integrable B atomLaw := by
    have h := (hi 1).sub hA
    apply h.congr (ae_of_all _ fun z => ?_)
    change weightedAtom 1 x y z - A z = B z
    rw [eq]; ring
  have hRA : ∫ z, A z ∂atomLaw = ∫ w, r w ∂standardPair := by
    have h := readoutSplit_preserving.integral_comp' (fun p => (1:ℝ) * r p.2)
    rw [integral_prod_mul (fun _ : ℝ => (1:ℝ)) r] at h
    change (∫ z : Atom, 1 * r (z 1,z 2) ∂atomLaw) = _ at h
    simpa [A] using h
  have hRB : ∫ z, B z ∂atomLaw = ∫ w, gateProd w ∂standardPair := by
    have h := readoutSplit_preserving.integral_comp' (fun p => p.1^2 * gateProd p.2)
    rw [integral_prod_mul (fun a : ℝ => a^2) gateProd, CircleKernelIdentification.gaussian_second,one_mul] at h
    exact h
  change ∫ z, weightedAtom τ x y z ∂atomLaw = _
  simp_rw [eq,integral_add hA (hB.const_mul τ),integral_const_mul,hRA,hRB]
  unfold gateProd cartesianKernel cartesianProduct
  rw [integral_mul_const]

theorem populationGram_sampled {N : ℕ} [NeZero N] (τ : ℝ) :
    populationGram N τ = sampledMatrix τ := by
  ext i j
  rw [sampledMatrix_cartesian]
  exact weightedAtom_cartesian τ (physicalAngle i) (physicalAngle j)

theorem populationMeanRow_constant {N : ℕ} (τ : ℝ) (j : Fin N) :
    populationMeanRow N τ j = CircleSpectrum.k0 τ := by
  let f := fun (p : ℝ × Atom) => weightedAtom τ (phase p.1) (circleInput N j) p.2
  have hf : Integrable f (angularLaw.prod atomLaw) :=
    (((energy_pow_integrable 1).const_mul (1+|τ|)).comp_snd angularLaw).mono'
      (angle_weighted_meas _ _).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa using weightedAtom_cap τ _ _ (phase_unit p.1) (grid_unit j) p.2)
  change (∫ z, ∫ t, f (t,z) ∂angularLaw ∂atomLaw) = _
  rw [(integral_integral_swap hf).symm]
  have eq (t : ℝ) : (∫ z, f (t,z) ∂atomLaw) = cartesianKernel τ (physicalAngle j) (2*Real.pi*t) := by
    change (∫ z, weightedAtom τ (Real.cos (2*Real.pi*t), Real.sin (2*Real.pi*t))
      (Real.cos (physicalAngle j),Real.sin (physicalAngle j)) z ∂atomLaw) = _
    have h := weightedAtom_cartesian τ (2*Real.pi*t) (physicalAngle j)
    simpa only [cartesian_kernel_isotropic,abs_sub_comm (physicalAngle j) (2*Real.pi*t)] using h
  simp_rw [eq]
  exact cartesian_integrated_row τ _

/-- High-probability control of the deterministic tracking hypotheses with
the spectral matrix and population row that occur in the circle flow proof. -/
theorem spectral_goodInit_failure {m N : ℕ} [NeZero N] (hm : 0 < m) {τ ρ u : ℝ} (hτ : |τ| ≤ 2)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hu : 0 < u) (hu' : u ≤ 1) :
    (seedLaw m).real {ω | ¬GoodInit τ ρ u (sampledMatrix τ) (fun _ : Fin N => CircleSpectrum.k0 τ) ω} ≤
      ((N+1:ℝ)^2+1) * (135/(m*u^2)) := by
  simpa only [populationGram_sampled, funext (populationMeanRow_constant (N:=N) τ)]
    using goodInit_failure (N:=N) hm hτ hρ hρ' hu hu'


theorem sampleAverage_meas {m : ℕ} {f : Atom → ℝ} (hf : Measurable f) :
    Measurable (sampleAverage (m:=m) f) :=
  (Finset.measurable_fun_sum _ (fun j _ => hf.comp (neuron_preserving m j).measurable)).const_mul _

private theorem measurable_forall_finite {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    {P : ι → Ω → Prop} (h : ∀ i, MeasurableSet {ω | P i ω}) :
    MeasurableSet {ω | ∀ i, P i ω} := by
  rw [show {ω | ∀ i, P i ω} = ⋂ i, {ω | P i ω} by ext; simp]
  exact MeasurableSet.iInter h

theorem measurable_goodInit {N m : ℕ} (hm : 0 < m) (τ ρ u : ℝ)
    (K : Matrix (Fin N) (Fin N) ℝ) (kQ : Fin N → ℝ) :
    MeasurableSet {ω : Seed m | GoodInit τ ρ u K kQ ω} := by
  have H (q : InitIndex N) := sampleAverage_meas (m:=m) (initTest_meas N τ ρ q)
  have E : Measurable (meanEnergy (m:=m)) := by
    have he (ω : Seed m) : meanEnergy ω = sampleAverage atomEnergy ω := by
      rw [meanEnergy,sampleAverage,← div_eq_inv_mul]; simp_rw [length_sq]; rfl
    rw [funext he]; exact H (.inl ())
  have M (i : Fin N) : Measurable (fun ω : Seed m => marginMass ω ρ (circleInput N i)) := by
    simp_rw [margin_initial]; exact H (.inr (.inl (some i)))
  have A : Measurable (fun ω : Seed m => angularMargin ω ρ) := by
    simp_rw [angle_margin_initial]; exact H (.inr (.inl none))
  have G (i j : Fin N) : Measurable (fun ω : Seed m => gridGram τ ω (startGates ω) i j) := by
    change Measurable (fun ω : Seed m => entry τ ω ω (circleInput N i) (circleInput N j)
      (fun k => actualGate (pre ω k (circleInput N i))) (fun k => actualGate (pre ω k (circleInput N j))))
    simp_rw [weightedAtom_initial hm]; exact H (.inr (.inr (j,some i)))
  have R (i : Fin N) : Measurable (fun ω : Seed m => populationRow τ ω (startGates ω) i) := by
    simp_rw [angular_entry_initial hm]; exact H (.inr (.inr (i,none)))
  have eq : {ω : Seed m | GoodInit τ ρ u K kQ ω} =
      {ω | meanEnergy ω ≤ 4} ∩ {ω | ∀ i : Fin N, marginMass ω ρ (circleInput N i) ≤ 3*ρ+u} ∩
      {ω | angularMargin ω ρ ≤ 3*ρ+u} ∩
      {ω | ∀ i j, |gridGram τ ω (startGates ω) i j-K i j| ≤ 2*u} ∩
      {ω | ∀ i, |populationRow τ ω (startGates ω) i-kQ i| ≤ 2*u} := by
    ext ω
    exact ⟨fun h => ⟨⟨⟨⟨h.energy,h.gridMargin⟩,h.angular⟩,h.gram⟩,h.mean⟩,
      fun ⟨⟨⟨⟨e,mm⟩,a⟩,g⟩,r⟩ => ⟨e,mm,a,g,r⟩⟩
  rw [eq]
  exact ((((measurableSet_le E measurable_const).inter
    (measurable_forall_finite (fun i => measurableSet_le (M i) measurable_const))).inter
    (measurableSet_le A measurable_const)).inter
    (measurable_forall_finite (fun i => measurable_forall_finite (fun j =>
      measurableSet_le (continuous_abs.measurable.comp ((G i j).sub_const _)) measurable_const)))).inter
    (measurable_forall_finite (fun i => measurableSet_le (continuous_abs.measurable.comp ((R i).sub_const _)) measurable_const))

/-- The two learning rates use exactly the same seed in this probability.
The tube radius may be chosen independently for each grid size in [0,1]. -/
theorem paired_schedule_goodInit {N : ℕ} [NeZero N] (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    (seedLaw (N^32)).real {ω |
      ¬GoodInit (1/2) ρ (1/(N:ℝ)^7) (sampledMatrix (1/2)) (fun _ : Fin N => CircleSpectrum.k0 (1/2)) ω ∨
      ¬GoodInit 2 ρ (1/(N:ℝ)^7) (sampledMatrix 2) (fun _ : Fin N => CircleSpectrum.k0 2) ω} ≤
      1350/(N:ℝ)^16 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hN' : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hs : 0 < (N:ℝ) := by positivity
  have hu : 0 < 1/(N:ℝ)^7 := by positivity
  have hu' : 1/(N:ℝ)^7 ≤ 1 := (div_le_one₀ (by positivity)).mpr (one_le_pow₀ hN')
  have bound (τ : ℝ) (hτ : |τ| ≤ 2) :
      (seedLaw (N^32)).real {ω | ¬GoodInit τ ρ (1/(N:ℝ)^7) (sampledMatrix τ) (fun _ : Fin N => CircleSpectrum.k0 τ) ω} ≤
      675/(N:ℝ)^16 := by
    refine (spectral_goodInit_failure (m:=N^32) (by positivity) hτ hρ hρ' hu hu').trans ?_
    push_cast
    have hh : ((N:ℝ)+1)^2+1 ≤ 5*(N:ℝ)^2 := by nlinarith [sq_nonneg ((N:ℝ)-1)]
    exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by field_simp; ring)
  exact (measureReal_union_le _ _).trans ((add_le_add (bound (1/2) (by norm_num)) (bound 2 (by norm_num))).trans_eq (by ring))


end CircleInitializationConcentration
