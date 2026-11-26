module

public import CircleEscape
public import CircleStats
import Mathlib.Tactic

/-! The initialization check for a fixed, preassigned update cap. The input
`lam` to the rule is the realized largest eigenvalue of the initial normalized
training Gram. The path argument needs only its value at initialization. -/

public section
noncomputable section

namespace CircleInitializationCheck
open CircleEscape MeasureTheory ProbabilityTheory Set

def capRate (lam : ℝ) : ℝ := 1 / max 1 lam

theorem capRate_eq_min (lam : ℝ) (positive : 0 < lam) :
    capRate lam = min 1 (1 / lam) := by
  unfold capRate
  by_cases h : lam ≤ 1
  · rw [max_eq_left h, min_eq_left ((le_div_iff₀ positive).mpr (by linarith)), div_one]
  · have h' := le_of_not_ge h
    rw [max_eq_right h', min_eq_right ((div_le_iff₀ positive).mpr (by linarith))]

def train (N m : ℕ) (η : ℝ) (initial : Net ℂ m) : ℕ → Net ℂ m
  | 0 => initial
  | T+1 => step (gridPoint N) (fun i => 1+(gridPoint N i).re)
      (1/Real.sqrt m) (η/(N*Real.sqrt m)) (train N m η initial T)

/-- Equality of the entire sequence of simultaneous GD iterates, including
zero curvature, for which the chosen step is one. -/
theorem trajectory_on_check (N m : ℕ) (lam : ℝ) (pass : lam ≤ 1) (initial : Net ℂ m) :
    train N m (capRate lam) initial = train N m 1 initial := by
  simp [capRate, max_eq_left pass]

def pairedSquare {Ω : Type*} (N m T : ℕ) (rate : Ω → ℝ) (initial : Ω → Net ℂ m)
    (reference : Ω → ℝ) (ω : Ω) : ℝ :=
  (populationMean (1/Real.sqrt m) (train N m (rate ω) (initial ω) T) - reference ω)^2

/-- For any common reference on the same seed space, equality of paths gives
equality of paired-error contributions on the passing event. The bound uses
the unrestricted capped MSE. -/
theorem restricted_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N m T : ℕ) (lam : Ω → ℝ) (initial : Ω → Net ℂ m) (Z : Ω → ℝ)
    (hE : MeasurableSet {ω | lam ω ≤ 1})
    (integrable : Integrable (pairedSquare N m T (capRate ∘ lam) initial Z) μ) :
    (∫ ω in {ω | lam ω ≤ 1}, pairedSquare N m T (fun _ => 1) initial Z ω ∂μ) =
      ∫ ω in {ω | lam ω ≤ 1}, pairedSquare N m T (capRate ∘ lam) initial Z ω ∂μ ∧
    (∫ ω in {ω | lam ω ≤ 1}, pairedSquare N m T (fun _ => 1) initial Z ω ∂μ) ≤
      ∫ ω, pairedSquare N m T (capRate ∘ lam) initial Z ω ∂μ := by
  have eqon := setIntegral_congr_fun (μ := μ) hE (f := pairedSquare N m T (fun _ => 1) initial Z)
    (g := pairedSquare N m T (capRate ∘ lam) initial Z) (by
      intro ω pass
      simp [pairedSquare, trajectory_on_check N m (lam ω) pass (initial ω)])
  refine ⟨eqon, eqon.le.trans ?_⟩
  exact setIntegral_le_integral integrable (ae_of_all _ (fun _ => sq_nonneg _))

/-- A divergent total fixed-step contribution transfers to the failing event
when the unconditional capped contribution vanishes (or is bounded). This
finite inequality also records the unnormalized quantity being localized. -/
theorem failing_mse_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N m T : ℕ) (lam : Ω → ℝ) (initial : Ω → Net ℂ m) (Z : Ω → ℝ)
    (hE : MeasurableSet {ω | lam ω ≤ 1})
    (hfix : Integrable (pairedSquare N m T (fun _ => 1) initial Z) μ)
    (hcap : Integrable (pairedSquare N m T (capRate ∘ lam) initial Z) μ) :
    (∫ ω, pairedSquare N m T (fun _ => 1) initial Z ω ∂μ) -
      (∫ ω, pairedSquare N m T (capRate ∘ lam) initial Z ω ∂μ) ≤
      ∫ ω in {ω | lam ω ≤ 1}ᶜ, pairedSquare N m T (fun _ => 1) initial Z ω ∂μ := by
  have pass := (restricted_mse μ N m T lam initial Z hE hcap).2
  linarith [integral_add_compl hE hfix]

/-- Averaging r independent runs with common mean and variance splits the MSE
into squared bias and the single-run variance divided by r. This identity is
exact at any finite width and horizon for which the second moments exist. -/
theorem ensemble_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : ℕ) (hr : 0 < r) (Y : Fin r → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (ind : ∀ i j, i ≠ j → Y i ⟂ᵢ[μ] Y j) (mean var target : ℝ)
    (commonMean : ∀ i, ∫ ω, Y i ω ∂μ = mean) (commonVar : ∀ i, variance (Y i) μ = var) :
    ∫ ω, ((r:ℝ)⁻¹ * (∑ i, Y i) ω-target)^2 ∂μ = (mean-target)^2 + var/r := by
  have hsum := memLp_finsetSum' Finset.univ (fun (i : Fin r) _ => hY i)
  have rp : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmean : (∫ ω, (r:ℝ)⁻¹ * (∑ i, Y i) ω ∂μ) = mean := by
    simp only [Finset.sum_apply, integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun i _ => (hY i).integrable one_le_two)]
    simp [commonMean, rp]
  rw [CircleStats.mse_decomposition (hsum.const_mul (r:ℝ)⁻¹) target, hmean,
    variance_const_mul, IndepFun.variance_sum (fun i _ => hY i) (fun i _ j _ hij => ind i j hij)]
  simp only [commonVar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Bootstrap for normalized parameter energy, uniform in layer imbalance.
The start-of-step spectral comparison is represented by the initial budget of
three. The GD energy-increment inequality is assumed only at steps before T.
No monotonicity assumption on the loss or the residual is needed. -/
theorem capped_energy_bootstrap (m T : ℕ) (hm : 0 < m) (short : 24*T ≤ m)
    (η u y : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (labels : y^2 = 3/2) (M R : ℕ → ℝ) (initial : η*u*M 0 ≤ 3)
    (increment : ∀ t < T, m*(M (t+1)-M t) ≤
      η * (-(4-η*u*M t)*(R t)^2 + 4*y*R t)) :
    ∀ t ≤ T, M t ≤ M 0 + 12*η*t/m ∧ η*u*M t ≤ 7/2 := by
  have mp : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hau : 0 ≤ η*u := mul_nonneg hη hu
  have hprod : η*u ≤ 1 := (mul_le_mul hη' hu' hu (by norm_num)).trans_eq (one_mul 1)
  have second (t : ℕ) (ht : t ≤ T) (first : M t ≤ M 0 + 12*η*t/m) :
      η*u*M t ≤ 7/2 := by
    have span : 24*(t:ℝ) ≤ m := by exact_mod_cast (Nat.le_trans (Nat.mul_le_mul_left 24 ht) short)
    have extra : 12*η*t/m ≤ 1/2 := by
      apply (div_le_iff₀ mp).mpr
      nlinarith [mul_le_mul_of_nonneg_right hη' (Nat.cast_nonneg t)]
    have hs : η*u*(12*η*t/m) ≤ 1/2 := by
      simpa using mul_le_mul hprod extra (by positivity) (by norm_num : (0:ℝ) ≤ 1)
    have sum := mul_le_mul_of_nonneg_left first hau
    rw [mul_add] at sum
    linarith
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨by simp, by linarith⟩
  | succ t ih =>
    intro ht
    obtain ⟨first, stable⟩ := ih (Nat.le_of_succ_le ht)
    have residual : -(4-η*u*M t)*(R t)^2 + 4*y*R t ≤ 12 := by
      nlinarith [mul_le_mul_of_nonneg_right stable (sq_nonneg (R t)), sq_nonneg (R t-4*y)]
    have delta := (increment t (Nat.lt_of_succ_le ht)).trans (mul_le_mul_of_nonneg_left residual hη)
    have rise : M (t+1)-M t ≤ 12*η/m := by
      apply (le_div_iff₀ mp).mpr
      linarith
    have next : M (t+1) ≤ M 0 + 12*η*(t+1:ℕ)/m := by
      push_cast
      rw [mul_add, add_div, mul_one]
      linarith
    exact ⟨next, second _ ht next⟩

end CircleInitializationCheck
