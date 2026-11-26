module

public import CircleEulerLimits
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Necessary width along any sequence of update counts tending to infinity.
The grid and the step inside each run can vary. The lower limit is stated by
its eventual lower bounds, so it includes sequences diverging to infinity. -/
public section
noncomputable section
namespace CircleNecessaryWidth
open Filter Real MeasureTheory ProbabilityTheory CircleEscapeBridge CircleEulerLimits
open scoped Topology

/-- Finite necessary width when the paired population MSE is bounded. -/
theorem width_paired (N m T : ℕ) (hN : 3≤N) (hm : 1≤m) (hT : 2≤T)
    {η b V : ℝ} (hp : 0<η) (hc : η≤1) (hb : 0≤b) (hb' : b≤1)
    (hV : (∫ ω, (trainedMean (CircleSeedIntegrability.path N m η) T ω - reference N m b ω)^2
      ∂seedLaw m) ≤ V) :
    4*log 2*(3:ℝ)^T ≤ 896*(m:ℝ)^2/η + log (4*V) := by
  let L := sqrt (64*(m:ℝ)/η)
  have hl : 0 < L := by dsimp [L]; positivity
  have hs : L^2 = 64*(m:ℝ)/η := sq_sqrt (by positivity)
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hhalf := half_amplitude m T hm hT (L:=L) (by rw [hs]; apply (le_div_iff₀ hp).2; linarith)
  have hbox := (CircleSeedIntegrability.actual_bounds N m T hN hm η L b hp hc hl hs hb hb').2.trans hV
  apply width_log_of_mass m T hm η (4*V) L hp hc hs
  have hsize : amplitude m T L/2 ≤ max (amplitude m T L-referenceCap m L) 0 :=
    (show _ ≤ amplitude m T L-referenceCap m L by linarith).trans (le_max_left ..)
  have hpos : 0 ≤ amplitude m T L/2 := by unfold amplitude; positivity
  have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hsize 2) (exp_pos (-896*(m:ℝ)^2/η)).le
  linarith only [hbox,he]

/-- Finite comparison in the normalization relevant to the width threshold. -/
private theorem ratio {η m p v : ℝ} (hη : 0<η) (hm : 0≤m) (hp : 0<p)
    (h : 4*log 2*p ≤ 896*m^2/η + v) :
    sqrt (log 2/224-v/(896*p)) ≤ m/(sqrt η*sqrt p) := by
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow,mul_pow,sq_sqrt hη.le,sq_sqrt hp.le]
  have h' := (le_div_iff₀ hη).mp (show 4*log 2*p-v ≤ 896*m^2/η by linarith)
  field_simp
  nlinarith only [h']

private theorem eventual_ratio (m T : ℕ → ℕ) (η : ℕ → ℝ) (v : ℝ)
    (ht : Tendsto T atTop atTop) (hp : ∀ᶠ i in atTop, 0<η i)
    (bound : ∀ᶠ i in atTop, 4*log 2*(3:ℝ)^(T i) ≤ 896*(m i:ℝ)^2/η i+v)
    {c : ℝ} (hc : c < sqrt (log 2/224)) :
    ∀ᶠ i in atTop, c < (m i:ℝ)/(sqrt (η i)*sqrt ((3:ℝ)^(T i))) := by
  have hg := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3)).comp ht
  have hz := (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<896) hg).inv_tendsto_atTop
  have hz' : Tendsto (fun i => v/(896*(3:ℝ)^(T i))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,Pi.inv_apply,mul_zero] using hz.const_mul v
  have hs := ((tendsto_const_nhds (x:=log 2/224) (f:=atTop)).sub hz').sqrt
  simp only [sub_zero] at hs
  filter_upwards [hs.eventually_const_lt hc,hp,bound] with i hi hp' h
  exact hi.trans_le (ratio hp' (Nat.cast_nonneg _) (by positivity) h)

/-- The lower limit of m/(√η 3^(T/2)) is at least √(log 2/224)
whenever the actual raw variances are eventually uniformly bounded. -/
theorem necessary_of_variance (N m T : ℕ → ℕ) (η : ℕ → ℝ) {V : ℝ}
    (ht : Tendsto T atTop atTop)
    (design : ∀ᶠ i in atTop, 3≤N i ∧ 1≤m i ∧ 0<η i ∧ η i≤1)
    (bound : ∀ᶠ i in atTop, variance (trainedMean (CircleSeedIntegrability.path (N i) (m i) (η i)) (T i))
      (seedLaw (m i)) ≤ V) {c : ℝ} (hc : c < sqrt (log 2/224)) :
    ∀ᶠ i in atTop, c < (m i:ℝ)/(sqrt (η i)*sqrt ((3:ℝ)^(T i))) := by
  apply eventual_ratio m T η (log V) ht (design.mono fun _ h => h.2.2.1) _ hc
  filter_upwards [design,bound] with i ⟨hN,hm,hp,hu⟩ h
  exact width_necessary _ _ _ hN hm _ _ hp hu h

/-- The same necessary condition follows from bounded MSE about the shared-seed
reference, uniformly for coefficients in [0,1]. -/
theorem necessary_of_paired_mse (N m T : ℕ → ℕ) (η b : ℕ → ℝ) {V : ℝ}
    (ht : Tendsto T atTop atTop)
    (design : ∀ᶠ i in atTop, 3≤N i ∧ 1≤m i ∧ 0<η i ∧ η i≤1 ∧ 0≤b i ∧ b i≤1)
    (bound : ∀ᶠ i in atTop, (∫ ω, (trainedMean (CircleSeedIntegrability.path (N i) (m i) (η i))
      (T i) ω - reference (N i) (m i) (b i) ω)^2 ∂seedLaw (m i)) ≤ V)
    {c : ℝ} (hc : c < sqrt (log 2/224)) :
    ∀ᶠ i in atTop, c < (m i:ℝ)/(sqrt (η i)*sqrt ((3:ℝ)^(T i))) := by
  apply eventual_ratio m T η (log (4*V)) ht (design.mono fun _ h => h.2.2.1) _ hc
  filter_upwards [design,bound,ht.eventually_ge_atTop 2] with i ⟨hN,hm,hp,hu,hb,hb'⟩ h hT
  exact width_paired _ _ _ hN hm hT hp hu hb hb' h

end CircleNecessaryWidth
