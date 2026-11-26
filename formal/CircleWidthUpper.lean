module

public import CircleWidthTracking
public import CircleWidthMoment
import all CircleGaussianTracking
import all CircleWidthTracking
import all CircleWidthMoment
import all CircleShortGDTails
import all CircleGaussianBernstein
import all CircleSharpInitialization
import all CircleSeedIntegrability
import Mathlib.Tactic

/-! Probability estimates for stopped, unrestricted GD above the critical width. -/
@[expose] public section
noncomputable section
namespace CircleWidthUpper
open Real MeasureTheory ProbabilityTheory Set Filter
open CircleEscapeBridge CircleGridSpectrum CircleTangentDrift CircleActualTracking
open CircleGaussianTracking CircleWidthTracking CircleWidthMoment

def exceptional (N m : ℕ) [NeZero N] (ρ u : ℝ) : Set (Seed m) :=
  {z | ¬GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) z} ∪
    {z | 2+sqrt m*u < initialRms N m z}

def failureBound (N m : ℕ) (u : ℝ) := 8*((N:ℝ)+1)^2 * exp (-(m:ℝ)*u^2/36864)
def errorBound (m T : ℕ) (ρ u : ℝ) := 6*(2*(30*ρ+3*u))*(2+sqrt m*u)*T

private theorem measurable_exceptional {N m : ℕ} [NeZero N] (hm : 0<m) (ρ u : ℝ) :
    MeasurableSet (exceptional N m ρ u) :=
  (CircleInitializationConcentration.measurable_goodInit hm 1 ρ u _ _).compl.union
    (measurableSet_lt measurable_const (initialRms_measurable _ _))

theorem probability {N m : ℕ} [NeZero N] (hm : 0<m) {ρ u : ℝ} (hρ : 0≤ρ) (hr : ρ≤1)
    (hu : 0≤u) (hc : u≤1) :
    (seedLaw m).real (exceptional N m ρ u) ≤ failureBound N m u := by
  have a := CircleGaussianBernstein.goodInit_exponential (N:=N) hm (by norm_num : |(1:ℝ)|≤2) hρ hr hu hc
  have cap : sqrt (m:ℝ)*u≤128*sqrt m := by nlinarith only [mul_le_mul_of_nonneg_left hc (sqrt_nonneg (m:ℝ)),sqrt_nonneg (m:ℝ)]
  have b := CircleSharpInitialization.initialRms_tail_exp (Nat.pos_of_ne_zero (NeZero.ne N)) hm (mul_nonneg (sqrt_nonneg _) hu) cap
  have sq : (sqrt (m:ℝ)*u)^2= m*u^2 := by rw [mul_pow,sq_sqrt (by positivity)]
  rw [sq] at b
  have sm : exp (-(m*u^2)/4096)≤exp (-(m:ℝ)*u^2/36864) := by
    apply exp_le_exp.mpr; nlinarith only [mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)]
  apply (measureReal_union_le (μ:=seedLaw m) _ _).trans ((add_le_add a (b.trans (mul_le_mul_of_nonneg_left sm (by positivity)))).trans ?_)
  unfold failureBound
  set e := exp (-(m:ℝ)*u^2/36864)
  have ep : 0≤e := exp_nonneg _
  have bnd : (((N:ℝ)+1)^2+1)*2+2*N ≤ 8*((N:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) N,sq_nonneg (N:ℝ)]
  nlinarith only [mul_le_mul_of_nonneg_right bnd ep]

def FitsBudget (m T : ℕ) (ρ u : ℝ) : Prop :=
  0≤ρ ∧ ρ≤1 ∧ 0≤u ∧ u≤1 ∧ (T:ℝ)*(16/sqrt m*(2+sqrt m*u))≤ρ ∧
    (T:ℝ)*(2*(30*ρ+3*u))≤1/2

private theorem inside {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η ρ u : ℝ} (hη : 0≤η) (hc : η≤1) (H : FitsBudget m T ρ u) (z : Seed m)
    (hz : z∉exceptional (n+1) m ρ u) :
    |rawError (n+1) m T η (stoppedCoefficient n T η) z|≤errorBound m T ρ u := by
  simp only [exceptional,Set.mem_union,Set.mem_ofPred_eq,not_or,not_not,not_lt] at hz
  exact stopped_tracking n m T hn odd hm z hη hc hz.1 H.1 H.2.1 H.2.2.1 hz.2 H.2.2.2.2.1 H.2.2.2.2.2

/-- A pointwise accuracy event and a larger-scale bound can be integrated
without requiring either event to contain the other. -/
theorem two_event_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m4 : MemLp X 4 μ) (E F : Set Ω) (me : MeasurableSet E) (mf : MeasurableSet F)
    (a b : ℝ) (fine : ∀ z∉E, |X z|≤a) (coarse : ∀ z∉F, |X z|≤b) :
    ∫ z, X z^2 ∂μ ≤ a^2 + b^2*μ.real E + sqrt (∫ z, X z^4 ∂μ)*sqrt (μ.real F) := by
  classical
  have hi : Integrable (fun z => X z ^ 2) μ := (m4.mono_exponent (by norm_num : (2:ENNReal)≤4)).integrable_sq
  have ma : Integrable (fun z : Ω => a^2) μ := integrable_const _
  have mb : Integrable (E.indicator fun _ => b^2) μ := (integrable_const _).indicator me
  have mF := hi.indicator mf
  have bound (z : Ω) : X z^2 ≤ a^2 + E.indicator (fun _ => b^2) z + F.indicator (fun z => X z^2) z := by
    by_cases h:z∈F
    · rw [indicator_of_mem h]; have e := Set.indicator_nonneg (s:=E) (fun _ _ => sq_nonneg b) z
      linarith [sq_nonneg a]
    · rw [indicator_of_notMem h,add_zero]
      by_cases e:z∈E
      · rw [indicator_of_mem e]
        have p := pow_le_pow_left₀ (abs_nonneg _) (coarse z h) 2
        rw [sq_abs] at p; exact p.trans (le_add_of_nonneg_left (sq_nonneg a))
      · rw [indicator_of_notMem e,add_zero]
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (fine z e) 2
  have mono := integral_mono hi ((ma.add mb).add mF) bound
  rw [integral_add' (ma.add mb) mF,integral_add' ma mb,integral_indicator me,integral_indicator mf,
    setIntegral_const,integral_const,probReal_univ,one_smul,smul_eq_mul] at mono
  rw [mul_comm (μ.real E)] at mono
  exact mono.trans (add_le_add_right (CircleMoment.exceptional_second_moment (F:=X) (CircleGaussianTracking.square_mem m4) F) _)

theorem mse_bound (n m T : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η r u s v : ℝ} (hη : 0≤η) (hc : η≤1) (H : FitsBudget m T r u) (J : FitsBudget m T s v) :
    (∫ z, (rawError (n+1) m T η (stoppedCoefficient n T η) z)^2 ∂seedLaw m) ≤
      (errorBound m T r u)^2 + (errorBound m T s v)^2 * failureBound (n+1) m u +
      sqrt (CircleShortGDTails.fourthBound m T)*sqrt (failureBound (n+1) m v) := by
  classical
  let X := rawError (n+1) m T η (stoppedCoefficient n T η)
  let μ := seedLaw m
  let E := exceptional (n+1) m r u
  let F := exceptional (n+1) m s v
  let a := errorBound m T r u
  let b := errorBound m T s v
  have me : MeasurableSet E := measurable_exceptional hm _ _
  have mf : MeasurableSet F := measurable_exceptional hm _ _
  have m4 := raw_mem4 (n+1) m T η (stoppedCoefficient n T η)
  have mono := two_event_bound X m4 E F me mf a b (inside hn odd hm hη hc H) (inside hn odd hm hη hc J)
  have fE := probability (N:=n+1) hm H.1 H.2.1 H.2.2.1 H.2.2.2.1
  have fF := probability (N:=n+1) hm J.1 J.2.1 J.2.2.1 J.2.2.2.1
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have gp : 0≤CircleKernelGD.gamma (n+1) := (show 0≤(3:ℝ)/π^2 by positivity).trans CircleKernelGD.gamma_bounds.1
  have al : 0≤1-η*CircleKernelGD.gamma (n+1) := sub_nonneg.mpr ((mul_le_of_le_one_left gp hc).trans CircleKernelGD.gamma_bounds.2)
  have a1 : 1-η*CircleKernelGD.gamma (n+1)≤1 := sub_le_self _ (mul_nonneg hη gp)
  have b0 : 0≤stoppedCoefficient n T η :=
    mul_nonneg wb.1 (sub_nonneg.mpr (pow_le_one₀ al a1))
  have b1 : stoppedCoefficient n T η≤1 := (mul_le_of_le_one_right wb.1 (sub_le_self _ (pow_nonneg al T))).trans wb.2
  have four := raw_fourth hη hc (by omega : 0<n+1) hm T b0 b1
  exact mono.trans (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left fE (sq_nonneg b)) _)
    (mul_le_mul (sqrt_le_sqrt four) (sqrt_le_sqrt fF) (sqrt_nonneg _) (sqrt_nonneg _)))

end CircleWidthUpper
