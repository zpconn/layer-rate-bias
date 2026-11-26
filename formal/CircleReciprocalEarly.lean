module

public import CircleGDLimits
import all CircleComparison
public import CircleReciprocalFourth
public import CircleReciprocalSpectral
import all CircleReciprocalSpectral
public import CircleReciprocalTracking
public import CircleReciprocalDesign
public import CircleReciprocalFinite
public import CirclePairedCoefficient
import all CirclePairedCoefficient
import all CircleReciprocal
import all CircleEscapeBridge
import all CircleKernelGD
import all CircleWidthTracking
import all CircleShortGDTails
import Mathlib.Tactic

/-! Paired early-cap error for the true seed-dependent uncapped update. -/
@[expose] public section
noncomputable section
namespace CircleReciprocalEarly
open scoped Topology
open Real MeasureTheory Filter Set CircleEscapeBridge CircleGridSpectrum CircleSpectrum
open CircleShortGDTails CircleKernelGD CircleTangentDrift CircleReciprocalDesign
open CirclePairedCoefficient CircleWidthTracking

def mseConstant := 2*trackingConstant^2+2*CircleResidualSpectrum.modeConstant^2+1

/-- The absolute good-event tracking error splits into a numerical budget
and the actual random initialization's grid-score transient. -/
theorem good_error (n : ℕ) (hn : 2000000000≤n+1) (odd : Odd (n+1)) (z : Seed ((n+1)^32))
    (G : GoodInit 1 (radius (n+1)) (tolerance (n+1)) (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (R : ‖CircleActualTracking.gridR (n+1) z‖≤residualCap (n+1))
    (sp : let N := n+1; let η := CircleReciprocal.rate N (N^32) 1 z
      0≤η ∧ η≤4 ∧ (∀ v : EuclideanSpace ℝ (Fin N), ‖v-η • gramOp (sampledMatrix 1) v‖≤‖v‖) ∧
        |1-η*gamma N|≤exp (-gamma N)) :
    let N := n+1
    |CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 n) z| ≤
      (trackingConstant+|score N (N^32) z|)/(N:ℝ)^3 := by
  intro N
  let η := CircleReciprocal.rate N (N^32) 1 z
  let b := weight 1 n
  let T := earlyCap N
  have d := design_sizes N hn
  have hm : 0<N^32 := pow_pos (Nat.succ_pos _) _
  have gp := (show 0≤(3:ℝ)/π^2 by positivity).trans (gamma_bounds (N:=N)).1
  have f : |1-η*gamma N|≤1 := sp.2.2.2.trans (exp_le_one_iff.mpr (neg_nonpos.mpr gp))
  have tr := CircleReciprocalTracking.stopped_tracking n (N^32) T (by omega) odd hm z sp.1 sp.2.1 G d.1 d.2.1 d.2.2.1 R sp.2.2.1 f d.2.2.2.2.1 d.2.2.2.2.2.1
  have Y : |CircleReciprocal.Y N (N^32) T 1 z-reference N (N^32) (stoppedCoefficient n T η) z|≤trackingConstant/(N:ℝ)^3 :=
    tr.trans d.2.2.2.2.2.2
  have sb := CircleReciprocalSpectral.short_decay (N:=N) (η:=η) sp.2.2.2
  rw [abs_pow] at sb
  have wb := CircleActualTracking.weight_abs_le_one n 1 (by norm_num)
  have X : reference N (N^32) (stoppedCoefficient n T η) z-reference N (N^32) b z =
      -(b*(1-η*gamma N)^T)*score N (N^32) z := by unfold reference stoppedCoefficient score;dsimp only [b,N];ring
  have aux : |b*(1-η*gamma N)^T| ≤ 1/(N:ℝ)^3 := by
    rw [abs_mul,abs_pow];exact (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) T) wb).trans sb
  have step := abs_sub_le (CircleReciprocal.Y N (N^32) T 1 z) (reference N (N^32) (stoppedCoefficient n T η) z) (reference N (N^32) b z)
  rw [X,abs_mul,abs_neg] at step
  exact step.trans ((add_le_add Y (mul_le_mul_of_nonneg_right aux (abs_nonneg _))).trans_eq (by ring))

theorem split_mse {m N : ℕ} [NeZero N] (hn : 3≤N) (hm : 0<m) (F : Seed m→ℝ)
    (int : Integrable (fun z => F z^2) (seedLaw m)) (E : Set (Seed m)) (me : MeasurableSet E)
    (good : ∀ z∈E, |F z|≤(trackingConstant+|score N m z|)/(N:ℝ)^3)
    (bad : (∫ z in Eᶜ, F z^2 ∂seedLaw m)≤1/(N:ℝ)^6) :
    (∫ z, F z^2 ∂seedLaw m)≤mseConstant/(N:ℝ)^6 := by
  let μ := seedLaw m
  let B := trackingConstant
  let q := score N m
  let g := fun z => (2*B^2+2*q z^2)/(N:ℝ)^6
  obtain ⟨mem,norm⟩ := CirclePairedCoefficient.score_bound hn hm
  have hi : Integrable g μ := (((integrable_const (μ:=μ) (2*B^2)).add (mem.integrable_sq.const_mul 2)).div_const _)
  have sq : (∫ z, q z^2 ∂μ)≤CircleResidualSpectrum.modeConstant^2 := by
    have k := (CirclePairedCoefficient.rms_of_mem μ mem).trans_le norm
    have h := pow_le_pow_left₀ (sqrt_nonneg _) k 2
    rw [sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at h
    exact h
  have whole : (∫ z, g z ∂μ) ≤ (2*B^2+2*CircleResidualSpectrum.modeConstant^2)/(N:ℝ)^6 := by
    have hq : Integrable (fun z => q z^2) μ := mem.integrable_sq
    dsimp only [g]
    rw [integral_div,integral_add (integrable_const (μ:=μ) (2*B^2)) (hq.const_mul 2),integral_const,integral_const_mul 2 (fun z => q z^2)]
    simp only [probReal_univ,one_smul]
    gcongr
  have dom : ∀ z∈E, F z^2≤g z := by
    intro z hz
    have h := pow_le_pow_left₀ (abs_nonneg _) (good z hz) 2
    rw [sq_abs,div_pow,←pow_mul] at h
    apply h.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    change (B+|q z|)^2≤2*B^2+2*q z^2
    nlinarith [sq_nonneg (B-|q z|),sq_abs (q z)]
  have ins := (setIntegral_mono_on int.integrableOn hi.integrableOn me dom).trans ((setIntegral_le_integral hi (ae_of_all μ fun z => show 0≤g z by dsimp [g];positivity)).trans whole)
  rw [←integral_add_compl me int]
  exact (add_le_add ins bad).trans_eq (by dsimp [mseConstant,B];ring)

/-- Finite-width assembly, with the two independently established spectral
and exceptional-set estimates supplied in their native forms. -/
theorem gaussian_mse (n : ℕ) (hn : 2000000000≤n+1) (odd : Odd (n+1))
    (int : let N := n+1
      Integrable (fun z => (CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 n) z)^2) (seedLaw (N^32)))
    (spectral : let N := n+1
      ∀ z : Seed (N^32), GoodInit 1 (radius N) (tolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z →
      let η := CircleReciprocal.rate N (N^32) 1 z
      0≤η ∧ η≤4 ∧ (∀ v : EuclideanSpace ℝ (Fin N), ‖v-η • gramOp (sampledMatrix 1) v‖≤‖v‖) ∧
        |1-η*gamma N|≤exp (-gamma N))
    (exceptional : let N := n+1
      ∀ E : Set (Seed (N^32)), MeasurableSet E → (seedLaw (N^32)).real E≤exp (-(N:ℝ)^12/1000000) →
      (∫ z in E, (CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32))≤1/(N:ℝ)^6) :
    let N := n+1
    (∫ z, (CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32))≤mseConstant/(N:ℝ)^6 := by
  intro N
  obtain ⟨E,me,fail,good⟩ := event N hn
  apply split_mse (N:=N) (by omega) (pow_pos (Nat.succ_pos n) 32)
    (fun z => CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 n) z) int E me _ (exceptional Eᶜ me.compl fail)
  intro z hz
  obtain ⟨G,R⟩ := good z hz
  exact good_error n hn odd z G R (spectral z G)

/-- Under the unrestricted original product Gaussian law, the actual early
learner with the uncapped reciprocal step tracks its own interpolation
reference at mean-square order N⁻⁶. -/
theorem early_mse : ∀ᶠ N : ℕ in atTop, Odd N →
    (∫ z, (CircleReciprocal.Y N (N^32) (earlyCap N) 1 z-reference N (N^32) (weight 1 (N-1)) z)^2 ∂seedLaw (N^32))
      ≤ mseConstant/(N:ℝ)^6 := by
  filter_upwards [eventually_ge_atTop 2000000000,CircleReciprocalFourth.short_exceptional] with N hn ex odd
  cases N with
  | zero => omega
  | succ n =>
    let N := n+1
    have hm : 0<N^32 := pow_pos (Nat.succ_pos _) _
    have w := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
    have mem := CircleReciprocalFourth.short_memLp N (by omega) odd 1 (weight 1 n) (by norm_num) w.1 w.2
    have d := design_sizes N hn
    apply gaussian_mse n hn odd ((mem.mono_exponent (by norm_num : (2:ENNReal)≤4)).integrable_sq) _ _
    · intro _ z G
      have q := CircleReciprocalSpectral.good_rate (by omega : 3≤N) odd hm z d.2.2.1 (d.2.2.2.1.trans (by norm_num)) G
      refine ⟨zero_le_one.trans q.1,q.2.1,?_,q.2.2.2.2⟩
      exact CircleReciprocalSpectral.contract q.2.2.2.1
    · exact fun E _ prob => ex odd _ w.1 w.2 E prob

/-- The paper's short-time paired RMS estimate for the actual whole-circle
population mean and reference, with c=1 and no event restriction. -/
theorem early_rms : ∀ᶠ N : ℕ in atTop, Odd N →
    sqrt (∫ z, (CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ 1 z-
      reference N (N^32) (weight 1 (N-1)) z)^2 ∂seedLaw (N^32)) ≤ sqrt mseConstant/(N:ℝ)^3 := by
  filter_upwards [early_mse] with N h odd
  apply (sqrt_le_sqrt (h odd)).trans_eq
  have nn : 0≤mseConstant := by unfold mseConstant;positivity
  rw [sqrt_div nn,show (N:ℝ)^6=((N:ℝ)^3)^2 by ring,sqrt_sq (by positivity)]

set_option maxHeartbeats 3000000 in
/-- Bias, variance and independently initialized ensemble MSE of the actual
early reciprocal learner along growing odd grids. -/
theorem early_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop) (hn : ∀ i, 16≤n i+1)
    (odd : ∀ i, Odd (n i+1)) :
    CircleGDLimits.BenchmarkLimits n (fun i => CircleReciprocal.Y (n i+1) ((n i+1)^32) (earlyCap (n i+1)) 1) := by
  let W := fun i => (n i+1)^32
  let Y := fun i => CircleReciprocal.Y (n i+1) (W i) (earlyCap (n i+1)) 1
  let Z := fun i => reference (n i+1) (W i) (weight 1 (n i))
  have h3 (i : ℕ) : 3≤n i+1 := by have := hn i;omega
  have hm (i : ℕ) : 0<W i := pow_pos (Nat.succ_pos _) _
  have meas (i : ℕ) : Measurable (Y i) := CircleReciprocal.Y_measurable _ _ _ _ (h3 i) (odd i) (hm i)
  have mem (i : ℕ) : MemLp (Y i) 2 (seedLaw (W i)) := by
    have w := CircleGaussianTracking.weight_bounds (n i) (τ:=1) (by norm_num)
    have h := CircleReciprocalFourth.short_memLp (n i+1) (hn i) (odd i) 1 _ (by norm_num) w.1 w.2
    have diff : MemLp (Y i-Z i) 2 (seedLaw (W i)) := h.mono_exponent (by norm_num)
    have ref : MemLp (Z i) 2 (seedLaw (W i)) := CircleSeedIntegrability.reference_memLp _ _ _ _ (by norm_num)
    simpa only [sub_add_cancel] using diff.add ref
  have ngrow : Tendsto (fun i => n i+1) atTop atTop := tendsto_atTop_mono (fun i => Nat.le_succ (n i)) grow
  have lim := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow).const_mul (sqrt mseConstant)
  have track : Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (∫ z, (Y i z-Z i z)^2 ∂seedLaw (W i))) atTop (𝓝 0) := by
    apply squeeze_zero' (.of_forall fun _ => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) _ (by simpa using lim)
    filter_upwards [ngrow.eventually early_rms] with i hb
    have h : sqrt (∫ z, (Y i z-Z i z)^2 ∂seedLaw (W i)) ≤ sqrt mseConstant/((n i:ℝ)+1)^3 := by
      have hb' := hb (odd i)
      change sqrt (∫ z, (Y i z-reference (n i+1) (W i) (weight 1 (n i)) z)^2 ∂seedLaw (W i))≤sqrt mseConstant/((n i+1:ℕ):ℝ)^3 at hb'
      simpa only [Nat.cast_add,Nat.cast_one] using hb'
    exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by field_simp)
  have res := CircleComparison.gaussian_reference_transfer n W grow h3 odd hm (τ:=1) (by norm_num) Y mem track
  have bias : Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ z, Y i z ∂seedLaw (W i))-1)) atTop (𝓝 (-(π^2/36))) := by
    convert res.1.neg using 2 with i <;> ring
  have var : Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (seedLaw (W i)))
      atTop (𝓝 (7*π^2/1620)) := by convert res.2 using 2;ring
  refine ⟨bias,var,?_⟩
  intro r hr
  convert (bias.pow 2).add (var.div_const r) using 2 with i
  · rw [CircleComparison.product_ensemble r hr (Y i) (mem i) (meas i)]
    ring
  · ring

/-- The asymptotic statement only requires the odd grid sizes to tend to
infinity. Small initial members of a design sequence do not affect its limits. -/
theorem growing_odd_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (odd : ∀ i, Odd (n i+1)) :
    CircleGDLimits.BenchmarkLimits n (fun i => CircleReciprocal.Y (n i+1) ((n i+1)^32) (earlyCap (n i+1)) 1) := by
  let l := fun i => if 16≤n i+1 then n i else 16
  have eq : l =ᶠ[atTop] n := by
    filter_upwards [grow.eventually_ge_atTop 16] with i hi
    exact ite_eq_left (by omega)
  have hs (i) : 16≤l i+1 := by dsimp [l];split <;> omega
  have ho (i) : Odd (l i+1) := by
    dsimp [l]
    split
    · exact odd i
    · exact ⟨8,rfl⟩
  obtain ⟨a,b,c⟩ := early_limits l (grow.congr' eq.symm) hs ho
  constructor
  · apply a.congr'
    filter_upwards [eq] with i hi
    exact congrArg (fun j : ℕ => ((j:ℝ)+1)^2*((∫ z, CircleReciprocal.Y (j+1) ((j+1)^32) (earlyCap (j+1)) 1 z ∂seedLaw ((j+1)^32))-1)) hi
  constructor
  · apply b.congr'
    filter_upwards [eq] with i hi
    exact congrArg (fun j : ℕ => ((j:ℝ)+1)^4*ProbabilityTheory.variance (CircleReciprocal.Y (j+1) ((j+1)^32) (earlyCap (j+1)) 1) (seedLaw ((j+1)^32))) hi
  intro r hr
  apply (c r hr).congr'
  filter_upwards [eq] with i hi
  exact congrArg (fun j : ℕ => ((j:ℝ)+1)^4*∫ z : Fin r → Seed ((j+1)^32), ((r:ℝ)⁻¹*(∑ a, CircleReciprocal.Y (j+1) ((j+1)^32) (earlyCap (j+1)) 1 (z a))-1)^2 ∂Measure.pi (fun _ : Fin r => seedLaw ((j+1)^32))) hi

end CircleReciprocalEarly
