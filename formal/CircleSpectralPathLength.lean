module

public import CircleResidualSpectrum
import all CircleResidualSpectrum
import all CircleFlowMoments
import all CircleFlowPath
import all CircleEscapeBridge
import all CircleSpectrum
public import CircleGridSpectrum
import all CircleGridSpectrum
import all CircleTangentDrift
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! A frequency-dependent path bound for the normalized circulant semigroup.
The fourth norm of a group of modes is controlled before integrating in time;
modes in different dyadic bands can decay at different rates. -/

public section
noncomputable section
namespace CircleSpectralPathLength
open Real MeasureTheory Set Finset CircleGridSpectrum

/-- Euclidean norm of a block of normalized complex Fourier coefficients. -/
def blockNorm {ι : Type*} (S : Finset ι) (a : ι → ℂ) :=
  √(∑ i ∈ S, ‖a i‖^2)

private theorem block_sq {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    blockNorm S a ^ 2 = ∑ i ∈ S, ‖a i‖^2 := sq_sqrt (sum_nonneg (fun _i _ => sq_nonneg _))

private theorem block_le_sum {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    blockNorm S a ≤ ∑ i ∈ S, ‖a i‖ := by
  apply (sq_le_sq₀ (sqrt_nonneg _) (sum_nonneg fun i _ => norm_nonneg _)).mp
  rw [sq_sqrt (sum_nonneg (fun _ _ => sq_nonneg _))]
  exact sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

private theorem block_fourth_cap {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    (blockNorm S a)^4 ≤ (S.card:ℝ)*∑ i ∈ S, ‖a i‖^4 := by
  have h := sum_mul_sq_le_sq_mul_sq S (fun _ : ι => (1:ℝ)) (fun i => ‖a i‖^2)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,←pow_mul] at h
  norm_num at h
  rwa [show blockNorm S a^4=(blockNorm S a^2)^2 by ring,block_sq]

private theorem lp4_pow {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
    {f : Ω → E} (hf : MemLp f 4 μ) : lpNorm f 4 μ ^ 4 = ∫ z, ‖f z‖^4 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg (fun z => by positivity))]
  norm_num

theorem block_mem {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Finset ι) (a : ι → Ω → ℂ) (ha : ∀ i ∈ S, MemLp (a i) 4 μ) :
    MemLp (fun z => blockNorm S (fun i => a i z)) 4 μ := by
  have cap := memLp_finsetSum S (fun i hi => (ha i hi).norm)
  apply cap.of_le
  · unfold blockNorm
    exact continuous_sqrt.comp_aestronglyMeasurable (S.aestronglyMeasurable_fun_sum (fun i hi => (ha i hi).aestronglyMeasurable.norm.pow _))
  · exact ae_of_all _ fun z => by
      change |blockNorm S (fun i => a i z)| ≤ |∑ i ∈ S, ‖a i z‖|
      rw [abs_of_nonneg (show 0 ≤ blockNorm S _ from sqrt_nonneg _),abs_of_nonneg (sum_nonneg fun i _ => norm_nonneg _)]
      exact block_le_sum _ _

/-- Block L⁴ costs the square root of the number of frequencies. Neither
independence of the modes nor a pointwise bound on the seed is assumed. -/
theorem block_lp4 {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Finset ι) (a : ι → Ω → ℂ) (ha : ∀ i ∈ S, MemLp (a i) 4 μ)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i ∈ S, lpNorm (a i) 4 μ ≤ K) :
    lpNorm (fun z => blockNorm S (fun i => a i z)) 4 μ ≤ √(S.card : ℝ)*K := by
  let B (z : Ω) := blockNorm S (fun i => a i z)
  have hB := block_mem S a ha
  have hBa : Integrable (fun z => ‖B z‖^4) μ := hB.integrable_norm_pow (by decide : 4≠0)
  have hI (i : ι) (hi : i ∈ S) : Integrable (fun z => ‖a i z‖^4) μ :=
    (ha i hi).integrable_norm_pow (by decide : 4≠0)
  have hx : lpNorm B 4 μ ^4 ≤ (√(S.card:ℝ)*K)^4 := by
    rw [lp4_pow hB]
    calc
      _ ≤ ∫ z, (S.card:ℝ)*∑ i ∈ S, ‖a i z‖^4 ∂μ := by
        apply integral_mono hBa ((integrable_finsetSum S hI).const_mul _)
        intro z; dsimp only
        rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤B z from sqrt_nonneg _)]
        exact block_fourth_cap _ _
      _ = (S.card:ℝ)*∑ i ∈ S, lpNorm (a i) 4 μ ^4 := by
        rw [integral_const_mul,integral_finsetSum S hI]
        congr 1
        exact sum_congr rfl fun i hi => (lp4_pow (ha i hi)).symm
      _ ≤ (S.card:ℝ)*∑ _i ∈ S, K^4 := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => pow_le_pow_left₀ lpNorm_nonneg (hb i hi) _)) (by positivity)
      _ = _ := by
        simp only [sum_const,nsmul_eq_mul,mul_pow,show √(S.card:ℝ)^4=(√(S.card:ℝ)^2)^2 by ring,
          sq_sqrt (Nat.cast_nonneg (α:=ℝ) S.card)]
        ring
  exact (pow_le_pow_iff_left₀ lpNorm_nonneg (mul_nonneg (sqrt_nonneg _) hK) (by decide : 4≠0)).mp hx

open CircleTangentDrift
open scoped ComplexConjugate
variable {N : ℕ} [NeZero N]

def normalizedCoeff (v : Fin N → ℝ) (r : ZMod N) : ℂ :=
  ZMod.dft (fun i => ((v ((ZMod.finEquiv N).symm i)):ℂ)) r / (N:ℂ)

def eigen (τ : ℝ) (r : ZMod N) := aliasValue (tangentCoeff τ) r

def synth (a : ZMod N → ℂ) (i : ZMod N) := ∑ r, a r*char r i

def referencePath (τ : ℝ) (v : Fin N → ℝ) (s : ℝ) : EuclideanSpace ℝ (Fin N) :=
  rmsCoordinates (fun i => (synth (fun r => (exp (-eigen τ r*s):ℂ)*normalizedCoeff v r) (ZMod.finEquiv N i)).re)

theorem referencePath_zero (τ : ℝ) (v : Fin N → ℝ) :
    referencePath τ v 0 = rmsCoordinates v := by
  unfold referencePath
  congr 1
  funext i
  simp only [mul_zero,exp_zero,Complex.ofReal_one,one_mul,normalizedCoeff,synth]
  rw [← synthesis]
  simp

private theorem periodicTangent_real (τ : ℝ) (p : AddCircle (π- -π)) : (periodicTangent τ p).im=0 := by
  have : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩
  change (AddCircle.liftIoc (π- -π) (-π) (fun x => (CircleKernelIdentification.polarNTK τ |x|:ℂ)) p).im=0
  rw [AddCircle.liftIoc]
  rfl

private theorem matrix_synth (τ : ℝ) (h : 0≤τ) (hu : τ≤2) (a : ZMod N→ℂ) (i : Fin N) :
    (∑ j : Fin N, sampledMatrix τ i j*(synth a (ZMod.finEquiv N j)).re)/(N:ℝ) =
    (synth (fun r => (eigen τ r : ℂ)*a r) (ZMod.finEquiv N i)).re := by
  let K (p : ZMod N) := periodicTangent τ (gridAngle p)
  have conv (q : ZMod N) : convolution K (synth a) q =
      synth (fun r => (eigen τ r:ℂ)*a r) q := by
    dsimp only [convolution,synth]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    have hs := sampled_character_eigenvalue τ h hu r q
    change (∑ j, K (q-j)*char r j)/(N:ℂ) = _ at hs
    calc
      _ = a r*((∑ j, K (q-j)*char r j)/N) := by rw [←mul_div_assoc,Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [hs]; dsimp [eigen]; ring
  have eqn := congrArg Complex.re (conv (ZMod.finEquiv N i))
  simp only [convolution,Complex.div_natCast_re,Complex.re_sum,Complex.mul_re,K,periodicTangent_real,
    zero_mul,sub_zero] at eqn
  rw [← fin_sum] at eqn
  exact eqn

theorem referencePath_deriv (τ : ℝ) (h : 0≤τ) (hu : τ≤2) (v : Fin N→ℝ) (s : ℝ) :
    HasDerivAt (referencePath τ v) (-(gramOp (sampledMatrix τ) (referencePath τ v s))) s := by
  let d (r : ZMod N) := eigen τ r
  let a (r : ZMod N) := normalizedCoeff v r
  let c (r : ZMod N) (t : ℝ) := exp (-d r*t)
  have hc (r : ZMod N) : HasDerivAt (c r) (-d r*c r s) s := by
    have hh : HasDerivAt (fun t : ℝ => -d r*t) (-d r) s := by simpa using (hasDerivAt_id s).const_mul (-d r)
    simpa [c,mul_comm] using hh.exp
  have hraw (i : Fin N) : HasDerivAt (fun t => (synth (fun r => (c r t:ℂ)*a r) (ZMod.finEquiv N i)).re)
        (-(synth (fun r => (d r:ℂ)*((c r s:ℂ)*a r)) (ZMod.finEquiv N i)).re) s := by
    let b (r : ZMod N) := (a r * char r (ZMod.finEquiv N i)).re
    have heq (t : ℝ) :
        (synth (fun r => (c r t:ℂ)*a r) (ZMod.finEquiv N i)).re = ∑ r, c r t*b r := by
      simp only [synth,Complex.re_sum,mul_assoc,Complex.re_ofReal_mul,b]
    simp_rw [heq]
    convert HasDerivAt.fun_sum (u:=Finset.univ) (fun r _ => (hc r).mul_const (b r)) using 1
    simp only [synth,Complex.re_sum,mul_assoc,Complex.re_ofReal_mul, ←Finset.sum_neg_distrib,b]
    apply Finset.sum_congr rfl; intros; ring
  have hh := rms_deriv (fun i => hraw i)
  convert hh using 1
  · rfl
  ext i
  rw [PiLp.neg_apply,gramOp_apply,rmsCoordinates]
  change -((∑ j : Fin N, sampledMatrix τ i j * ((synth (fun r => (c r s:ℂ)*a r) (ZMod.finEquiv N j)).re / √N))/N) =
    -(synth (fun r => (d r:ℂ)*((c r s:ℂ)*a r)) (ZMod.finEquiv N i)).re / √N
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, div_right_comm, matrix_synth τ h hu]
  ring

private theorem dft_synth (a : ZMod N → ℂ) (r : ZMod N) :
    ZMod.dft (synth a) r = N*a r := by
  have he : synth a = (N:ℂ) • (ZMod.dft.symm a) := by
    funext i
    rw [Pi.smul_apply,ZMod.invDFT_apply]
    simp only [smul_eq_mul,synth,char]
    rw [← mul_assoc,mul_inv_cancel₀ (NeZero.ne (N:ℂ)),one_mul]
    apply sum_congr rfl; intros; ring
  rw [he,map_smul,ZMod.dft.apply_symm_apply,Pi.smul_apply,smul_eq_mul]

private theorem synth_parseval (a : ZMod N → ℂ) :
    ∑ i, ‖synth a i‖^2 = (N:ℝ)*∑ r, ‖a r‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.conj_mul']
  calc
    _ = ∑ i, ∑ r, a r*(conj (synth a i)*char r i) := by
      apply sum_congr rfl; intro i _
      conv_lhs => rhs; rw [synth]
      rw [Finset.mul_sum]; apply sum_congr rfl; intros; ring
    _ = ∑ r, a r*conj (ZMod.dft (synth a) r) := by rw [sum_comm]; simp_rw [←Finset.mul_sum,adjoint_character_sum]
    _ = _ := by
      simp only [dft_synth,map_mul,map_natCast,Finset.mul_sum]
      apply sum_congr rfl; intros; ring

/-- Norm of the physical reference is bounded by the l² norm of its damped modes;
the normalization matches `gridR` exactly. -/
theorem norm_referencePath (τ : ℝ) (v : Fin N→ℝ) (s : ℝ) :
    ‖referencePath τ v s‖ ≤
      blockNorm univ (fun r => (exp (-eigen τ r*s):ℂ)*normalizedCoeff v r) := by
  let a (r : ZMod N) := (exp (-eigen τ r*s):ℂ)*normalizedCoeff v r
  change ‖rmsCoordinates (fun i => (synth a (ZMod.finEquiv N i)).re)‖ ≤ blockNorm univ a
  apply (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ blockNorm univ a from sqrt_nonneg _)).mp
  rw [rmsCoordinates_norm_sq,block_sq,div_le_iff₀ (show 0<(N:ℝ) by exact_mod_cast NeZero.pos N)]
  rw [mul_comm,← synth_parseval]
  rw [← fin_sum]
  apply sum_le_sum
  intro i _
  exact sq_le_sq.mpr (by simpa using (Complex.abs_re_le_norm (synth a (ZMod.finEquiv N i))))

section Bands
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}

def bandSet (level : ι→ℕ) (d : ℕ) := univ.filter (fun r => level r=d)

def pathBudget (J : ℕ) (level : ι→ℕ) (rate : ℕ→ℝ) (a : ι→ℂ) :=
  ∑ d ∈ range (J+1), (rate d)⁻¹*blockNorm (bandSet level d) a

private theorem damp_block (a : ι→ℂ) (eig : ι→ℝ) (t : ℝ) (ht : 0≤t)
    (J : ℕ) (level : ι→ℕ) (hlevel : ∀ r, level r ≤ J) (rate : ℕ→ℝ)
    (he : ∀ r, rate (level r) ≤ eig r) :
    blockNorm univ (fun r => (exp (-eig r*t):ℂ)*a r) ≤
      ∑ d ∈ range (J+1), exp (-rate d*t)*blockNorm (bandSet level d) a := by
  let S := range (J+1)
  have hmap : ∀ r ∈ (univ:Finset ι), level r ∈ S := fun r _ => mem_range.mpr (by have := hlevel r; omega)
  have hd (d : ℕ) : ∑ r ∈ bandSet level d, ‖(exp (-eig r*t):ℂ)*a r‖^2 ≤
      (exp (-rate d*t)*blockNorm (bandSet level d) a)^2 := by
    rw [mul_pow,block_sq,Finset.mul_sum]
    apply sum_le_sum; intro r hr
    have hrd := (mem_filter.mp hr).2
    have hrate := he r
    rw [hrd] at hrate
    have ht' := exp_le_exp.mpr (show -(eig r)*t ≤ -(rate d)*t by nlinarith [mul_le_mul_of_nonneg_right hrate ht])
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _), mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le ht' 2) (sq_nonneg _)
  have hnon (d : ℕ) : 0 ≤ exp (-rate d*t)*blockNorm (bandSet level d) a := mul_nonneg (exp_nonneg _) (sqrt_nonneg _)
  apply (sq_le_sq₀ (show 0≤blockNorm univ _ from sqrt_nonneg _) (sum_nonneg (fun d _ => hnon d))).mp
  rw [block_sq, ← sum_fiberwise_of_maps_to hmap]
  exact (sum_le_sum (fun d _ => hd d)).trans (sum_sq_le_sq_sum_of_nonneg fun d _ => hnon d)

private theorem exp_area {b T : ℝ} (hb : 0<b) :
    (∫ t in (0:ℝ)..T, exp (-b*t)) ≤ b⁻¹ := by
  rw [intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr hb.ne'), integral_exp]
  simp only [mul_zero,exp_zero,smul_eq_mul, inv_neg]
  nlinarith [mul_nonneg (inv_nonneg.mpr hb.le) (exp_nonneg (-b*T))]

theorem referencePath_integral_le (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (v : Fin N→ℝ) {T : ℝ} (hT : 0≤T)
    (J : ℕ) (level : ZMod N→ℕ) (hlevel : ∀ r, level r ≤ J) (rate : ℕ→ℝ)
    (hpos : ∀ d, 0<rate d) (he : ∀ r, rate (level r) ≤ eigen τ r) :
    (∫ t in (0:ℝ)..T, ‖referencePath τ v t‖) ≤ pathBudget J level rate (normalizedCoeff v) := by
  let B := fun d => blockNorm (bandSet level d) (normalizedCoeff v)
  have hc : Continuous (referencePath τ v) := continuous_iff_continuousAt.mpr fun t => (referencePath_deriv τ hτ hτ' v t).continuousAt
  have hci (d : ℕ) : Continuous (fun t : ℝ => exp (-rate d*t)*B d) := by fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..T, ∑ d ∈ range (J+1), exp (-rate d*t)*B d := by
      apply intervalIntegral.integral_mono_on hT (hc.norm.intervalIntegrable _ _)
        ((continuous_finsetSum _ fun d _ => hci d).intervalIntegrable _ _)
      exact fun t ht => (norm_referencePath τ v t).trans (damp_block _ _ _ ht.1 J level hlevel rate he)
    _ ≤ _ := by
      rw [intervalIntegral.integral_finsetSum (fun d _ => (hci d).intervalIntegrable _ _),pathBudget]
      apply sum_le_sum; intro d _
      rw [intervalIntegral.integral_mul_const]
      exact mul_le_mul_of_nonneg_right (exp_area (T:=T) (hpos d)) (sqrt_nonneg _)

theorem pathBudget_mem (J : ℕ) (level : ι→ℕ) (rate : ℕ→ℝ)
    (a : ι→Ω→ℂ) (ha : ∀ r, MemLp (a r) 4 μ) :
    MemLp (fun z => pathBudget J level rate (fun r => a r z)) 4 μ := by
  apply memLp_finsetSum
  intro d _
  exact (block_mem (bandSet level d) a (fun r _ => ha r)).const_mul _

theorem pathBudget_lp4 (J : ℕ) (level : ι→ℕ) (rate cap : ℕ→ℝ)
    (a : ι→Ω→ℂ) (ha : ∀ r, MemLp (a r) 4 μ)
    (hc : ∀ d, 0≤cap d) (hr : ∀ d, 0<rate d)
    (hb : ∀ r, lpNorm (a r) 4 μ ≤ cap (level r)) :
    lpNorm (fun z => pathBudget J level rate (fun r => a r z)) 4 μ ≤
      ∑ d ∈ range (J+1), (rate d)⁻¹ * (√((bandSet level d).card : ℝ)*cap d) := by
  let X (d : ℕ) : Ω→ℝ := (rate d)⁻¹ • (fun z => blockNorm (bandSet level d) (fun i => a i z))
  have hX (d : ℕ) : MemLp (X d) 4 μ := (block_mem (bandSet level d) a (fun r _ => ha r)).const_smul _
  have hh : (fun z => pathBudget J level rate (fun i => a i z)) = ∑ d ∈ range (J+1), X d := by
    funext z; simp [pathBudget,X,Finset.sum_apply]
  rw [hh]
  apply (lpNorm_sum_le (fun d _ => hX d) (by norm_num)).trans
  apply sum_le_sum
  intro d _
  dsimp only [X]
  rw [lpNorm_const_smul, coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hr d).le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hr d).le)
  exact block_lp4 _ _ (fun r _ => ha r) _ (hc d) (fun r hx => (mem_filter.mp hx).2 ▸ hb r)

private theorem sqrt_geom (J : ℕ) :
    ∑ d ∈ range (J+1), √((2:ℝ)^d) ≤ 4*√((2:ℝ)^J) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ, Real.sqrt_mul (by positivity)]
    have h : (4:ℝ) ≤ 3*√2 := by nlinarith [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg (2:ℝ)]
    nlinarith [mul_le_mul_of_nonneg_left h (sqrt_nonneg ((2:ℝ)^J))]

/-- Comparable decay rates inside each dyadic shell. -/
theorem dyadic_lp4 (J : ℕ) (level : ι→ℕ) (a : ι→Ω→ℂ)
    (ha : ∀ r, MemLp (a r) 4 μ) (C c : ℝ) (hC : 0≤C) (hc : 0<c)
    (hb : ∀ r, lpNorm (a r) 4 μ ≤ C/((2:ℝ)^(level r))^2)
    (count : ∀ d, ((bandSet level d).card:ℝ) ≤ 5*(2:ℝ)^d) :
    lpNorm (fun z => pathBudget J level (fun d => c/((2:ℝ)^d)^2) (fun r => a r z)) 4 μ ≤
      4*(C/c)*√5*√((2:ℝ)^J) := by
  have hh := pathBudget_lp4 J level (fun d => c/((2:ℝ)^d)^2) (fun d => C/((2:ℝ)^d)^2)
    a ha (fun d => by positivity) (fun d => by positivity) hb
  apply hh.trans
  calc
    _ ≤ ∑ d ∈ range (J+1), ((C/c)*√5)*√((2:ℝ)^d) := by
      apply sum_le_sum; intro d _
      have hd := sqrt_le_sqrt (count d)
      rw [sqrt_mul (by norm_num : 0≤(5:ℝ))] at hd
      calc
        _ = C/c*√((bandSet level d).card:ℝ) := by field_simp
        _ ≤ _ := by rw [mul_assoc]; gcongr
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left (sqrt_geom J) (show 0≤C/c*√5 by positivity)]

end Bands

private theorem exists_rep (hodd : Odd N) (r : ZMod N) :
    ∃ k : ℤ, (k:ZMod N)=r ∧ k.natAbs≤N ∧
      (r=0 ∨ r=1 ∨ r= -1 → k.natAbs≤1) ∧ (r≠0 → r≠1 → r≠ -1 → Even k) := by
  have hn := NeZero.pos N
  by_cases hz : r=0
  · exact ⟨0, by simp [hz], by simp, by simp, by simp [hz]⟩
  by_cases hp : r=1
  · exact ⟨1, by simp [hp], by simpa using (show 1≤N by omega), by simp, by simp [hp]⟩
  by_cases hm : r= -1
  · exact ⟨-1, by simp [hm], by simpa using (show 1≤N by omega), by simp, by simp [hm]⟩
  obtain ⟨j,hj,hjN,he,hjr⟩ := even_representative hodd r hz
  have hjE : Even (j:ℤ) := by exact_mod_cast he
  by_cases h : j≤N
  · exact ⟨j, by simpa using hjr,by simpa using h, by simp [hz,hp,hm], fun _ _ _ => hjE⟩
  · let k : ℤ := (j:ℤ)-2*N
    have hk : k.natAbs≤N := by
      have h' : k < 0 := by dsimp [k]; omega
      have hab := Int.natCast_natAbs k
      rw [abs_of_neg h'] at hab
      dsimp [k] at hab
      omega
    refine ⟨k,by simp [k,hjr],hk,by simp [hz,hp,hm],fun _ _ _ => ?_⟩
    obtain ⟨i,hi⟩ := hjE
    exact ⟨i-N,by dsimp [k]; omega⟩

/-- The three label frequencies use 0 and ±1. Every other residue uses its even
representative with absolute value at most the grid size. -/
def representative (ho : Odd N) (r : ZMod N) := (exists_rep ho r).choose

private theorem rep_spec (ho : Odd N) (r : ZMod N) :
    ((representative ho r:ℤ):ZMod N)=r ∧ (representative ho r).natAbs≤N ∧
    (r=0 ∨ r=1 ∨ r= -1 → (representative ho r).natAbs≤1) ∧
    (r≠0 → r≠1 → r≠ -1 → Even (representative ho r)) :=
  (exists_rep ho r).choose_spec

def shell (ho : Odd N) (r : ZMod N) := ((representative ho r).natAbs+1).log2

theorem shell_le (ho : Odd N) (r : ZMod N) : shell ho r≤(N+1).log2 := by
  apply (Nat.le_log2 (Nat.succ_ne_zero N)).2
  exact (Nat.log2_self_le (Nat.succ_ne_zero _)).trans (Nat.succ_le_succ (rep_spec ho r).2.1)

private theorem shell_bounds (ho : Odd N) (r : ZMod N) :
    2^(shell ho r) ≤ (representative ho r).natAbs+1 ∧
      (representative ho r).natAbs+1 < 2^(shell ho r+1) :=
  ⟨Nat.log2_self_le (Nat.succ_ne_zero _), Nat.lt_log2_self⟩

theorem shell_count (ho : Odd N) (d : ℕ) : ((bandSet (shell ho) d).card:ℝ)≤5*(2:ℝ)^d := by
  let K : ℕ := 2^(d+1)
  have inj : Function.Injective (representative ho) := by
    intro r s h
    rw [← (rep_spec ho r).1,← (rep_spec ho s).1]
    exact congrArg (fun k : ℤ => (k:ZMod N)) h
  have h := card_le_card_of_injOn (s:=bandSet (shell ho) d) (t:=Icc (-(K:ℤ)) (K:ℤ)) (representative ho) (fun r hr => by
    have hrd := (mem_filter.mp hr).2
    have hu := (shell_bounds ho r).2
    rw [hrd] at hu
    have hab := Int.natCast_natAbs (representative ho r)
    have hnat : (representative ho r).natAbs≤K := Nat.le_of_lt (Nat.lt_of_succ_lt hu)
    have hb : |representative ho r| ≤ (K:ℤ) := hab ▸ (by exact_mod_cast hnat : ((representative ho r).natAbs:ℤ)≤K)
    exact mem_Icc.mpr (abs_le.mp hb)) inj.injOn
  have hK : (0:ℤ)≤K := Int.natCast_nonneg _
  have hI := Int.card_Icc_of_le (-(K:ℤ)) K (by linarith)
  have hp : 0<2^d := Nat.two_pow_pos d
  have hcard : (Finset.Icc (-(K:ℤ)) (K:ℤ)).card=K+1+K := by exact_mod_cast (by push_cast; linarith : ((Finset.Icc (-(K:ℤ)) (K:ℤ)).card:ℤ)=((K+1+K:ℕ):ℤ))
  rw [hcard] at h
  have hnat : (bandSet (shell ho) d).card≤5*2^d := by dsimp only [K] at h; rw [pow_succ] at h; omega
  exact_mod_cast hnat

omit [NeZero N] in
private theorem coeff_le_eigen {τ : ℝ} (ht : 0≤τ) (hu : τ≤2) {k : ℤ} {r : ZMod N}
    (hk : (k:ZMod N)=r) : tangentCoeff τ k ≤ eigen τ r := by
  let f (j : ℤ) := if (j:ZMod N)=r then tangentCoeff τ j else 0
  have hs : Summable f := by
    refine ((tangentCoeff_summable τ ht hu).indicator {j : ℤ | (j:ZMod N)=r}).congr fun j => ?_
    simp [Set.indicator_apply,f]
  have hp (j : ℤ) : 0≤f j := by dsimp [f]; split <;> simp_all only [tangentCoeff_nonneg ht,le_refl]
  have hl := hs.le_tsum k (fun j _ => hp j)
  simpa only [f,hk,ite_true,eigen,aliasValue] using hl

def shellConstant : ℝ := 1/(32*(1+π^2))

theorem shellConstant_pos : 0<shellConstant := by unfold shellConstant; positivity

theorem shell_eigen (ho : Odd N) {τ : ℝ} (ht : 1/2≤τ) (hu : τ≤2) (r : ZMod N) :
    shellConstant/((2:ℝ)^(shell ho r))^2 ≤ eigen τ r := by
  let k := representative ho r
  let D := (2:ℝ)^(shell ho r)
  have ht0 : 0≤τ := by linarith
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  have hD0 : 0<D := by linarith
  have hπ := pi_pos
  have hspec := rep_spec ho r
  change ((k:ZMod N)=r) ∧ _ at hspec
  apply le_trans _ (coeff_le_eigen ht0 hu hspec.1)
  change shellConstant/D^2 ≤ tangentCoeff τ k
  have hsmall : shellConstant/D^2≤1/8 := by
    rw [shellConstant,div_div,(div_le_div_iff₀ (by positivity) (by norm_num))]
    have hD1 := one_le_pow₀ hD (n:=2)
    nlinarith [mul_nonneg (sq_nonneg π) (sq_nonneg D)]
  by_cases hk : k=0
  · simp [hk,tangentCoeff,CircleSpectrum.ntkEven]
    change shellConstant/D^2 ≤ (2+τ)/π^2
    rw [shellConstant,div_div,div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 ≤ (2+τ)*D^2 := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hD)
    nlinarith only [mul_le_mul_of_nonneg_left h1 (show 0≤π^2 by positivity),h1, sq_nonneg π]
  by_cases h1 : k.natAbs=1
  · have hne : ¬Even k := by rcases (Int.natAbs_eq_iff.mp h1) with h|h <;> rw [h] <;> decide
    rw [tangentCoeff,ite_eq_right hne,ite_eq_left h1]
    linarith
  have hn : r≠0 ∧ r≠1 ∧ r≠ -1 := by
    by_contra! q
    have hsmallk : k.natAbs≤1 := hspec.2.2.1 (by tauto)
    have hzero : k.natAbs=0 := by omega
    exact hk (Int.natAbs_eq_zero.mp hzero)
  have he := hspec.2.2.2 hn.1 hn.2.1 hn.2.2
  apply le_trans _ (even_mode_lower ht0 he hk)
  have hkup := (shell_bounds ho r).2
  rw [pow_succ] at hkup
  have hkr : (k.natAbs:ℝ)≤2*D := by dsimp only [D]; exact_mod_cast (show k.natAbs≤2*2^(shell ho r) by omega)
  rw [Nat.cast_natAbs,Int.cast_abs] at hkr
  have hk2 : (k:ℝ)^2≤4*D^2 := by nlinarith [sq_le_sq₀ (abs_nonneg (k:ℝ)) (show 0≤2*D by positivity) |>.2 hkr,sq_abs (k:ℝ)]
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk
  rw [shellConstant,div_div,div_le_div_iff₀ (by positivity) (by positivity)]
  have hτD : D^2/2 ≤ τ*D^2 := by nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg D)]
  nlinarith only [mul_le_mul_of_nonneg_left hk2 (sq_nonneg π),mul_le_mul_of_nonneg_left hτD (sq_nonneg π),hτD,sq_nonneg D, mul_nonneg (sq_nonneg π) (sq_nonneg D)]
open CircleResidualSpectrum CircleEscapeBridge CircleFlowPath

private theorem modeConstant_nonneg : 0≤modeConstant :=
  lpNorm_nonneg.trans (initialCoeff_uniform (N:=1) (m:=1) (by decide) 0).2

private theorem mode_shell_cap {m : ℕ} (hm : 0<m) (ho : Odd N) (r : ZMod N) :
    lpNorm (initialCoeff N m r) 4 (seedLaw m) ≤ (4*modeConstant)/((2:ℝ)^(shell ho r))^2 := by
  let k := representative ho r
  let D := (2:ℝ)^(shell ho r)
  have hD : 0<D := by dsimp [D]; positivity
  have hspec := rep_spec ho r
  have hd : D≤(k.natAbs:ℝ)+1 := by dsimp only [D]; exact_mod_cast (shell_bounds ho r).1
  by_cases hs : r=0 ∨ r=1 ∨ r= -1
  · have hsmall : k.natAbs≤1 := hspec.2.2.1 hs
    have hh : (k.natAbs:ℝ) ≤ 1 := by exact_mod_cast hsmall
    have hp : D^2≤4 := by nlinarith [sq_le_sq₀ hD.le (by norm_num : (0:ℝ)≤2) |>.2 (show D≤2 by linarith)]
    apply (initialCoeff_uniform hm r).2.trans
    apply (le_div_iff₀ (sq_pos_of_pos hD)).2
    nlinarith [mul_le_mul_of_nonneg_left hp modeConstant_nonneg]
  have hn : r≠0 ∧ r≠1 ∧ r≠ -1 := by tauto
  have hkn : 2≤k.natAbs := by
    by_contra! h
    have hh : k.natAbs=0 ∨ k.natAbs=1 := by omega
    rcases hh with hz | h1
    · have hz' := Int.natAbs_eq_zero.mp hz
      exact hn.1 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hz']; simp))
    · rcases Int.natAbs_eq_iff.mp h1 with hp | hp
      · exact hn.2.1 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hp]; simp))
      · exact hn.2.2 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hp]; simp))
  apply (initialCoeff_high hm ho hn.1 hn.2.1 hn.2.2 hspec.1 (hspec.2.2.2 hn.1 hn.2.1 hn.2.2) hkn hspec.2.1).2.trans
  change modeConstant/(1+|(k:ℝ)|)^2≤4*modeConstant/D^2
  rw [Nat.cast_natAbs,Int.cast_abs] at hd
  calc
    _ ≤ modeConstant/D^2 := by
      apply div_le_div_of_nonneg_left modeConstant_nonneg (by positivity)
      exact pow_le_pow_left₀ hD.le (by linarith) _
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [modeConstant_nonneg]) (sq_nonneg _)

/-- The freeze-at-initialization residual uses the actual finite network and the public grid teacher. -/
def rawResidual (N m : ℕ) (z : Seed m) : Fin N → ℝ :=
  residual (circleInput N) (circleLabel N) (1/√(m:ℝ)) z

theorem normalizedCoeff_raw (m : ℕ) (r : ZMod N) (z : Seed m) :
    normalizedCoeff (rawResidual N m z) r = initialCoeff N m r z := by
  simp only [normalizedCoeff,rawResidual,CircleFlowPath.residual,CircleFlowMoments.output_eq_complex,initialCoeff]
  rfl

/-- A horizon-independent seed functional controlling the integrated norm of the actual
grid reference. All frequencies come from the network and training labels. -/
def seedBudget (ho : Odd N) (m : ℕ) (z : Seed m) : ℝ :=
  pathBudget (N+1).log2 (shell ho) (fun d => shellConstant/((2:ℝ)^d)^2)
    (fun r => initialCoeff N m r z)

theorem seedBudget_nonneg (ho : Odd N) (m : ℕ) (z : Seed m) : 0≤seedBudget ho m z := by
  unfold seedBudget pathBudget
  apply sum_nonneg
  exact fun _ _ => mul_nonneg (inv_nonneg.mpr (div_nonneg shellConstant_pos.le (sq_nonneg _))) (sqrt_nonneg _)

theorem seedBudget_continuous (ho : Odd N) (m : ℕ) : Continuous (seedBudget ho m) := by
  unfold seedBudget pathBudget blockNorm initialCoeff
  simp only [ZMod.dft_apply,smul_eq_mul]
  unfold CircleEscape.output CircleEscape.feature CircleEscapeBridge.initial
  simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  fun_prop

theorem seedBudget_mem {m : ℕ} (hm : 0<m) (ho : Odd N) :
    MemLp (seedBudget ho m) 4 (seedLaw m) :=
  pathBudget_mem _ _ _ _ (fun r => (initialCoeff_uniform hm r).1)

def budgetConstant : ℝ := 16*(modeConstant/shellConstant)*√5*√2

theorem budgetConstant_nonneg : 0≤budgetConstant := by
  unfold budgetConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (div_nonneg modeConstant_nonneg shellConstant_pos.le)) (sqrt_nonneg _)) (sqrt_nonneg _)

/-- The fourth norm of the integrated residual budget grows at most as the
square root of the odd grid size, uniformly over every positive finite width. -/
theorem seedBudget_lp4 {m : ℕ} (hm : 0<m) (ho : Odd N) :
    lpNorm (seedBudget ho m) 4 (seedLaw m) ≤ budgetConstant*√(N:ℝ) := by
  have h := dyadic_lp4 (N+1).log2 (shell ho) (initialCoeff N m)
    (fun r => (initialCoeff_uniform hm r).1) (4*modeConstant) shellConstant
    (mul_nonneg (by norm_num) modeConstant_nonneg) shellConstant_pos (mode_shell_cap hm ho) (shell_count ho)
  apply h.trans
  have hn := NeZero.pos N
  have hk : (2:ℝ)^((N+1).log2) ≤ 2*(N:ℝ) := by
    exact_mod_cast (Nat.log2_self_le (Nat.succ_ne_zero N)).trans (show N+1≤2*N by omega)
  have hroot := sqrt_le_sqrt hk
  rw [sqrt_mul (by norm_num : (0:ℝ)≤2)] at hroot
  unfold budgetConstant
  have hc := mul_le_mul_of_nonneg_left hroot (show 0≤4*((4*modeConstant)/shellConstant)*√5 from
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (by norm_num) modeConstant_nonneg) shellConstant_pos.le)) (sqrt_nonneg _))
  convert hc using 1; ring

theorem seedBudget_dominates {m : ℕ} (ho : Odd N) {τ T : ℝ} (ht : 1/2≤τ) (hu : τ≤2)
    (hT : 0≤T) (z : Seed m) :
    (∫ s in (0:ℝ)..T, ‖referencePath τ (rawResidual N m z) s‖) ≤ seedBudget ho m z := by
  have h := referencePath_integral_le τ (by linarith) hu (rawResidual N m z) hT (N+1).log2
    (shell ho) (shell_le ho) (fun d => shellConstant/((2:ℝ)^d)^2)
    (fun d => div_pos shellConstant_pos (by positivity)) (shell_eigen ho ht hu)
  simpa only [seedBudget,show normalizedCoeff (rawResidual N m z)=_ from funext fun r => normalizedCoeff_raw m r z] using h

end CircleSpectralPathLength
