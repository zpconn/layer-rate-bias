module

public import CircleInitialResidualSecond
public import CircleSpectralPathLength
import all CircleInitialResidualSecond
import all CircleSpectralPathLength
import all CircleResidualSpectrum
import all CircleReferenceMoments
import all CircleFlowMoments
import all CircleInitializationConcentration
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleFlowPath
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Exact second moments of sampled Gaussian residual modes and their grouped path budget. -/
@[expose] public section
noncomputable section
namespace CircleGroupedResidual
open Real MeasureTheory ProbabilityTheory CircleInitialResidualSecond CircleInitializationConcentration
  CircleReferenceMoments CircleKernelIdentification CircleGridSpectrum CircleSpectralPathLength
  CircleEscapeBridge CircleFlowPath CircleResidualSpectrum
open scoped ComplexConjugate
variable {N m : ℕ} [NeZero N]

private theorem empirical_cov {f g : Atom → ℝ} (hm : 0<m) (hf : MemLp f 2 atomLaw)
    (hg : MemLp g 2 atomLaw) :
    covariance (sampleAverage f) (sampleAverage g) (seedLaw m) = covariance f g atomLaw/m := by
  have eq : sampleAverage (m:=m) (f+g) = sampleAverage f+sampleAverage g := by
    ext z;simp [sampleAverage,Finset.sum_add_distrib,mul_add]
  have v := average_variance hm (hf.add hg)
  rw [eq,variance_add (average_mem hf) (average_mem hg),variance_add hf hg,
    average_variance hm hf,average_variance hm hg] at v
  have hm' : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp [hm'] at v ⊢;linarith

omit [NeZero N] in
private theorem pred_eq (hm : 0<m) (i : Fin N) : prediction N m i = fun z =>
    √m*sampleAverage (term (physicalAngle i)) z := by
  have hs : √(m:ℝ)≠0 := sqrt_ne_zero'.mpr (by exact_mod_cast hm)
  have scale : √(m:ℝ)*(m:ℝ)⁻¹ = 1/√(m:ℝ) := by
    field_simp [hs];nlinarith [sq_sqrt (Nat.cast_nonneg m),show (0:ℝ)<m by exact_mod_cast hm]
  ext z
  rw [prediction,CircleFlowMoments.output_eq_complex,CircleEscape.output,sampleAverage,←mul_assoc,scale]
  congr 1
  simp only [term,initial,feature_coord]

/-- Every pair of grid outputs has the actual sampled ReLU covariance for every positive width. -/
theorem prediction_cov (hm : 0<m) (i j : Fin N) :
    covariance (prediction N m i) (prediction N m j) (seedLaw m) = sampledMatrix 0 i j := by
  let u := physicalAngle i
  let v := physicalAngle j
  have hi := term_moments u
  have hj := term_moments v
  have c : covariance (term u) (term v) atomLaw = sampledMatrix 0 i j := by
    rw [covariance_eq_sub hi.1 hj.1,hi.2.1,hj.2.1,mul_zero,sub_zero,sampledMatrix_cartesian]
    change (∫ z, (fun p : ℝ × (ℝ×ℝ) => (p.1*phi u p.2)*(p.1*phi v p.2))
      (CircleReferenceMoments.split z) ∂atomLaw)=_
    rw [CircleReferenceMoments.split_preserving.integral_comp' (fun p : ℝ × (ℝ×ℝ) => (p.1*phi u p.2)*(p.1*phi v p.2))]
    simp_rw [show ∀ p : ℝ×(ℝ×ℝ), (p.1*phi u p.2)*(p.1*phi v p.2)=p.1^2*(phi u p.2*phi v p.2) by intro p;ring]
    rw [integral_prod_mul (fun t : ℝ => t^2) (fun w => phi u w*phi v w),CircleKernelIdentification.gaussian_second]
    simp [cartesianKernel,cartesianProduct,u,v,phi]
  rw [pred_eq hm i,pred_eq hm j,covariance_const_mul_left,covariance_const_mul_right,
    empirical_cov hm hi.1 hj.1,c]
  have h : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp [h];rw [sq_sqrt (Nat.cast_nonneg m)];ring

private def proj (p v : Fin N → ℝ) := (∑ i, p i*v i)/N

omit [NeZero N] in
private theorem raw_moments (hm : 0<m) (i : Fin N) :
    MemLp (raw N m i) 2 (seedLaw m) ∧ (∫ z,raw N m i z ∂seedLaw m) = -circleLabel N i := by
  have h := prediction_moments hm i
  refine ⟨h.1.sub (memLp_const _),?_⟩
  unfold raw
  rw [integral_sub (h.1.integrable (by norm_num)) (integrable_const _),h.2.1];simp

private theorem raw_cov (hm : 0<m) (i j : Fin N) :
    covariance (raw N m i) (raw N m j) (seedLaw m) = sampledMatrix 0 i j := by
  unfold raw
  rw [covariance_sub_const_left ((prediction_moments hm i).1.integrable (by norm_num)),
    covariance_sub_const_right ((prediction_moments hm j).1.integrable (by norm_num)),prediction_cov hm]

private theorem projected_sq (hm : 0<m) (p : Fin N → ℝ) :
    let P := fun z : Seed m => proj p (rawResidual N m z)
    MemLp P 2 (seedLaw m) ∧
    (∫ z, (P z)^2 ∂seedLaw m) =
      (∑ i, p i*((∑ j, sampledMatrix 0 i j*p j)/N))/N + (proj p (circleLabel N))^2 := by
  intro P
  let X i := fun z : Seed m => p i*raw N m i z
  let F z := ∑ i,X i z
  have mx (i : Fin N) : MemLp (X i) 2 (seedLaw m) := (raw_moments hm i).1.const_mul _
  have mf : MemLp F 2 (seedLaw m) := memLp_finsetSum _ (fun i _ => mx i)
  have mp : MemLp P 2 (seedLaw m) := by
    change MemLp (fun z => F z / N) 2 _
    simpa only [div_eq_mul_inv] using mf.mul_const (N:ℝ)⁻¹
  have mean : (∫ z, P z ∂seedLaw m) = -proj p (circleLabel N) := by
    change (∫ z,F z/N ∂seedLaw m) = _
    rw [integral_div,show (∫ z,F z ∂seedLaw m)=∑ i,∫ z,X i z ∂seedLaw m from
      integral_finsetSum _ (fun i _ => (mx i).integrable (by norm_num))]
    simp only [X,integral_const_mul,(raw_moments hm _).2,mul_neg,Finset.sum_neg_distrib,neg_div,proj]
  have cov (i j : Fin N) : covariance (X i) (X j) (seedLaw m)=p i*(p j*sampledMatrix 0 i j) := by
    unfold X;rw [covariance_const_mul_left,covariance_const_mul_right,raw_cov hm]
  have var : variance P (seedLaw m)=
      (∑ i, p i*((∑ j, sampledMatrix 0 i j*p j)/N))/N := by
    change variance (fun z => F z/N) _=_
    simp_rw [div_eq_mul_inv (F _)]
    rw [variance_mul_const,← covariance_self mf.aemeasurable,covariance_fun_sum_left mx mf]
    simp_rw [show ∀ i, covariance (X i) F (seedLaw m) = ∑ j,covariance (X i) (X j) (seedLaw m) from
      fun i => covariance_fun_sum_right mx (mx i),cov]
    simp_rw [←Finset.mul_sum,←mul_div_assoc,←Finset.sum_div]
    simp_rw [mul_comm (p _) (sampledMatrix _ _ _)]
    ring
  have v := variance_eq_sub mp
  rw [var,mean,neg_sq] at v;simp only [Pi.pow_apply] at v;exact ⟨mp,by linarith⟩


private def component (r : ZMod N) (a : ℂ) (i : Fin N) :=
  (a*char r (ZMod.finEquiv N i)).re

private theorem component_eigen (r : ZMod N) (a : ℂ) (i : Fin N) :
    (∑ j,sampledMatrix 0 i j*component r a j)/N=eigen 0 r*component r a i := by
  let coeff (k : ZMod N) := if k=r then a else 0
  have h := matrix_synth 0 (by norm_num) (by norm_num) coeff i
  have se (q : ZMod N) : synth coeff q=a*char r q := by simp [synth,coeff,ite_mul]
  have te (q : ZMod N) : synth (fun k => (eigen 0 k:ℂ)*coeff k) q=(eigen 0 r:ℂ)*(a*char r q) := by
    simp [synth,coeff,mul_ite,ite_mul,mul_assoc]
  simpa only [se,te,Complex.re_ofReal_mul,component] using h

private theorem norm_split (r : ZMod N) (v : Fin N → ℝ) :
    ‖normalizedCoeff v r‖^2 = (proj (component r 1) v)^2+(proj (component r Complex.I) v)^2 := by
  have rep : normalizedCoeff v r =
      (∑ j : Fin N, conj (char r (ZMod.finEquiv N j))*(v j:ℂ))/N := by
    rw [normalizedCoeff,ZMod.dft_apply,← (ZMod.finEquiv N).toEquiv.sum_comp]
    simp [smul_eq_mul,char,← AddChar.map_neg_eq_conj,mul_comm]
  rw [rep,Complex.sq_norm,Complex.normSq_apply]
  simp [proj,component,Complex.div_natCast_re,Complex.div_natCast_im,Complex.re_sum,Complex.im_sum,sq]

private theorem component_unit (r : ZMod N) (i : Fin N) :
    component r 1 i^2 + component r Complex.I i^2 = 1 := by
  have hi : ‖char r (ZMod.finEquiv N i)‖=1 := by simp [char,AddChar.norm_apply]
  have := Complex.sq_norm (char r (ZMod.finEquiv N i))
  rw [hi,Complex.normSq_apply] at this
  simpa [component,sq] using this.symm

/-- Exact second moment of each complex residual coefficient, including its teacher phase. -/
theorem residual_mode_second (hm : 0<m) (r : ZMod N) :
    (∫ z, ‖normalizedCoeff (rawResidual N m z) r‖^2 ∂seedLaw m) =
      eigen 0 r + ‖normalizedCoeff (circleLabel N) r‖^2 := by
  let p := component r 1
  let q := component r Complex.I
  have u (a : ℂ) : (∑ i,component r a i*((∑ j,sampledMatrix 0 i j*component r a j)/N))/N =
      eigen 0 r *((∑ i,(component r a i)^2)/N) := by
    simp_rw [component_eigen,show ∀ i, component r a i*(eigen 0 r*component r a i)=eigen 0 r*(component r a i)^2 by intro i;ring]
    rw [← Finset.mul_sum,mul_div_assoc]
  have unit : ((∑ i,p i^2)/N)+((∑ i,q i^2)/N)=1 := by
    rw [←add_div,← Finset.sum_add_distrib]
    simp only [p,q,component_unit,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,div_self (NeZero.ne (N:ℝ))]
  have P := projected_sq hm p
  have Q := projected_sq hm q
  simp only [p,q,u] at P Q
  simp_rw [norm_split]
  rw [integral_add P.1.integrable_sq Q.1.integrable_sq,P.2,Q.2]
  dsimp only [p,q] at unit
  linear_combination eigen 0 r*unit

/-- The finite groups share no independence assumption. Each group's L² cost
uses the sum of exact second moments of its modes. -/
def groupCost (N : ℕ) [NeZero N] (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) :=
  ∑ d ∈ Finset.range (J+1), (rate d)⁻¹ * √(∑ r ∈ bandSet level d,
    (eigen 0 r+‖normalizedCoeff (circleLabel N) r‖^2))

def groupSeed (N m : ℕ) [NeZero N] (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) (z : Seed m) :=
  pathBudget J level rate (fun r => initialCoeff N m r z)


private theorem lp2_power {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : MemLp f 2 μ) : lpNorm f 2 μ ^ 2 = ∫ z, f z^2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.norm_eq_abs,sq_abs]
  rw [← Real.rpow_natCast,← Real.rpow_mul (integral_nonneg (fun z => sq_nonneg _))]
  norm_num

private theorem block_lp2 (hm : 0<m) (S : Finset (ZMod N)) :
    lpNorm (fun z => blockNorm S (fun i => initialCoeff N m i z)) 2 (seedLaw m) =
      √(∑ r ∈ S,(eigen 0 r+‖normalizedCoeff (circleLabel N) r‖^2)) := by
  have h (r : ZMod N) := (initialCoeff_uniform (N:=N) hm r).1
  have B := (block_mem S _ (fun r _ => h r)).mono_exponent (by norm_num : (2:ENNReal)≤4)
  rw [←sqrt_sq (show 0≤lpNorm _ _ _ from lpNorm_nonneg),lp2_power B]
  congr 1
  simp_rw [block_sq]
  have hi (r : ZMod N) : Integrable (fun z => ‖initialCoeff N m r z‖^2) (seedLaw m) :=
    (h r |>.mono_exponent (by norm_num : (2:ENNReal)≤4)).norm.integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [normalizedCoeff_raw] using residual_mode_second hm r

/-- Minkowski across the chosen groups, after using their exact second moments. -/
theorem group_lp2 (hm : 0<m) (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) (hr : ∀ d,0<rate d) :
    MemLp (groupSeed N m J level rate) 2 (seedLaw m) ∧
    lpNorm (groupSeed N m J level rate) 2 (seedLaw m) ≤ groupCost N J level rate := by
  have ha (r : ZMod N) := (initialCoeff_uniform (N:=N) hm r).1
  let X (d : ℕ) : Seed m→ℝ := (rate d)⁻¹ • (fun z => blockNorm (bandSet level d) (fun i => initialCoeff N m i z))
  have hx (d : ℕ) : MemLp (X d) 2 (seedLaw m) :=
    ((block_mem (bandSet level d) _ (fun r _ => ha r)).mono_exponent (by norm_num : (2:ENNReal)≤4)).const_smul _
  have eq : groupSeed N m J level rate = ∑ d ∈ Finset.range (J+1),X d := by
    funext z;simp [groupSeed,pathBudget,X,Finset.sum_apply]
  rw [eq]
  refine ⟨memLp_finsetSum' _ (fun d _ => hx d),(lpNorm_sum_le (fun d _ => hx d) (by norm_num)).trans_eq ?_⟩
  unfold groupCost
  apply Finset.sum_congr rfl;intro d _
  dsimp only [X]
  rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hr d)),block_lp2 hm]

theorem group_tail (hm : 0<m) (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) (hr : ∀ d,0<rate d)
    {u : ℝ} (hu : 0<u) :
    (seedLaw m).real {z | u < groupSeed N m J level rate z} ≤ (groupCost N J level rate)^2/u^2 := by
  let Z := groupSeed N m J level rate
  have h := group_lp2 hm J level rate hr
  have mark := mul_meas_ge_le_integral_of_nonneg (μ:=seedLaw m) (f:=fun z => (Z z)^2)
    (ae_of_all _ fun z => sq_nonneg _) h.1.integrable_sq (u^2)
  rw [←lp2_power h.1] at mark
  apply (measureReal_mono (s₂:={z : Seed m | u^2≤(Z z)^2}) (fun z hz =>
    pow_le_pow_left₀ hu.le (le_of_lt hz) 2)).trans
  apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
  rw [mul_comm]
  exact mark.trans (pow_le_pow_left₀ lpNorm_nonneg h.2 2)

/-- The grouped budget exceeds its manuscript threshold with probability at most δ/6. -/
theorem group_design_tail (hm : 0<m) (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) (hr : ∀ d,0<rate d)
    (hF : 0<groupCost N J level rate) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw m).real {z | √(6/δ)*groupCost N J level rate < groupSeed N m J level rate z} ≤ δ/6 := by
  apply (group_tail hm J level rate hr (mul_pos (sqrt_pos.mpr (by positivity)) hF)).trans_eq
  rw [mul_pow,sq_sqrt (by positivity : 0≤6/δ)]
  field_simp


/-- The three nonzero teacher frequencies, with coincidences automatically
counted on grids smaller than three. -/
theorem normalized_teacher (r : ZMod N) :
    normalizedCoeff (circleLabel N) r =
      (if (0:ZMod N)=r then 1 else 0) +
      (2:ℂ)⁻¹*((if (1:ZMod N)=r then 1 else 0)+(if (-1:ZMod N)=r then 1 else 0)) := by
  have hl : label (N:=N)=char 0+(2:ℂ)⁻¹ • (char 1+char (-1)) := by
    ext1 i
    have hneg : char (-1) i=conj (char 1 i) := by simp [char,AddChar.map_neg_eq_conj]
    rw [Pi.add_apply,Pi.smul_apply,Pi.add_apply,hneg,char_grid]
    unfold label
    simp only [char,zero_mul,AddChar.map_zero_eq_one,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_one]
    rw [Complex.add_conj];push_cast;ring
  change ZMod.dft (label (N:=N)) r/(N:ℂ)=_
  rw [hl,map_add,map_smul,map_add]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_div,mul_div_assoc,char_dft]

theorem groupSeed_measurable (J : ℕ) (level : ZMod N → ℕ) (rate : ℕ → ℝ) :
    Measurable (groupSeed N m J level rate) := by
  have coeff (r : ZMod N) : Measurable (fun z : Seed m => normalizedCoeff (rawResidual N m z) r) := by
    unfold normalizedCoeff rawResidual CircleFlowPath.residual CircleFlowPath.output CircleFlowPath.pre
    simp only [ZMod.dft_apply,smul_eq_mul]
    fun_prop
  unfold groupSeed pathBudget blockNorm
  simp_rw [←normalizedCoeff_raw]
  fun_prop

end CircleGroupedResidual
