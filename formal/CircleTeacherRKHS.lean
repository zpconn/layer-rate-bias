module

public import CircleReferenceMoments
public import CircleStats
import all CircleReferenceMoments
import all CircleKernelIdentification
import all CircleGridSpectrum
import all CircleSpectrum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! The covariance feature Hilbert space, its population representer and power
on the odd grid. The Fourier norm is evaluated at the prescribed cosine teacher. -/

public section
noncomputable section
namespace CircleTeacherRKHS
open MeasureTheory Real Finset CircleGridSpectrum CircleSpectrum CircleKernelIdentification
  CircleReferenceMoments CircleTangentDrift
open scoped InnerProductSpace

/-- Hidden Gaussian feature-space model of the circle covariance RKHS. -/
abbrev H := Lp ℝ 2 standardPair

def sectionAt (u : ℝ) : H := (phi_mem 2 u).toLp (phi u)
def q : H := (pop_mem 2).toLp populationFeature
def gridSection {N : ℕ} (i : Fin N) : H := sectionAt (physicalAngle i)
def covarianceWeight (n : ℕ) := c0/(c0+S n)
def designWeight (n : ℕ) (_ : Fin (n+1)) := covarianceWeight n/(n+1)

theorem covariance (u v : ℝ) : ⟪sectionAt u,sectionAt v⟫_ℝ=cartesianKernel 0 u v := by
  rw [MeasureTheory.L2.inner_def]
  simp only [cartesianKernel,zero_mul,add_zero,cartesianProduct]
  apply integral_congr_ae
  filter_upwards [(phi_mem 2 u).coeFn_toLp,(phi_mem 2 v).coeFn_toLp] with w hw hv
  change (sectionAt v w)*(sectionAt u w)=_
  rw [show sectionAt v w=phi v w from hv, show sectionAt u w=phi u w from hw]
  simp [phi,mul_comm]

theorem grid_covariance {N : ℕ} [NeZero N] (i j : Fin N) :
    ⟪gridSection i,gridSection j⟫_ℝ=sampledMatrix 0 i j := by
  rw [sampledMatrix_cartesian]; exact covariance _ _

theorem q_section (u : ℝ) : ⟪q,sectionAt u⟫_ℝ=c0 := by
  rw [MeasureTheory.L2.inner_def,←populationFeature_mixed u]
  apply integral_congr_ae
  filter_upwards [(pop_mem 2).coeFn_toLp,(phi_mem 2 u).coeFn_toLp] with w hq hφ
  change (sectionAt u w)*(q w)=_
  rw [show sectionAt u w=phi u w from hφ,show q w=populationFeature w from hq]
  simp [phi,mul_comm]

theorem q_norm : ‖q‖^2=c0 := by
  rw [←real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def,←populationFeature_second]
  apply integral_congr_ae
  filter_upwards [(pop_mem 2).coeFn_toLp] with w hq
  change q w*q w=_
  rw [show q w=populationFeature w from hq,sq]

private theorem alias_zero (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    aliasValue (tangentCoeff 0) (0:ZMod (n+1))=c0+S n := by
  rw [constant_alias_eq hn ho 0 (by norm_num) (by norm_num), S_eq_alias_sum]
  simp [k0,c0,ntkEven,covEven]

private theorem denom_pos (n : ℕ) : 0<c0+S n := by
  rw [S_eq_alias_sum]
  exact add_pos_of_pos_of_nonneg (by unfold c0; positivity)
    (tsum_nonneg (fun _ => by unfold covEven; positivity))

theorem normal_equations (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (i : Fin (n+1)) :
    ∑ j,designWeight n j*⟪gridSection j,gridSection i⟫_ℝ=⟪q,gridSection i⟫_ℝ := by
  simp only [grid_covariance,designWeight,←Finset.mul_sum]
  rw [show ⟪q,gridSection i⟫_ℝ=c0 from q_section _,div_mul_eq_mul_div,
    mul_div_assoc,←Nat.cast_add_one,sampled_column 0 (by norm_num) (by norm_num),alias_zero n hn ho,covarianceWeight]
  exact div_mul_cancel₀ _ (denom_pos n).ne'

theorem power (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    ‖q-∑ i,designWeight n i • gridSection i‖=√(minVariance n) := by
  have hp := CircleStats.power_squared q gridSection (designWeight n) (normal_equations n hn ho)
  simp only [gridSection,q_section,designWeight,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add_one,q_norm] at hp
  have he : ‖q-∑ i,designWeight n i • gridSection i‖^2=minVariance n := by
    simp only [designWeight,gridSection]
    rw [hp,minVariance,covarianceWeight]
    field_simp [(denom_pos n).ne',show (n:ℝ)+1≠0 by positivity]
    ring
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt he)

private theorem kernel_cont (a : ℝ) : Continuous (cartesianKernel 0 a) := by
  have hc : Continuous (fun u : ℝ => (periodicTangent 0 ((u-a:ℝ):AddCircle (π- -π))).re) := by
    exact Complex.continuous_re.comp ((periodicTangent 0).continuous.comp
      (AddCircle.continuous_mk' _ |>.comp (continuous_id.sub continuous_const)))
  exact hc.congr fun v => periodicTangent_cartesian 0 a v

private theorem diag (a : ℝ) : cartesianKernel 0 a a=cartesianKernel 0 0 0 := by
  simp only [cartesian_kernel_isotropic,sub_self]

private theorem section_cont : Continuous sectionAt := by
  apply continuous_iff_continuousAt.2
  intro a
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hm := (kernel_cont a).continuousAt (x:=a)
  have hs : Filter.Tendsto (fun v : ℝ => cartesianKernel 0 0 0 + cartesianKernel 0 0 0 -
      2*cartesianKernel 0 a v) (nhds a) (nhds 0) := by
    convert (tendsto_const_nhds.sub (tendsto_const_nhds.mul hm)) using 1
    rw [diag a, show cartesianKernel 0 0 0+cartesianKernel 0 0 0-2*cartesianKernel 0 0 0=0 by ring]
  have hsq (v : ℝ) : ‖sectionAt v-sectionAt a‖^2=cartesianKernel 0 0 0+
      cartesianKernel 0 0 0-2*cartesianKernel 0 a v := by
    rw [norm_sub_sq_real,←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,
      real_inner_comm (sectionAt a) (sectionAt v)]
    simp only [covariance,diag];ring
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,←hsq,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

private theorem feature_integrable : Integrable (fun u => sectionAt (2*π*u)) angularLaw := by
  have hc : Continuous (fun u : ℝ => sectionAt (2*π*u)) := section_cont.comp (continuous_const.mul continuous_id)
  exact ((hc.intervalIntegrable (μ:=volume) (0:ℝ) 1).1)

private def meanSection : H := ∫ u, sectionAt (2*π*u) ∂angularLaw

private theorem mean_section (u : ℝ) : ⟪sectionAt u,meanSection⟫_ℝ=c0 := by
  rw [meanSection,←integral_inner feature_integrable]
  simp_rw [covariance]
  rw [cartesian_integrated_row]
  simp [k0,c0]

theorem mean_representation : (∫ u, sectionAt (2*π*u) ∂angularLaw)=q := by
  have hq : ⟪q,meanSection⟫_ℝ=c0 := by
    rw [meanSection,←integral_inner feature_integrable]
    simp [q_section]
  have hself : ⟪meanSection,meanSection⟫_ℝ=c0 := by
    conv_lhs => rhs; rw [meanSection]
    rw [←integral_inner feature_integrable]
    simp_rw [fun t => real_inner_comm (sectionAt (2*π*t)) meanSection,mean_section]
    simp
  change meanSection=q
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have e := norm_sub_sq_real meanSection q
  rw [←real_inner_self_eq_norm_sq meanSection,hself,q_norm,real_inner_comm q meanSection,hq] at e
  nlinarith [norm_nonneg (meanSection-q)]

theorem population_statistic (h : H) :
    (∫ u, ⟪h,sectionAt (2*π*u)⟫_ℝ ∂angularLaw)=⟪h,q⟫_ℝ := by
  rw [integral_inner feature_integrable,mean_representation]

theorem teacher_certificate (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (h : H)
    (y : Fin (n+1)→ℝ) (value R : ℝ) (labels : ∀ i, ⟪h,gridSection i⟫_ℝ=y i)
    (cap : ‖h‖≤R) :
    |value-(∫ u, ⟪h,sectionAt (2*π*u)⟫_ℝ ∂angularLaw)|≤
    |value-covarianceWeight n*((∑ i,y i)/(n+1))|+R*√(minVariance n) := by
  have hh := CircleStats.teacher_certificate q h gridSection (designWeight n) y value R labels cap
  rwa [population_statistic,←power n hn ho,
    show covarianceWeight n*((∑ i,y i)/(n+1))=∑ i,designWeight n i*y i by
      simp only [designWeight,←mul_sum];ring]

theorem after_labels (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (h : H)
    (t y : Fin (n+1)→ℝ) (value R : ℝ) (labels : ∀ i, ⟪h,gridSection i⟫_ℝ=y i)
    (cap : ‖h‖≤R) (fit : ∀ i, ∑ j,t j*sampledMatrix 0 j i=y i) :
    |value-(∫ u, ⟪h,sectionAt (2*π*u)⟫_ℝ ∂angularLaw)|≤
    |value-∑ i,designWeight n i*y i|+√(R^2-∑ i,t i*y i)*√(minVariance n) := by
  rw [population_statistic,←power n hn ho]
  exact CircleStats.certificate_after_labels q h gridSection _ _ _ _ _ labels cap
    (normal_equations n hn ho) (by simpa only [grid_covariance] using fit)


/-- Both endpoints and the entire fitted-radius interval are realized by covariance
feature-space teachers with the same exact data. -/
theorem sharp_interval (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1))
    (t y : Fin (n+1)→ℝ) (R s : ℝ) (hR : 0≤R) (hs : |s|≤1)
    (fit : ∀ i, ∑ j,t j*sampledMatrix 0 j i=y i) (feasible : ∑ i,t i*y i≤R^2) :
    ∃ h : H, ‖h‖≤R ∧ (∀ i,⟪h,gridSection i⟫_ℝ=y i) ∧
    (∫ u, ⟪h,sectionAt (2*π*u)⟫_ℝ ∂angularLaw)=∑ i,designWeight n i*y i+
      s*√(R^2-∑ i,t i*y i)*√(minVariance n) := by
  obtain ⟨h,cap,labels,mean⟩ := CircleStats.certificate_attained q gridSection (designWeight n) t y
    R s hR hs (normal_equations n hn ho) (by simpa only [grid_covariance] using fit) feasible
  exact ⟨h,cap,labels,by rwa [population_statistic,←power n hn ho]⟩

private def linearSection : H := sectionAt 0-sectionAt π

private theorem linear_coeff : ∀ᵐ w ∂standardPair, linearSection w=w.1 := by
  filter_upwards [Lp.coeFn_sub (sectionAt 0) (sectionAt π),(phi_mem 2 0).coeFn_toLp,
    (phi_mem 2 π).coeFn_toLp] with w he h0 hπ
  change (sectionAt 0-sectionAt π) w=_
  rw [he]
  change sectionAt 0 w-sectionAt π w=_
  rw [show sectionAt 0 w=phi 0 w from h0,show sectionAt π w=phi π w from hπ]
  simp only [phi,projection,cos_zero,sin_zero,mul_one,mul_zero,add_zero,cos_pi,sin_pi,mul_neg]
  cases le_total 0 w.1 with
  | inl hw => rw [max_eq_left hw,max_eq_right (neg_nonpos.mpr hw)];ring
  | inr hw => rw [max_eq_right hw,max_eq_left (neg_nonneg.mpr hw)];ring

private theorem linear_section (u : ℝ) : ⟪linearSection,sectionAt u⟫_ℝ=cos u/2 := by
  let F (w : ℝ×ℝ) := w.1*phi u w
  have hf : Integrable F standardPair := mixed_integrable (coord_mem 2).1 (phi_mem 2 u)
  let flip (w : ℝ×ℝ) : ℝ×ℝ := (-w.1,-w.2)
  have hneg : MeasurePreserving (fun x : ℝ => -x) G G :=
    ⟨by fun_prop,by simp [G, ProbabilityTheory.gaussianReal_map_neg]⟩
  have hflip : MeasurePreserving flip standardPair standardPair := hneg.prod hneg
  have he : (∫ w,F (flip w) ∂standardPair)=∫ w,F w ∂standardPair :=
    (integral_map hflip.measurable.aemeasurable (hflip.map_eq.symm ▸ hf.aestronglyMeasurable)).symm.trans
      (by rw [hflip.map_eq])
  have hs (w : ℝ×ℝ) : F w+F (flip w)=w.1*projection u w := by
    have h : projection u (flip w) = -projection u w := by simp [projection,flip];ring
    simp only [F,phi,h,flip]
    rw [neg_mul,←sub_eq_add_neg,←mul_sub]
    congr 1
    rcases le_total 0 (projection u w) with hp|hp
    · rw [max_eq_left hp,max_eq_right (neg_nonpos.mpr hp),sub_zero]
    · rw [max_eq_right hp,max_eq_left (neg_nonneg.mpr hp),zero_sub,neg_neg]
  have hF : (∫ w,F w ∂standardPair)+(∫ w,F (flip w) ∂standardPair)=cos u := by
    have hf2 : Integrable (fun w => F (flip w)) standardPair := (hflip.integrable_comp hf.aestronglyMeasurable).2 hf
    rw [←integral_add hf hf2]
    simp_rw [hs,show ∀ w : ℝ×ℝ,w.1*projection u w=w.1^2*cos u+(w.1*w.2)*sin u by
      intro w; unfold projection; ring]
    have sqi : Integrable (fun w : ℝ×ℝ => w.1^2) standardPair := (coord_mem 2).1.integrable_sq
    have prod := mixed_integrable (coord_mem 2).1 (coord_mem 2).2
    rw [integral_add (sqi.mul_const _) (prod.mul_const _),integral_mul_const,integral_mul_const]
    have cross : (∫ w : ℝ×ℝ,w.1*w.2 ∂standardPair)=0 := by
      rw [standardPair,integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y),
        ProbabilityTheory.integral_id_gaussianReal,zero_mul]
    have fst : (∫ w : ℝ×ℝ,w.1^2 ∂standardPair)=1 := by
      rw [standardPair,integral_fun_fst (fun x : ℝ => x^2)]
      simp [gaussian_second]
    rw [fst,cross]
    ring
  rw [MeasureTheory.L2.inner_def]
  have hf' : (∫ w,inner ℝ (linearSection w) (sectionAt u w) ∂standardPair)=∫ w,F w ∂standardPair := by
    apply integral_congr_ae
    filter_upwards [linear_coeff,(phi_mem 2 u).coeFn_toLp] with w hw hu
    change sectionAt u w*linearSection w=_
    rw [hw,show sectionAt u w=phi u w from hu,mul_comm]
  rw [hf']
  rw [he] at hF
  linarith

def teacherVector : H := c0⁻¹ • q + (2:ℝ) • linearSection

theorem teacher_evaluation (u : ℝ) : ⟪teacherVector,sectionAt u⟫_ℝ=1+cos u := by
  simp only [teacherVector,inner_add_left,real_inner_smul_left,q_section,linear_section]
  field_simp [show c0≠0 by unfold c0;positivity]

theorem teacher_mean : (∫ u, ⟪teacherVector,sectionAt (2*π*u)⟫_ℝ ∂angularLaw)=1 := by
  rw [population_statistic,teacherVector,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,q_norm,linearSection,inner_sub_left,
    real_inner_comm q (sectionAt 0),real_inner_comm q (sectionAt π),q_section,q_section]
  simp [show c0≠0 by unfold c0; positivity]

theorem teacher_norm : ‖teacherVector‖^2=π^2/2+4 := by
  have hcross : ⟪q,linearSection⟫_ℝ=0 := by simp only [linearSection,inner_sub_right,q_section,sub_self]
  have hlin : ⟪linearSection,linearSection⟫_ℝ=1 := by
    conv_lhs => rhs; rw [linearSection]
    rw [inner_sub_right,linear_section,linear_section,cos_pi,cos_zero];ring
  rw [←real_inner_self_eq_norm_sq]
  simp only [teacherVector,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    hcross,hlin,show ⟪linearSection,q⟫_ℝ=0 by rw [real_inner_comm,hcross],
    show ⟪q,q⟫_ℝ=c0 by rw [real_inner_self_eq_norm_sq,q_norm],c0]
  field_simp [Real.pi_ne_zero];ring

/-- Every representing feature vector of this teacher spends at least the computed radius. -/
theorem teacher_minimal (h : H) (rep : ∀ u, ⟪h,sectionAt u⟫_ℝ=1+cos u) :
    π^2/2+4≤‖h‖^2 := by
  have he (u) : ⟪h-teacherVector,sectionAt u⟫_ℝ=0 := by
    rw [inner_sub_left,rep,teacher_evaluation,sub_self]
  have hq : ⟪h-teacherVector,q⟫_ℝ=0 := by rw [←population_statistic];simp [he]
  have hl : ⟪h-teacherVector,linearSection⟫_ℝ=0 := by simp only [linearSection,inner_sub_right,he,sub_self]
  have ht : ⟪h-teacherVector,teacherVector⟫_ℝ=0 := by
    change ⟪h-teacherVector,c0⁻¹ • q + (2:ℝ) • linearSection⟫_ℝ=0
    simp only [inner_add_right,real_inner_smul_right,hq,hl,mul_zero,add_zero]
  have hh := norm_add_sq_real (h-teacherVector) teacherVector
  rw [sub_add_cancel,ht,teacher_norm] at hh
  nlinarith [sq_nonneg ‖h-teacherVector‖]

local instance : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩

abbrev Angle := AddCircle (π- -π)

/-- The prescribed teacher written as a circle function. -/
def teacher : Angle→ℂ :=
  (fourier 0 : Angle→ℂ) + (1/2:ℂ) • (fourier 1 : Angle→ℂ) +
    (1/2:ℂ) • (fourier (-1) : Angle→ℂ)

theorem teacher_angle (u : ℝ) : teacher (u:Angle)=(1+cos u:ℝ) := by
  simp only [teacher,Pi.add_apply,Pi.smul_apply,smul_eq_mul,fourier_zero,fourier_neg]
  rw [fourier_coe_apply]
  push_cast
  have hπ : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [show 2*(π:ℂ)*Complex.I*1*(u:ℂ)/((π:ℂ)- -(π:ℂ))=(u:ℂ)*Complex.I by field_simp;ring,
    Complex.exp_mul_I]
  simp [←Complex.cos_conj,←Complex.sin_conj]
  ring

theorem teacher_fourier (k : ℤ) :
    fourierCoeff teacher k = (if k=0 then 1 else if k=1 ∨ k=(-1) then 1/2 else 0) := by
  have hi (l : ℤ) : Integrable (fourier l : Angle→ℂ) AddCircle.haarAddCircle :=
    (fourier l).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [teacher,fourierCoeff.add ((hi 0).add ((hi 1).smul (1/2:ℂ))) ((hi (-1)).smul (1/2:ℂ))]
  rw [fourierCoeff.add (hi 0) ((hi 1).smul (1/2:ℂ))]
  simp only [Pi.add_apply,fourierCoeff.const_smul,fourierCoeff_fourier,Pi.single_apply,smul_eq_mul]
  by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases hn : k=(-1) <;> simp_all

private theorem c_zero : tangentCoeff 0 0=c0 := by norm_num [tangentCoeff,ntkEven,c0]
private theorem c_one : tangentCoeff 0 1=1/8 := by norm_num [tangentCoeff]
private theorem c_neg : tangentCoeff 0 (-1)=1/8 := by norm_num [tangentCoeff]

theorem teacher_zero_modes (k : ℤ) (hk : tangentCoeff 0 k=0) : fourierCoeff teacher k=0 := by
  rw [teacher_fourier]
  split_ifs with h h
  · subst k; have h0 : 0<c0 := by unfold c0;positivity
    rw [c_zero] at hk; exact (h0.ne' hk).elim
  · rcases h with rfl|rfl <;> norm_num [c_one,c_neg] at hk
  · rfl

/-- The sparse weighted Fourier sum equals the actual minimum feature-space norm. -/
theorem fourier_norm :
    (∑' k : ℤ, ‖fourierCoeff teacher k‖^2 / tangentCoeff 0 k)=‖teacherVector‖^2 := by
  rw [teacher_norm,tsum_eq_sum (s:=({0,1,-1}:Finset ℤ))]
  · simp only [sum_insert (by decide : (0:ℤ)∉({1,-1}:Finset ℤ)),
      sum_insert (by decide : (1:ℤ)∉({-1}:Finset ℤ)),sum_singleton,teacher_fourier,
      c_zero,c_one,c_neg]
    norm_num [c0]
  · intro k hk
    simp only [mem_insert,mem_singleton,not_or] at hk
    rw [teacher_fourier,ite_eq_right hk.1,ite_eq_right (not_or.mpr hk.2)]
    simp

end CircleTeacherRKHS
