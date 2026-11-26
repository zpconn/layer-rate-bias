module

public import CircleMajorityFold
public import CircleMeanDynamics
import all CircleMajorityFold
import all CircleMajorityCF
import all CircleAngularGeometry
import all CircleMeanDynamics
import all CircleFlowPath
import all CircleSharpTracking
import all CircleTangentDrift
import all CircleEscape
import Mathlib.Tactic

/-! Sharp angular cancellation for the signed one-neuron tangent row. -/
@[expose] public section
noncomputable section
namespace CircleSignedAngular
open Real MeasureTheory Set Filter CircleEscape CircleAngularGeometry CircleMajorityFold
open scoped Topology InnerProductSpace

def x (u : ℝ) := point (2*π*u)
abbrev Q := CircleTangentDrift.angularLaw
def avg (N : ℕ) (f : ℂ→ℝ) := (∑ i, f (gridPoint N i))/N
def gridGate (N : ℕ) (w : ℂ) := (1/(N:ℝ)) • ∑ i, gate w (gridPoint N i) • gridPoint N i
def popGate (w : ℂ) := ∫ u, gate w (x u) • x u ∂Q
def signedGate (N : ℕ) (b : ℝ) (w : ℂ) := popGate w-b • gridGate N w
def signedFeature (N : ℕ) (b : ℝ) (w : ℂ) := ‖w‖/π-b*avg N (feature w)
def G (N : ℕ) (b : ℝ) := sqrt ((1/π-b*amplitude N)^2+2*b*amplitude N*(1-cos (halfCell N))/π)
def B (N : ℕ) (b : ℝ) := max |1/π-b*amplitude N| |1/π-b*amplitude N*cos (halfCell N)|

theorem x_norm (u : ℝ) : ‖x u‖=1 := by
  rw [Complex.norm_def,Complex.normSq_apply]
  simp only [x,point,←sq,cos_sq_add_sin_sq,sqrt_one]

theorem x_continuous : Continuous x := by
  have eq : x = fun u : ℝ => ((Real.cos (2*π*u):ℝ):ℂ)+Complex.I*((Real.sin (2*π*u):ℝ):ℂ) := by funext u;apply Complex.ext <;> simp only [x,point,Complex.add_re,Complex.add_im,Complex.I_mul_re,Complex.I_mul_im,Complex.ofReal_re,Complex.ofReal_im,neg_zero,add_zero,zero_add]
  rw [eq];fun_prop

theorem gate_field_integrable (w : ℂ) : Integrable (fun u => gate w (x u) • x u) Q := by
  have xc := x_continuous
  have gm : Measurable (fun u => gate w (x u)) := Measurable.ite
    (measurableSet_lt measurable_const (continuous_const.inner xc).measurable) measurable_const measurable_const
  apply (integrable_const (1:ℝ)).mono' (gm.smul xc.measurable).aestronglyMeasurable
  filter_upwards with u
  change ‖gate w (x u) • x u‖≤1
  rw [norm_smul,x_norm,mul_one,Real.norm_eq_abs]
  unfold gate; split <;> norm_num

theorem pop_feature (w : ℂ) : (∫ u, feature w (x u) ∂Q)=‖w‖/π := by
  let f := fun t : ℝ => feature w (point t)
  change (∫ u in Ioc (0:ℝ) 1, f (2*π*u))=_
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_comp_mul_left f (by positivity : 2*π≠0)]
  simp only [mul_zero,mul_one,smul_eq_mul]
  dsimp only [f]
  simp_rw [feature_eq]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right]
  have h := integral_half (0-w.arg)
  have eq : 2*π-w.arg=0-w.arg+2*π := by ring
  rw [eq,h];ring

theorem inner_pop (w v : ℂ) : inner ℝ v (popGate w)=∫ u, gate w (x u)*inner ℝ v (x u) ∂Q := by
  rw [popGate,←integral_inner (𝕜:=ℝ) (gate_field_integrable w)]
  simp only [real_inner_smul_right]

theorem inner_grid (N : ℕ) (w v : ℂ) : inner ℝ v (gridGate N w)=avg N (fun u => gate w u*inner ℝ v u) := by
  simp only [gridGate,avg,real_inner_smul_right,inner_sum,div_eq_inv_mul,mul_one]

private theorem gated_le (w v u : ℂ) : gate w u*inner ℝ v u≤feature v u := by
  unfold gate feature;split <;> simp
private theorem gated_self (w u : ℂ) : gate w u*inner ℝ w u=feature w u := by
  unfold gate feature;split_ifs with h
  · rw [one_mul,max_eq_left h.le]
  · rw [zero_mul,max_eq_right (not_lt.mp h)]

private theorem linear_pop (w v : ℂ) : inner ℝ v (popGate w)≤‖v‖/π := by
  rw [inner_pop,←pop_feature]
  have hi := (gate_field_integrable w).const_inner v (𝕜:=ℝ)
  apply integral_mono (by simpa only [real_inner_smul_right] using hi) _ (fun u => gated_le _ _ _)
  change IntegrableOn _ (Ioc 0 1) volume
  have c : Continuous (fun u => feature v (x u)) := (continuous_const.inner x_continuous).max continuous_const
  exact c.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem self_pop (w : ℂ) : inner ℝ w (popGate w)=‖w‖/π := by
  rw [inner_pop,←pop_feature]; simp only [gated_self]

private theorem linear_grid (N : ℕ) (w v : ℂ) : inner ℝ v (gridGate N w)≤avg N (feature v) := by
  rw [inner_grid,avg,avg]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => gated_le _ _ _) (Nat.cast_nonneg _)

private theorem self_grid (N : ℕ) (w : ℂ) : inner ℝ w (gridGate N w)=avg N (feature w) := by
  rw [inner_grid,avg,avg]; simp only [gated_self]

private theorem half_range {N : ℕ} (hn : 3≤N) : 0<halfCell N ∧ halfCell N≤π/2 := by
  have hN : 3≤(N:ℝ) := by exact_mod_cast hn
  unfold halfCell
  refine ⟨by positivity,(div_le_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_left hN pi_pos.le,pi_pos]

theorem amplitude_pos {N : ℕ} (hn : 3≤N) : 0<amplitude N := by
  have ⟨d,hl⟩ := half_range hn
  have h := sin_pos_of_pos_of_lt_pi d (by linarith [pi_pos])
  have np : 0<(N:ℝ) := by positivity
  unfold amplitude;positivity

private theorem folded_bounds {N : ℕ} (hn : 3≤N) (ho : Odd N) (θ : ℝ) :
    amplitude N*cos (halfCell N)≤CircleMajorityCF.angular N θ ∧ CircleMajorityCF.angular N θ≤amplitude N := by
  let q := halfCell N
  have ⟨qp,ql⟩ := half_range hn
  have p : 0<2*q := by dsimp [q];positivity
  let d := toIcoMod p (-q) θ
  have mem := toIcoMod_mem_Ico p (-q) θ
  change -q≤d ∧ d< -q+2*q at mem
  have dom : d∈Icc (-q) q := ⟨mem.1,by linarith [mem.2]⟩
  have equiv : CircleMajorityCF.angular N θ=CircleMajorityCF.angular N d := by
    have per := (angular_periodic hn ho).zsmul (toIcoDiv p (-q) θ) d
    rwa [toIcoMod_add_toIcoDiv_zsmul] at per
  rw [equiv,angular_on_cell hn ho dom]
  have c : cos q≤cos d := by
    rw [←cos_abs d]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by dsimp [q];linarith [pi_pos]) (abs_le.mpr dom)
  exact ⟨mul_le_mul_of_nonneg_left c (amplitude_pos hn).le,mul_le_of_le_one_right (amplitude_pos hn).le (cos_le_one _)⟩

private theorem avg_polar (N : ℕ) (w : ℂ) : avg N (feature w)=‖w‖*CircleMajorityCF.angular N w.arg := by
  change (∑ i : Fin N, feature w (point (CircleGridSpectrum.physicalAngle i)))/N=_
  simp only [CircleMajorityCF.angular,feature_eq,halfWave,←Finset.mul_sum,mul_div_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro i _;rw [←cos_neg (w.arg-_),neg_sub]

theorem grid_norm_bound {N : ℕ} (hn : 3≤N) (ho : Odd N) (w : ℂ) : ‖gridGate N w‖≤amplitude N := by
  let v := gridGate N w
  have H := (linear_grid N w v).trans ((avg_polar N v) ▸ mul_le_mul_of_nonneg_left (folded_bounds hn ho v.arg).2 (norm_nonneg _))
  change inner ℝ v v≤‖v‖*amplitude N at H
  rw [real_inner_self_eq_norm_sq,pow_two] at H
  by_cases h : v=0
  · change ‖v‖≤_;rw [h,norm_zero];exact (amplitude_pos hn).le
  · exact le_of_mul_le_mul_left H (norm_pos_iff.mpr h)

private theorem pop_formula {w : ℂ} (hw : w≠0) : popGate w=(1/(π*‖w‖)) • w := by
  let v := popGate w
  have wp := norm_pos_iff.mpr hw
  have Bv : ‖v‖≤1/π := by
    have h := linear_pop w v
    change inner ℝ v v≤_ at h
    rw [real_inner_self_eq_norm_sq,pow_two,div_eq_mul_inv] at h
    by_cases h0 : v=0
    · rw [h0,norm_zero];positivity
    · simpa using le_of_mul_le_mul_left h (norm_pos_iff.mpr h0)
  have z := self_pop w
  have vp : ‖v‖^2≤(1/π)^2 := pow_le_pow_left₀ (norm_nonneg v) Bv 2
  apply sub_eq_zero.mp; apply norm_eq_zero.mp; apply (sq_eq_zero_iff).mp
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm w (popGate w),z,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0<1/(π*‖w‖))]
  change ‖v‖^2-2*(1/(π*‖w‖)*(‖w‖/π))+(1/(π*‖w‖)*‖w‖)^2=0
  have h0 : 0≤‖v-(1/(π*‖w‖)) • w‖^2 := sq_nonneg _
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm w v,show inner ℝ w v=‖w‖/π from z,
    norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<1/(π*‖w‖))] at h0
  have a : 1/(π*‖w‖)*(‖w‖/π)=(1/π)^2 := by field_simp
  have b : 1/(π*‖w‖)*‖w‖=1/π := by field_simp
  rw [a,b] at h0 ⊢; linarith

theorem gate_bound {N : ℕ} (hn : 3≤N) (ho : Odd N) {b : ℝ} (hb : 0≤b) (w : ℂ) :
    ‖signedGate N b w‖≤G N b := by
  by_cases hw : w=0
  · subst w;simp [signedGate,popGate,gridGate,gate,G]
  rw [signedGate,pop_formula hw,G]
  apply le_sqrt_of_sq_le
  have wp := norm_pos_iff.mpr hw
  rw [norm_sub_sq_real,real_inner_smul_left,real_inner_smul_right,self_grid,avg_polar,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity : 0<1/(π*‖w‖)),abs_of_nonneg hb]
  have lo := (folded_bounds hn ho w.arg).1
  have up := pow_le_pow_left₀ (norm_nonneg _) (grid_norm_bound hn ho w) 2
  have e : 1/(π*‖w‖)*‖w‖=1/π := by field_simp
  have h : 1/(π*‖w‖)*(b*(‖w‖*CircleMajorityCF.angular N w.arg))=b/π*CircleMajorityCF.angular N w.arg := by field_simp
  rw [e,h]
  have h₁ := mul_le_mul_of_nonneg_left lo (div_nonneg hb pi_pos.le)
  have h₂ := mul_le_mul_of_nonneg_left up (sq_nonneg b)
  simp only [div_eq_mul_inv] at h₁ ⊢
  nlinarith only [h₁,h₂]

theorem feature_bound {N : ℕ} (hn : 3≤N) (ho : Odd N) {b : ℝ} (hb : 0≤b) (w : ℂ) :
    |signedFeature N b w|≤B N b*‖w‖ := by
  have ⟨lo,hi⟩ := folded_bounds hn ho w.arg
  have eq : signedFeature N b w=(1/π-b*CircleMajorityCF.angular N w.arg)*‖w‖ := by rw [signedFeature,avg_polar];ring
  rw [eq,abs_mul,abs_of_nonneg (norm_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply abs_le.mpr
  constructor
  · apply ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le (1/π-b*amplitude N))).trans
    linarith only [mul_le_mul_of_nonneg_left hi hb]
  · apply le_trans _ ((le_abs_self _).trans (le_max_right _ _))
    linarith only [mul_le_mul_of_nonneg_left lo hb]

private theorem support_derivative {F : ℂ→ℝ} {a : ℂ} {z : ℝ→ℂ} {t : ℝ} {v : ℂ}
    (h : HasDerivAt z v t) (reg : DifferentiableAt ℝ (fun s => F (z s)) t)
    (eq : inner ℝ (z t) a = F (z t)) (support : ∀ y,inner ℝ y a≤F y) :
    HasDerivAt (fun s => F (z s)) (inner ℝ v a) t := by
  have d : HasDerivAt (fun s => inner ℝ (z s) a) (inner ℝ v a) t := by
    simpa only [inner_zero_right,zero_add] using h.inner ℝ (hasDerivAt_const t a)
  have hm : IsLocalMin (fun s => F (z s)-inner ℝ (z s) a) t := by
    apply Eventually.of_forall; intro s;dsimp only;rw [eq,sub_self]
    exact sub_nonneg.mpr (support _)
  exact reg.hasDerivAt.congr_deriv (sub_eq_zero.mp (hm.hasDerivAt_eq_zero (reg.hasDerivAt.sub d)))

/-- A line segment may contain gate ties, or pass through zero. The two convex
parts have their integral and discrete supporting rows as derivatives almost
everywhere on the segment, including segments wholly contained in a gate plane. -/
theorem feature_lipschitz {N : ℕ} (hn : 3≤N) (ho : Odd N) {b : ℝ} (hb : 0≤b) (v w : ℂ) :
    |signedFeature N b v-signedFeature N b w|≤G N b*‖v-w‖ := by
  let δ := v-w
  let z (s : ℝ) := w+s • δ
  let f (s : ℝ) := ‖z s‖/π
  let g (s : ℝ) := avg N (feature (z s))
  have hz (t : ℝ) : HasDerivAt z δ t := by
    simpa [z] using ((hasDerivAt_id t).smul_const δ).const_add w
  have zac : AbsolutelyContinuousOnInterval z 0 1 :=
    (show ContDiff ℝ 1 z by unfold z;fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have fac : AbsolutelyContinuousOnInterval f 0 1 := by
    simp only [f,div_eq_inv_mul]
    exact (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval zac).const_mul _
  have gac : AbsolutelyContinuousOnInterval g 0 1 := by
    simp only [g,avg,div_eq_inv_mul]
    apply AbsolutelyContinuousOnInterval.const_mul
    apply CircleFlowPath.acsum
    intro i _
    apply (LipschitzWith.id.max_const (0:ℝ)).comp_absolutelyContinuousOnInterval
    exact (show ContDiff ℝ 1 (fun t => inner ℝ (z t) (gridPoint N i)) by simp only [z,inner_add_left,real_inner_smul_left];fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have yd := fac.fun_sub (gac.const_mul b)
  have bound : ∀ᵐ t : ℝ, t∈Ioc 0 1 →
      |deriv (fun u => f u-b*g u) t|≤G N b*‖δ‖ := by
    filter_upwards [fac.ae_differentiableAt,gac.ae_differentiableAt] with t hf hg h
    have u := mem_uIcc_of_le h.1.le h.2
    have df := support_derivative (hz t) (hf u) (self_pop (z t)) (linear_pop (z t))
    have dg := support_derivative (hz t) (hg u) (self_grid N (z t)) (linear_grid N (z t))
    have dy := df.sub (dg.const_mul b)
    change HasDerivAt (fun u => f u-b*g u) _ t at dy
    rw [dy.deriv,← real_inner_smul_right,←inner_sub_right]
    change |inner ℝ δ (signedGate N b (z t))|≤_
    exact (abs_real_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left (gate_bound hn ho hb _) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have result := CircleSharpTracking.endpoint_variation (C:=G N b) (q:=fun _ => ‖δ‖)
    zero_le_one yd intervalIntegrable_const bound
  simpa [f,g,z,δ,signedFeature,sub_add_cancel] using result

end CircleSignedAngular
