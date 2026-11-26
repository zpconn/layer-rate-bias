module

public import SmoothGramLimit
public import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Tactic

/-! One training example at fixed fan-in. The Gaussian initialization supplies the
single-neuron moments, empirical tangent kernel, residual, and nonzero movement law. -/
@[expose] public section
noncomputable section
namespace PhysicalTangentLaw
open TwoLayerNetwork TwoLayerBudget SmoothSeedLaw MeasureTheory ProbabilityTheory Filter Real Set
open scoped InnerProduct Topology NNReal
variable {d n : ℕ}

/-- The upper subgradient is selected at a zero preactivation. -/
def slope (α u : ℝ) := if 0≤u then 1 else α

theorem slope_ok {α : ℝ} (ha : α≤1) (u : ℝ) : Slope α u (slope α u) := by
  unfold slope Slope; split_ifs <;> grind

def feature (α b : ℝ) (x w : Space d) := leaky α (b*inner ℝ w x)
def derivFeature (α b : ℝ) (x w : Space d) := slope α (b*inner ℝ w x)
def signalAtom (α b : ℝ) (x : Space d) (t : Neuron d) := t.1 * feature α b x t.2
def featureSq (α b : ℝ) (x : Space d) (t : Neuron d) := (feature α b x t.2)^2
def gateSq (α b : ℝ) (x : Space d) (t : Neuron d) := t.1^2*(derivFeature α b x t.2)^2

def featureVariance (α b : ℝ) (x : Space d) := ∫ w, (feature α b x w)^2 ∂stdGaussian (Space d)
def gateMoment (α b : ℝ) (x : Space d) := ∫ w, (derivFeature α b x w)^2 ∂stdGaussian (Space d)
def kernelLimit (α b : ℝ) (x : Space d) := featureVariance α b x+b^2*gateMoment α b x

def average (f : Neuron d → ℝ) (n : ℕ) (ω : Draws d) := (∑ i ∈ Finset.range n,f (ω i))/(n:ℝ)
def initial (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) :=
  (∑ i ∈ Finset.range n,signalAtom α b x (ω i))/sqrt n
def kernel (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) :=
  average (featureSq α b x) n ω+b^2*average (gateSq α b x) n ω

def factor (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) :=
  sqrt ((b^2/(d:ℝ))*average (gateSq α b x) n ω)/kernel α b x n ω
def limitFactor (α b : ℝ) (x : Space d) := sqrt ((b^2/(d:ℝ))*gateMoment α b x)/kernelLimit α b x

def tangentNorm (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) := |initial α b x n ω| *factor α b x n ω

private theorem projLaw (x : Space d) (hx : ‖x‖=1) :
    HasLaw (fun w : Space d => inner ℝ w x) (gaussianReal 0 1) (stdGaussian (Space d)) := by
  rw [show (fun w : Space d => inner ℝ w x)=innerSL ℝ x from funext (fun w => real_inner_comm _ _)]
  refine ⟨by fun_prop,?_⟩
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,hx]; simp

private theorem feature_meas (α b : ℝ) (x : Space d) : Measurable (feature α b x) := by
  unfold feature leaky; exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
private theorem gate_meas (α b : ℝ) (x : Space d) : Measurable (derivFeature α b x) := by
  unfold derivFeature slope; exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

private theorem feature_mem {α : ℝ} (ha : 0≤α) (h1 : α≤1) (b : ℝ) (x : Space d) (hx : ‖x‖=1) :
    MemLp (feature α b x) 2 (stdGaussian (Space d)) := by
  have p := ((projLaw x hx).memLp_comp (memLp_id_gaussianReal 2)).const_mul b
  apply p.norm.mono' (feature_meas α b x).aestronglyMeasurable
  apply ae_of_all; intro w
  change |leaky α (b*inner ℝ w x)|≤|b*inner ℝ w x|
  simpa [leaky] using leaky_lipschitz α (b*inner ℝ w x) 0 ha h1

private theorem gate_mem {α : ℝ} (ha : 0≤α) (h1 : α≤1) (b : ℝ) (x : Space d) :
    MemLp (derivFeature α b x) 2 (stdGaussian (Space d)) := by
  apply (memLp_const (1:ℝ)).mono' (gate_meas α b x).aestronglyMeasurable
  apply ae_of_all; intro w
  unfold derivFeature slope; split_ifs <;> simp [Real.norm_eq_abs,abs_of_nonneg ha,h1]

private theorem integrals {α : ℝ} (ha : 0≤α) (h1 : α≤1) (b : ℝ) (x : Space d) (hx : ‖x‖=1) :
    Integrable (featureSq α b x) (neuronLaw d) ∧ Integrable (gateSq α b x) (neuronLaw d) ∧
    (∫ t, featureSq α b x t ∂neuronLaw d)=featureVariance α b x ∧
    (∫ t, gateSq α b x t ∂neuronLaw d)=gateMoment α b x := by
  have a := (feature_mem ha h1 b x hx).integrable_sq
  have g := (gate_mem ha h1 b x).integrable_sq
  refine ⟨a.comp_snd _,normal_squared.1.mul_prod g,?_,?_⟩
  · unfold featureSq neuronLaw featureVariance
    rw [integral_fun_snd (fun w => (feature α b x w)^2),probReal_univ,one_smul]
  · unfold gateSq neuronLaw gateMoment
    rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => (derivFeature α b x w)^2),normal_squared.2,one_mul]

theorem positive_moments {α b : ℝ} (ha : 0<α) (h1 : α≤1) (bp : 0<b) (x : Space d) (hx : ‖x‖=1) :
    0<featureVariance α b x ∧ 0<gateMoment α b x := by
  have proj := projLaw x hx
  have p := proj.integrable_comp normal_squared.1
  have ex : (∫ w : Space d, (inner ℝ w x)^2 ∂stdGaussian (Space d))=1 :=
    (proj.integral_comp normal_squared.1.aestronglyMeasurable).trans normal_squared.2
  have sf := (feature_mem ha.le h1 b x hx).integrable_sq
  have sg := (gate_mem ha.le h1 b x).integrable_sq
  have alpha2 : α^2≤1 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h1)]
  constructor
  · have lb : α^2*b^2≤featureVariance α b x := by
      calc _ = ∫ w : Space d, (α^2*b^2)*(inner ℝ w x)^2 ∂stdGaussian (Space d) := by rw [integral_const_mul,ex,mul_one]
           _ ≤ _ := by
              apply integral_mono (p.const_mul _) sf; intro w
              dsimp only [feature,leaky,Function.comp_apply]; split_ifs
              · rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right alpha2 (sq_nonneg (b*inner ℝ w x))]
              · ring_nf; rfl
    exact lt_of_lt_of_le (by positivity) lb
  · have lb : α^2≤gateMoment α b x := by
      calc _ = ∫ _w : Space d, α^2 ∂stdGaussian (Space d) := by simp
           _ ≤ _ := by
              apply integral_mono (integrable_const _) sg; intro w
              dsimp only [derivFeature,slope]; split_ifs <;> simp [alpha2]
    exact lt_of_lt_of_le (sq_pos_of_pos ha) lb

private theorem average_lln (f : Neuron d → ℝ) (mf : Measurable f) (i : Integrable f (neuronLaw d)) :
    ∀ᵐ ω ∂law d, Tendsto (fun n => average f n ω) atTop (𝓝 (∫ t, f t ∂neuronLaw d)) := by
  simpa only [average,smul_eq_mul,div_eq_inv_mul] using observable_lln f mf i

private theorem average_meas (f : Neuron d → ℝ) (mf : Measurable f) (n : ℕ) : Measurable (average f n) := by
  unfold average; fun_prop

theorem kernel_lln {α : ℝ} (ha : 0≤α) (h1 : α≤1) (b : ℝ) (x : Space d) (hx : ‖x‖=1) :
    ∀ᵐ ω ∂law d, Tendsto (fun n => kernel α b x n ω) atTop (𝓝 (kernelLimit α b x)) ∧
      Tendsto (fun n => average (gateSq α b x) n ω) atTop (𝓝 (gateMoment α b x)) := by
  obtain ⟨hi,gi,hs,gs⟩ := integrals ha h1 b x hx
  have hf := average_lln _ (by unfold featureSq; have := feature_meas α b x; fun_prop) hi
  have hg := average_lln _ (by unfold gateSq; have := gate_meas α b x; fun_prop) gi
  rw [hs] at hf; rw [gs] at hg
  filter_upwards [hf,hg] with ω h g
  exact ⟨h.add (g.const_mul _),g⟩

/-- The reference residual has a nondegenerate Gaussian limit at the actual finite-width normalization. -/
theorem residual_clt {α : ℝ} (ha : 0≤α) (h1 : α≤1) (b : ℝ) (x : Space d) (hx : ‖x‖=1) :
    TendstoInDistribution (initial α b x) atTop id (fun _ => law d) (gaussianReal 0 (featureVariance α b x).toNNReal) := by
  let f := signalAtom α b x
  have fm : Measurable f := by unfold f signalAtom; have := feature_meas α b x; fun_prop
  have fi : MemLp f 2 (neuronLaw d) := by
    apply (memLp_two_iff_integrable_sq fm.aestronglyMeasurable).mpr
    have prod := normal_squared.1.mul_prod ((feature_mem ha h1 b x hx).integrable_sq)
    simpa only [f,signalAtom,mul_pow,neuronLaw] using prod
  let X := fun (i : ℕ) (ω : Draws d) => f (ω i)
  have one := eval_law (d:=d) 0
  have mean : (∫ ω, X 0 ω ∂law d)=0 := by
    change (∫ ω, (f ∘ (fun ω : Draws d => ω 0)) ω ∂law d)=0
    rw [one.integral_comp fi.aestronglyMeasurable]
    unfold f signalAtom neuronLaw
    rw [integral_prod_mul (fun a : ℝ => a) (feature α b x),integral_id_gaussianReal,zero_mul]
  have var : variance (X 0) (law d) = featureVariance α b x := by
    have mx : MemLp (X 0) 2 (law d) := one.memLp_comp fi
    rw [variance_eq_sub mx,mean,zero_pow (by decide : 2≠0),sub_zero]
    change (∫ ω : Draws d, (f (ω 0))^2 ∂law d)=_
    have ie : (∫ ω : Draws d, (f (ω 0))^2 ∂law d) = ∫ t, (f t)^2 ∂neuronLaw d := one.integral_comp (fi.aestronglyMeasurable.pow 2)
    rw [ie]
    simp only [f,signalAtom,mul_pow,neuronLaw,featureVariance]
    rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => (feature α b x w)^2),normal_squared.2,one_mul]
  have iid := iid_observable _ fm
  have hy : HasLaw id (gaussianReal 0 (variance (X 0) (law d)).toNNReal)
      (gaussianReal 0 (featureVariance α b x).toNNReal) := by rw [var]; exact HasLaw.id
  have clt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X:=X) hy (one.memLp_comp fi) iid.1 iid.2
  apply clt.congr _ (ae_of_all _ (fun _ => rfl))
  intro n; apply ae_of_all; intro ω; simp only [mean,mul_zero,sub_zero,initial,X,f,div_eq_inv_mul]

theorem factor_pos {α b : ℝ} (hd : 0<d) (ha : 0<α) (h1 : α≤1) (bp : 0<b) (x : Space d) (hx : ‖x‖=1) :
    0<limitFactor α b x := by
  obtain ⟨p,q⟩ := positive_moments ha h1 bp x hx
  unfold limitFactor kernelLimit; positivity

/-- The physical first-layer tangent movement tends to a positive multiple of the absolute
value of a nondegenerate centered Gaussian. The multiplier uses the true initial kernel. -/
theorem tangent_limit {α b : ℝ} (ha : 0<α) (h1 : α≤1) (bp : 0<b) (x : Space d) (hx : ‖x‖=1) :
    TendstoInDistribution (tangentNorm α b x) atTop (fun z : ℝ => |z| *limitFactor α b x)
      (fun _ => law d) (gaussianReal 0 (featureVariance α b x).toNNReal) := by
  have hf := feature_meas α b x
  have hg := gate_meas α b x
  have hfm (n : ℕ) : Measurable (factor α b x n) := by
    have f := average_meas (featureSq α b x) (by unfold featureSq;fun_prop) n
    have g := average_meas (gateSq α b x) (by unfold gateSq;fun_prop) n
    unfold factor kernel; fun_prop
  have pp := positive_moments ha h1 bp x hx
  have kp : 0<kernelLimit α b x := by unfold kernelLimit; exact add_pos pp.1 (mul_pos (sq_pos_of_pos bp) pp.2)
  have lim : TendstoInMeasure (law d) (factor α b x) atTop (fun _ => limitFactor α b x) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hfm n).aestronglyMeasurable)
    filter_upwards [kernel_lln ha.le h1 b x hx] with ω h
    exact ((h.2.const_mul _).sqrt).div h.1 kp.ne'
  exact (residual_clt ha.le h1 b x hx).continuous_comp_prodMk_of_tendstoInMeasure_const
    (g:=fun p : ℝ×ℝ => |p.1| *p.2) (by fun_prop) lim (fun n => (hfm n).aemeasurable)

theorem tangent_measurable (α b : ℝ) (x : Space d) (n : ℕ) : Measurable (tangentNorm α b x n) := by
  have hf := feature_meas α b x
  have hg := gate_meas α b x
  have f := average_meas (featureSq α b x) (by unfold featureSq;fun_prop) n
  have g := average_meas (gateSq α b x) (by unfold gateSq;fun_prop) n
  unfold tangentNorm initial signalAtom factor kernel; fun_prop

theorem tangent_congr (α b : ℝ) (x : Space d) (n : ℕ) {ω v : Draws d} (eq : ∀ i<n, ω i=v i) :
    tangentNorm α b x n ω=tangentNorm α b x n v := by
  have sum (f : Neuron d→ℝ) : (∑ i ∈ Finset.range n,f (ω i))=∑ i ∈ Finset.range n,f (v i) :=
    Finset.sum_congr rfl (fun i hi => congrArg f (eq i (Finset.mem_range.mp hi)))
  simp only [tangentNorm,initial,factor,kernel,average,sum]

/-- An explicitly positive portion of the limiting Gaussian gives a uniform positive-
probability lower tail for the tangent movement. -/
theorem tangent_positive_probability {α b : ℝ} (hd : 0<d) (ha : 0<α) (h1 : α≤1) (bp : 0<b)
    (x : Space d) (hx : ‖x‖=1) : ∃ p : ℝ, 0<p ∧ ∀ᶠ n : ℕ in atTop,
      p ≤ (law d).real {ω | limitFactor α b x < tangentNorm α b x n ω} := by
  let a := limitFactor α b x
  let μ := gaussianReal 0 (featureVariance α b x).toNNReal
  let G := fun z : ℝ => |z| * a
  have ap : 0<a := factor_pos hd ha h1 bp x hx
  have vp := (positive_moments ha h1 bp x hx).1
  have v0 : (featureVariance α b x).toNNReal≠0 := (toNNReal_pos.mpr vp).ne'
  have : NullSingletonClass μ := nullSingletonClass_gaussianReal v0
  have gm : Measurable G := by unfold G; fun_prop
  have fw : (μ.map G) (frontier (Ioi a))=0 := by
    rw [frontier_Ioi,Measure.map_apply gm (measurableSet_singleton a)]
    apply measure_mono_null (t:={-1,1}) _ ((Set.finite_singleton (1:ℝ)).insert (-1) |>.measure_zero μ)
    intro z hz; change |z| * a=a at hz
    have ih : |z|=1 := mul_right_cancel₀ ap.ne' (hz.trans (one_mul a).symm)
    rcases le_total 0 z with pos|neg
    · rw [abs_of_nonneg pos] at ih; simp [ih]
    · rw [abs_of_nonpos neg] at ih; simp [show z=-1 by linarith]
  have prob : 0<(μ.map G).real (Ioi a) := by
    rw [Measure.real,ENNReal.toReal_pos_iff]
    refine ⟨?_,measure_lt_top _ _⟩
    rw [Measure.map_apply gm measurableSet_Ioi]
    have sub : Ioo (1:ℝ) 2 ⊆ G ⁻¹' Ioi a := by
      intro z hz; change a < |z| * a; rw [abs_of_nonneg (by linarith [hz.1])]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hz.1 ap
    apply lt_of_lt_of_le _ (measure_mono sub)
    apply lt_of_le_of_ne bot_le; intro h
    have hh := gaussianReal_absolutelyContinuous' 0 v0 h.symm
    simp [Real.volume_Ioo] at hh
  have dist := tangent_limit ha h1 bp x hx
  have lim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' dist.tendsto fw
  change Tendsto (fun n => ((law d).map (tangentNorm α b x n)) (Ioi a)) _ (𝓝 ((μ.map G) (Ioi a))) at lim
  simp_rw [Measure.map_apply (tangent_measurable _ _ _ _) measurableSet_Ioi] at lim
  have lr := (ENNReal.tendsto_toReal (measure_ne_top (μ.map G) (Ioi a))).comp lim
  exact ⟨_,half_pos prob,(lr.eventually_const_lt (half_lt_self prob)).mono (fun _ hi => hi.le)⟩

end PhysicalTangentLaw
