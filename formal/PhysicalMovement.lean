module

public import PhysicalInitialization
public import PhysicalTangentIdentity
import Mathlib.Tactic

/-! A positive-probability lower bound on the actual relative physical displacement of
full-batch gradient descent at positive fixed input dimension. -/
@[expose] public section
noncomputable section
namespace PhysicalMovement
open Real MeasureTheory ProbabilityTheory Set Filter TwoLayerNetwork TwoLayerBudget TwoLayerLimit
  SmoothSeedLaw PhysicalInitialization PhysicalTangentLaw SmoothGramLimit NonlinearBudget
open scoped InnerProduct Topology NNReal
variable {n d : ℕ}

def extend (z : Params n d) (i : ℕ) : Neuron d :=
  if h : i<n then (readout z ⟨i,h⟩, TwoLayerNetwork.hidden z ⟨i,h⟩) else (0,0)

private theorem pack_extend (z : Params n d) : packed n (extend z)=z := by
  ext ⟨i,j⟩
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [packed,extend,readout,TwoLayerNetwork.hidden]

private theorem meas_extend : Measurable (extend (n:=n) (d:=d)) := by
  apply Measurable.of_eval; intro i
  by_cases h : i<n
  · simp only [extend,dite_eq_left h]; unfold readout TwoLayerNetwork.hidden; fun_prop
  · simp only [extend,dite_eq_right h]; fun_prop

private theorem phys_norm_meas : Measurable (fun z : Params n d => ‖physical z‖) := by
  have eq : (fun z : Params n d => ‖physical z‖) = fun z => sqrt ((∑ i,(readout z i)^2)/n + (∑ i,‖TwoLayerNetwork.hidden z i‖^2)/d) := by
    funext z; rw [←physical_sq,sqrt_sq (norm_nonneg _)]
  rw [eq]; unfold TwoLayerNetwork.hidden readout; fun_prop

def F (α b : ℝ) (x : Space d) (z : Params n d) := residual (leaky α) (fun _ : Fin 1 => b) (fun _ => x) 0 z
def A (α b : ℝ) (x : Space d) (z : Params n d) := jac (leaky α) (slope α) (fun _ : Fin 1 => b) (fun _ => x) z
def J (α b : ℝ) (x : Space d) (z v : Params n d) := A α b x (z+v)
def tangent (α b : ℝ) (x : Space d) (z : Params n d) := tangentNorm α b x n (extend z)

private theorem on_packed (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) :
    tangent α b x (packed n ω) = tangentNorm α b x n ω := by
  apply tangent_congr; intro i hi; simp [extend,hi]

private theorem scale_zero : Tendsto TwoLayerLimit.scale atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => log n/cube n) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : 0<(3:ℝ)⁻¹)).tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  change Tendsto (fun n : ℕ => sqrt (log n/cube n)) _ _
  simpa only [sqrt_zero] using h.sqrt

private theorem endpoint {α b : ℝ} (ha : 0<α) (h1 : α≤1) (bp : 0<b) (x : Space d) (hx : ‖x‖=1)
    (η : ℝ) (ep : 0<η) : ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      (stdGaussian (Params n d)).real {z | ¬JointEndpoint (F α b x z) (J α b x z) (A α b x z)
        (‖A α b x z‖^2)⁻¹ (L*scale n) (L*scale n)} ≤ η := by
  apply joint_movement_in_probability (by decide : 0<1) α (b^2) ha h1 (sq_pos_of_pos bp)
    (fun _ => b) (fun _ => bp) (fun _ => x) (fun _ => hx) 0 _
    (fun _ => smoothSlopes (slope α) (fun _ => b) (fun _ => x)) _ η ep
  · intro v
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one,Fin.sum_univ_one,norm_smul,hx,mul_one,Real.norm_eq_abs,sq_abs]
    nlinarith only [sq_nonneg (v 0*b)]
  · intro n z j i; exact slope_ok h1 _

private theorem initial_norm_tail (hd : 0<d) (η : ℝ) (ep : 0<η) : ∀ᶠ n : ℕ in atTop,
    (stdGaussian (Params n d)).real {z | (1/2:ℝ)≤|‖physical z‖/sqrt n-1|} ≤ η := by
  let u (n : ℕ) (ω : Draws d) := ‖physical (packed n ω)‖/sqrt n
  have p : TendstoInMeasure (law d) u atTop (fun _ => 1) := by
    apply tendstoInMeasure_of_tendsto_ae _ (normalized hd)
    intro n; exact ((phys_norm_meas.comp_aemeasurable (packed_law n d).aemeasurable).div_const _).aestronglyMeasurable
  have l := (tendstoInMeasure_iff_measureReal_norm.mp p (1/2) (by norm_num)).eventually_lt_const ep
  filter_upwards [l] with n hh
  have ms : MeasurableSet {z : Params n d | (1/2:ℝ)≤|‖physical z‖/sqrt n-1|} := by have := phys_norm_meas (n:=n) (d:=d); measurability
  rw [←(packed_law n d).measureReal_eq ms]
  exact hh.le

/-- The good seeds form a Borel set under the actual packed standard Gaussian.
At every seed in this set, the physical displacement of the limiting interpolant,
relative to its physical initialization, exceeds `c/√n`. -/
theorem nonlinear_relative_lower {α b : ℝ} (hd : 0<d) (ha : 0<α) (h1 : α≤1) (bp : 0<b)
    (x : Space d) (hx : ‖x‖=1) :
    ∃ c p : ℝ, 0<c ∧ 0<p ∧ ∀ᶠ n : ℕ in atTop, ∃ E : Set (Params n d),
      MeasurableSet E ∧ p ≤ (stdGaussian (Params n d)).real E ∧ ∀ z∈E,
      ∃ D : Params n d, Tendsto (gd (F α b x z) (J α b x z) (‖A α b x z‖^2)⁻¹) atTop (𝓝 D) ∧
        F α b x z D=0 ∧ 0<‖physical z‖ ∧ c/sqrt n < ‖physical D‖/‖physical z‖ := by
  let a := limitFactor α b x
  have ap : 0<a := factor_pos hd ha h1 bp x hx
  obtain ⟨p,pp,large⟩ := tangent_positive_probability hd ha h1 bp x hx
  obtain ⟨L,_,gdgood⟩ := endpoint ha h1 bp x hx (p/4) (by positivity)
  have e : Tendsto (fun n => L*scale n) atTop (𝓝 0) := by simpa only [mul_zero] using scale_zero.const_mul L
  refine ⟨a/4,p/2,by positivity,by positivity,?_⟩
  filter_upwards [large,gdgood,e.eventually_lt_const (half_pos ap),initial_norm_tail hd (p/4) (by positivity),eventually_ge_atTop 1] with n ref gd small denom hn
  let μ := stdGaussian (Params n d)
  let high := {z : Params n d | a<tangent α b x z}
  let den := {z : Params n d | (1/2:ℝ)≤|‖physical z‖/sqrt n-1|}
  let bad := {z : Params n d | ¬JointEndpoint (F α b x z) (J α b x z) (A α b x z)
      (‖A α b x z‖^2)⁻¹ (L*scale n) (L*scale n)}
  let hull := toMeasurable μ bad
  have mf : Measurable (tangent α b x (n:=n)) := (tangent_measurable α b x n).comp meas_extend
  have mh : MeasurableSet high := measurableSet_lt measurable_const mf
  have md : MeasurableSet den := by have := phys_norm_meas (n:=n) (d:=d); unfold den; measurability
  have mhull : MeasurableSet hull := measurableSet_toMeasurable _ _
  have hi : p≤μ.real high := by
    rw [←(packed_law n d).measureReal_eq mh]; simpa only [high,on_packed,mem_ofPred_eq] using ref
  have hu : μ.real hull≤p/4 := by simpa only [hull,Measure.real,measure_toMeasurable] using gd
  refine ⟨high \ (hull ∪ den),mh.diff (mhull.union md),?_,?_⟩
  · have l := le_measureReal_sdiff (μ:=μ) (s₁:=high) (s₂:=hull ∪ den)
    have u := measureReal_union_le (μ:=μ) hull den
    change μ.real den≤p/4 at denom
    linarith
  intro z hz
  obtain ⟨hh,outs⟩ := hz
  have ok : z∉bad := fun fail => outs (Or.inl (subset_toMeasurable μ bad fail))
  have hit : JointEndpoint (F α b x z) (J α b x z) (A α b x z) (‖A α b x z‖^2)⁻¹ (L*scale n) (L*scale n) := not_not.mp ok
  obtain ⟨K,gram,D,conv,fit,vec,_⟩ := hit
  have star := PhysicalTangentIdentity.identity α b x hx n (extend z) K
  dsimp only at star
  rw [pack_extend] at star
  have close := hidden_sub_le hd D (((A α b x z)†) (K.symm (-F α b x z 0)))
  have exactStar : hiddenNorm (((A α b x z)†) (K.symm (-F α b x z 0))) = tangentNorm α b x n (extend z) := star gram
  rw [exactStar] at close
  change a < tangentNorm α b x n (extend z) at hh
  have num : a/2<‖physical D‖ := by linarith [neg_le_of_abs_le (close.trans vec),physical_hidden_le D]
  have no : ¬ (1/2:ℝ) ≤ |‖physical z‖/sqrt n-1| := fun h => outs (Or.inr h)
  have limits := abs_lt.mp (lt_of_not_ge no)
  have sp : 0<sqrt (n:ℝ) := sqrt_pos.mpr (by exact_mod_cast hn)
  have pos : 0<‖physical z‖ := (div_pos_iff_of_pos_right sp).mp (by linarith [limits.1] : 0<‖physical z‖/sqrt n)
  have upper : ‖physical z‖<2*sqrt n := (div_lt_iff₀ sp).mp (by linarith [limits.2])
  refine ⟨D,conv,fit,pos,(div_lt_div_iff₀ sp pos).mpr ?_⟩
  nlinarith only [mul_lt_mul_of_pos_left upper ap,mul_lt_mul_of_pos_right num sp]

end PhysicalMovement
