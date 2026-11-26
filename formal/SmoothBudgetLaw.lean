module

public import SmoothGaussianLaw
import Mathlib.Tactic

/-! Distribution of the squared displacement of the infinite-time nonlinear GD iterate.
The random variable is defined on every seed by a measurable extension. -/
@[expose] public section
noncomputable section
namespace SmoothBudgetLaw
open SmoothSeedLaw SmoothGramLimit SmoothTrainingLimit TwoLayerNetwork TwoLayerLimit NonlinearBudget
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped InnerProduct NNReal Topology
variable {n d k : ℕ}

theorem packed_continuous (n : ℕ) : Continuous (packed (d:=d) n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin (d+1) => ℝ)).comp
  apply continuous_pi; rintro ⟨i,j⟩
  refine Fin.cases ?_ (fun t => ?_) j
  · exact continuous_fst.comp (continuous_apply (i:ℕ))
  · exact (EuclideanSpace.proj t : Space d →L[ℝ] ℝ).continuous.comp (continuous_snd.comp (continuous_apply (i:ℕ)))

theorem jac_continuous {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (act : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : Continuous (jac (n:=n) φ g b x) := by
  have cf : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (act.first t).continuousAt)
  have cg := g_continuous act
  let M : Matrix (Fin k) (Fin n × Fin (d+1)) ℝ ≃ₗ[ℝ] (Params n d →L[ℝ] Space k) :=
    Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap
  apply M.toLinearMap.continuous_of_finiteDimensional.comp
  apply continuous_pi; intro j
  apply continuous_pi; rintro ⟨i,p⟩
  refine Fin.cases ?_ (fun t => ?_) p
  · change Continuous (fun z : Params n d => φ (b j*inner ℝ (TwoLayerNetwork.hidden z i) (x j))/Real.sqrt n)
    unfold TwoLayerNetwork.hidden;fun_prop
  · change Continuous (fun z : Params n d => (b j*(readout z i*g (b j*inner ℝ (TwoLayerNetwork.hidden z i) (x j)))*x j t)/Real.sqrt n)
    unfold readout TwoLayerNetwork.hidden;fun_prop

def iterate (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (h : ℝ) (n : ℕ) (ω : Draws d) :=
  gd (residual φ b x y (packed n ω)) (fun z => jac φ g b x (packed n ω+z)) h

theorem iterate_continuous {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (act : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k) (h : ℝ) (n t : ℕ) :
    Continuous (fun ω => iterate φ g b x y h n ω t) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    let z := fun ω => packed n ω+iterate φ g b x y h n ω t
    have cz : Continuous z := (packed_continuous n).add ih
    have jj := (jac_continuous act b x).comp cz
    have ff := residual_continuous (continuous_iff_continuousAt.mpr (fun t => (act.first t).continuousAt)) b x y (0:Params n d)
    have rr : Continuous (fun ω => residual φ b x y (packed n ω) (iterate φ g b x y h n ω t)) := by
      have p := ff.comp cz
      simpa only [Function.comp_def,TwoLayerNetwork.residual,zero_add,z] using p
    change Continuous (fun ω => iterate φ g b x y h n ω t+(-h) • ((jac φ g b x (z ω))†)
      (residual φ b x y (packed n ω) (iterate φ g b x y h n ω t)))
    exact ih.add ((((ContinuousLinearMap.adjoint : (Params n d →L[ℝ] Space k) ≃ₗᵢ⋆[ℝ] _).continuous.comp jj).clm_apply rr).const_smul (-h))

/-- Real-valued measurable extension of the terminal squared displacement.
On every convergent trajectory it equals the actual squared distance from initialization. -/
def trained (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (h : ℝ) (n : ℕ) (ω : Draws d) := limsup (fun t => ‖iterate φ g b x y h n ω t‖^2) atTop

theorem trained_measurable {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (act : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k) (h : ℝ) (n : ℕ) :
    Measurable (trained φ g b x y h n) :=
  Measurable.limsup (fun t => ((iterate_continuous act b x y h n t).norm.pow 2).measurable)

theorem trained_eq {φ g : ℝ → ℝ} {b : Fin k → ℝ} {x : Fin k → Space d} {y : Space k}
    {h : ℝ} {ω : Draws d} {D : Params n d} (lim : Tendsto (iterate φ g b x y h n ω) atTop (𝓝 D)) :
    trained φ g b x y h n ω=‖D‖^2 := (lim.norm.pow 2).limsup_eq

theorem frame_ker (G : Space k →L[ℝ] Space k) {l : ℝ} (lp : 0<l)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (G v)) : LinearMap.ker G.toLinearMap=⊥ := by
  apply LinearMap.ker_eq_bot'.mpr; intro v hv
  have s := frame v
  change G v=0 at hv
  rw [hv,inner_zero_right] at s
  by_contra nv
  exact (not_lt_of_ge s) (mul_pos lp (sq_pos_of_pos (norm_pos_iff.mpr nv)))

def populationEquiv (G : Space k →L[ℝ] Space k) {l : ℝ} (lp : 0<l)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (G v)) : Space k ≃L[ℝ] Space k :=
  ContinuousLinearEquiv.ofBijective G (frame_ker G lp frame)
    (LinearMap.ker_eq_bot_iff_range_eq_top.mp (frame_ker G lp frame))

/-- Stability of the inverse Gram quadratic form on a fixed residual ball.
Only the fixed population inverse occurs in the constant. -/
theorem reference_stability (K E : Space k ≃L[ℝ] Space k) {l τ V : ℝ} (lp : 0<l)
    (small : τ≤l/2) (τ₀ : 0≤τ) (V₀ : 0≤V)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (E v))
    (close : ‖K.toContinuousLinearMap-E.toContinuousLinearMap‖≤τ)
    (r : Space k) (res : ‖r‖≤V) :
    |inner ℝ r (K.symm r)-inner ℝ r (E.symm r)| ≤
      (V*‖E.symm.toContinuousLinearMap‖*(2*V/l))*τ := by
  let D := K.toContinuousLinearMap-E.toContinuousLinearMap
  let z := K.symm r
  have kz : K z=r := K.apply_symm_apply r
  have dz : ‖D z‖≤τ*‖z‖ := (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right close (norm_nonneg _))
  have de : inner ℝ z (E z) ≤ inner ℝ z r + ‖z‖*(τ*‖z‖) := by
    have s := (abs_real_inner_le_norm z (D z)).trans (mul_le_mul_of_nonneg_left dz (norm_nonneg _))
    change |inner ℝ z (K z-E z)|≤_ at s
    rw [inner_sub_right,kz] at s
    linarith [(abs_le.mp s).1]
  have nz : ‖z‖≤2*V/l := by
    rcases eq_or_lt_of_le (norm_nonneg z) with eq|zp
    · rw [←eq];positivity
    · have cs := (real_inner_le_norm z r).trans (mul_le_mul_of_nonneg_left res zp.le)
      apply (le_div_iff₀ lp).mpr
      apply le_of_mul_le_mul_right (a:=‖z‖)
      · nlinarith only [frame z,de,cs,mul_le_mul_of_nonneg_right small (sq_nonneg ‖z‖)]
      · exact zp
  have eq : z-E.symm r = E.symm (-(D z)) := by
    apply E.injective
    rw [map_sub,E.apply_symm_apply,E.apply_symm_apply]
    change E z-r = -(K z-E z)
    rw [kz,neg_sub]
  rw [←inner_sub_right,eq]
  calc
    _ ≤ ‖r‖*‖E.symm (-(D z))‖ := abs_real_inner_le_norm _ _
    _ ≤ V*(‖E.symm.toContinuousLinearMap‖*(τ*(2*V/l))) := by
      apply mul_le_mul res _ (norm_nonneg _) V₀
      apply (E.symm.toContinuousLinearMap.le_opNorm _).trans
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left (dz.trans (mul_le_mul_of_nonneg_left nz τ₀)) (norm_nonneg _)
    _ = _ := by ring


def quadratic (E : Space k ≃L[ℝ] Space k) (y z : Space k) := inner ℝ (z-y) (E.symm (z-y))

/-- An arbitrary completion assigns the actual squared movement to every
convergent interpolating GD trajectory with invertible empirical Gram.
Values on all other seeds are unrestricted. -/
def Completion (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k) (h : ℝ)
    (B : ℕ → Draws d → ℝ) : Prop :=
  ∀ n ω D, Tendsto (iterate φ g b x y h n ω) atTop (𝓝 D) →
    TwoLayerNetwork.residual φ b x y (packed n ω) D = 0 →
    (∃ K : Space k ≃L[ℝ] Space k, K.toContinuousLinearMap = gram φ g b x (packed n ω)) →
    B n ω=‖D‖^2

theorem population_replacement (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v))
    (B : ℕ → Draws d → ℝ) (agrees : Completion φ g b x y h B) :
    let E := populationEquiv (Γ φ g b x) lp frame
    TendstoInMeasure (law d) (B - fun n => quadratic E y ∘ initPred φ b x n) atTop 0 := by
  intro E
  let G := Γ φ g b x
  have eqG : E.toContinuousLinearMap=G := rfl
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε ep
  apply Metric.tendsto_nhds.mpr
  intro η ηp
  let e := η/4
  have epos : 0<e := by dsimp [e];positivity
  let C := 2*(∑ j, Cmat φ b x j j)+2*‖y‖^2
  let V := sqrt (|C|/e+1)
  have vp : 0<V := by dsimp [V];positivity
  have Vcut : C/V^2 ≤ e := by
    change C/(sqrt _)^2 ≤ e
    rw [sq_sqrt (by positivity)];apply (div_le_iff₀ (by positivity)).mpr
    have eq : e*(|C|/e+1) = |C|+e := by field_simp
    rw [eq];linarith [le_abs_self C]
  let H := V*‖E.symm.toContinuousLinearMap‖*(2*V/l)
  have H₀ : 0≤H := by dsimp [H];positivity
  let τ := min (l/2) (ε/(4*(1+H)))
  have τpos : 0<τ := lt_min (by positivity) (by positivity)
  have mulτ : H*τ ≤ ε/4 := by
    have u := (le_div_iff₀ (show 0<4*(1+H) by positivity)).mp (min_le_right (l/2) (ε/(4*(1+H))))
    change τ*(4*(1+H))≤ε at u
    linarith only [show 4*(τ*H)+4*τ≤ε by nlinarith only [u],τpos]
  obtain ⟨L,_,emp⟩ := smooth_movement_in_probability hk act b bp x hx y l h lp hp step frame e epos
  have ll := (tendstoInMeasure_iff_measureReal_norm.mp (gram_law act b x)) τ τpos
  have az : Tendsto (fun n => L*SmoothTrainingLimit.scale n) atTop (𝓝 0) := by simpa using SmoothTrainingLimit.scale_zero.const_mul L
  filter_upwards [eventually_ge_atTop 1,emp,ll.eventually_lt_const epos,
    az.eventually_lt_const (show 0<ε/4 by positivity)] with n hn fast near rate
  let F := fun ω : Draws d => TwoLayerNetwork.residual φ b x y (packed n ω)
  let J := fun (ω : Draws d) z => jac φ g b x (packed n ω+z)
  let A := fun ω : Draws d => jac φ g b x (packed n ω)
  let bad₁ := {ω : Draws d | ¬Endpoint (F ω) (J ω) (A ω) h (L*SmoothTrainingLimit.scale n)}
  let bad₂ := {ω : Draws d | τ≤‖gram φ g b x (packed n ω)-G‖}
  let bad₃ := {ω : Draws d | V^2≤‖F ω 0‖^2}
  have p₁ : (law d).real bad₁ ≤ e := fast
  have p₂ : (law d).real bad₂ ≤ e := near.le
  have p₃ : (law d).real bad₃ ≤ e := (residual_tail act b x y n hn (sq_pos_of_pos vp)).trans Vcut
  have union := (measureReal_union_le (μ:=law d) (bad₁∪bad₂) bad₃).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add p₁ p₂)) p₃)
  have sub : {ω : Draws d | ε≤|B n ω-quadratic E y (initPred φ b x n ω)|} ⊆ (bad₁∪bad₂)∪bad₃ := by
    intro ω miss
    by_contra outside
    have endpt : Endpoint (F ω) (J ω) (A ω) h (L*SmoothTrainingLimit.scale n) := by_contra (fun z => outside (Or.inl (Or.inl z)))
    have close : ‖gram φ g b x (packed n ω)-G‖≤τ := le_of_not_ge (fun z => outside (Or.inl (Or.inr z)))
    have res : ‖F ω 0‖≤V := (sq_le_sq₀ (norm_nonneg _) vp.le).mp (le_of_not_ge (fun z => outside (Or.inr z)))
    obtain ⟨K,inv,D,lim,fit,err⟩ := endpt
    have kop : K.toContinuousLinearMap=gram φ g b x (packed n ω) := ContinuousLinearMap.ext inv
    have val := agrees n ω D lim fit ⟨K,kop⟩
    let r := F ω 0
    have stab := reference_stability K E lp (min_le_left _ _) τpos.le vp.le frame
      (by rwa [kop,eqG]) r res
    have qr : quadratic E y (initPred φ b x n ω)=inner ℝ r (E.symm r) := by
      dsimp [r,F]; rw [initial_residual];rfl
    change ε≤|B n ω-quadratic E y (initPred φ b x n ω)| at miss
    rw [val,qr] at miss
    have tri := abs_sub_le (‖D‖^2) (inner ℝ r (K.symm r)) (inner ℝ r (E.symm r))
    change |‖D‖^2-inner ℝ r (K.symm r)|≤_ at err
    change |inner ℝ r (K.symm r)-inner ℝ r (E.symm r)|≤H*τ at stab
    linarith
  have bound := (measureReal_mono (μ:=law d) sub).trans union
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg,Pi.sub_apply,Pi.zero_apply,
    Function.comp_apply,Real.norm_eq_abs]
  exact lt_of_le_of_lt bound (by dsimp [e];linarith)

/-- Full nonlinear limiting law for any measurable completion, including a
fixed assigned value on seeds with failed convergence, fit or invertibility. -/
theorem smooth_budget_law_of_completion (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v))
    (B : ℕ → Draws d → ℝ) (agrees : Completion φ g b x y h B) (meas : ∀ n, AEMeasurable (B n) (law d)) :
    let E := populationEquiv (Γ φ g b x) lp frame
    TendstoInDistribution B atTop (quadratic E y) (fun _ => law d) (multivariateGaussian 0 (Cmat φ b x)) := by
  intro E
  have cq : Continuous (quadratic E y) := by unfold quadratic;fun_prop
  have clt : TendstoInDistribution (fun n => quadratic E y ∘ initPred φ b x n) atTop
      (quadratic E y) (fun _ => law d) (multivariateGaussian 0 (Cmat φ b x)) :=
    TendstoInDistribution.continuous_comp (g:=quadratic E y) cq (SmoothGaussianLaw.prediction_clt act b x)
  exact tendstoInDistribution_of_tendstoInMeasure_sub B (quadratic E y) clt
    (population_replacement hk act b bp x hx y l h lp hp step frame B agrees) meas

theorem smooth_budget_law (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v)) :
    TendstoInDistribution (trained φ g b x y h) atTop
      (quadratic (populationEquiv (Γ φ g b x) lp frame) y) (fun _ => law d)
      (multivariateGaussian 0 (Cmat φ b x)) :=
  smooth_budget_law_of_completion hk act b bp x hx y l h lp hp step frame _
    (fun _ _ _ lim _ _ => trained_eq lim) (fun n => (trained_measurable act b x y h n).aemeasurable)

theorem softplus_budget_law (hk : 0<k) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ softplus sigmoid b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ softplus sigmoid b x v)) :
    TendstoInDistribution (trained softplus sigmoid b x y h) atTop
      (quadratic (populationEquiv (Γ softplus sigmoid b x) lp frame) y) (fun _ => law d)
      (multivariateGaussian 0 (Cmat softplus b x)) :=
  smooth_budget_law hk softplus_activation b bp x hx y l h lp hp step frame


/-- The measurable success event, including prediction interpolation and
invertibility of the initialization Gram. -/
def success (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (h : ℝ) (n : ℕ) : Set (Draws d) :=
  {ω | (∃ D, Tendsto (iterate φ g b x y h n ω) atTop (𝓝 D)) ∧
    Tendsto (fun t => TwoLayerNetwork.residual φ b x y (packed n ω) (iterate φ g b x y h n ω t))
      atTop (𝓝 0) ∧ IsUnit (gram φ g b x (packed n ω))}

theorem success_measurable {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (act : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k) (h : ℝ) (n : ℕ) :
    MeasurableSet (success φ g b x y h n) := by
  have cf : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (act.first t).continuousAt)
  have cr := residual_continuous cf b x y (0:Params n d)
  have rr (t : ℕ) : Continuous (fun ω => TwoLayerNetwork.residual φ b x y (packed n ω)
      (iterate φ g b x y h n ω t)) := by
    have c := cr.comp ((packed_continuous n).add (iterate_continuous act b x y h n t))
    simpa only [Function.comp_def,TwoLayerNetwork.residual,zero_add,Pi.add_apply] using c
  exact (measurableSet_exists_tendsto (l:=atTop) fun t => (iterate_continuous act b x y h n t).measurable).inter
    ((measurableSet_tendsto_fun (l:=atTop) (fun t => (rr t).measurable) (g:=fun _ => 0) measurable_const).inter
      ((gram_measurable act b x n) (Units.isOpen.measurableSet)))

theorem mem_success {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (act : Activation φ g L₁ L₂)
    {b : Fin k → ℝ} {x : Fin k → Space d} {y : Space k} {h : ℝ} {ω : Draws d} {D : Params n d}
    (lim : Tendsto (iterate φ g b x y h n ω) atTop (𝓝 D))
    (fit : TwoLayerNetwork.residual φ b x y (packed n ω) D = 0)
    (inv : ∃ K : Space k ≃L[ℝ] Space k, K.toContinuousLinearMap = gram φ g b x (packed n ω)) :
    ω∈success φ g b x y h n := by
  have c := residual_continuous (continuous_iff_continuousAt.mpr (fun t => (act.first t).continuousAt)) b x y (packed n ω)
  obtain ⟨K,eq⟩ := inv
  exact ⟨⟨D,lim⟩,fit ▸ (c.tendsto D).comp lim,eq ▸ K.toUnit.isUnit⟩

/-- The probability of failed convergence, interpolation or invertibility
tends to zero as width increases. -/
theorem failure_probability_zero (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v)) :
    Tendsto (fun n : ℕ => (law d).real (success φ g b x y h n)ᶜ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr; intro ε ep
  obtain ⟨L,_,hf⟩ := smooth_movement_in_probability hk act b bp x hx y l h lp hp step frame (ε/2) (by positivity)
  filter_upwards [hf] with n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  apply lt_of_le_of_lt ((measureReal_mono ?_).trans hn) (half_lt_self ep)
  intro ω miss ok
  obtain ⟨K,inv,D,lim,fit,_⟩ := ok
  exact miss (mem_success act lim fit ⟨K,ContinuousLinearMap.ext inv⟩)

/-- The explicit fixed-value convention used in the statement of the
finite-width theorem. -/
def fixedCompletion (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (h a : ℝ) (n : ℕ) : Draws d → ℝ := by
  classical
  exact (success φ g b x y h n).piecewise (trained φ g b x y h n) (fun _ => a)

theorem fixed_budget_law (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h a : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v)) :
    TendstoInDistribution (fixedCompletion φ g b x y h a) atTop
      (quadratic (populationEquiv (Γ φ g b x) lp frame) y) (fun _ => law d)
      (multivariateGaussian 0 (Cmat φ b x)) := by
  classical
  apply smooth_budget_law_of_completion hk act b bp x hx y l h lp hp step frame
  · intro n ω D lim fit inv
    simp [fixedCompletion,Set.piecewise,mem_success act lim fit inv,trained_eq lim]
  · intro n
    exact ((trained_measurable act b x y h n).piecewise (success_measurable act b x y h n) measurable_const).aemeasurable

/-- Length and direction representation of every fixed input family, including
zero rows. Thus the bounds on the direction do not restrict the design. -/
theorem factor_design (v : Fin k → Space d) :
    ∃ (b : Fin k → ℝ) (x : Fin k → Space d), (∀ j, 0≤b j) ∧ (∀ j, ‖x j‖≤1) ∧
      (∀ j, b j • x j=v j) ∧ (∀ j w, b j*inner ℝ w (x j)=inner ℝ w (v j)) := by
  let b := fun j => max 1 ‖v j‖
  let x := fun j => (b j)⁻¹ • v j
  have bp (j) : 0<b j := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have eq (j) : b j • x j=v j := by simp [x,smul_smul,(bp j).ne']
  refine ⟨b,x,fun j => (bp j).le,?_,eq,?_⟩
  · intro j
    change ‖(b j)⁻¹ • v j‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (bp j)),←div_eq_inv_mul]
    exact (div_le_one (bp j)).mpr (le_max_right _ _)
  · intro j w
    rw [←real_inner_smul_right,eq]

end SmoothBudgetLaw
