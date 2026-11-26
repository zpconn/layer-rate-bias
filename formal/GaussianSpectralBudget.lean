module
public import GaussianTraceBudget
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-! Correlated centered Gaussian initialization in any finite orthonormal eigenbasis.
The displacement can depend on the same initialization. -/
@[expose] public section
noncomputable section
namespace GaussianSpectralBudget
open MeasureTheory ProbabilityTheory WithLp Matrix Real Finset GaussianTraceBudget
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev E (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def synth (b : OrthonormalBasis ι ℝ (E ι)) (v z : ι→ℝ) : E ι :=
  ∑ i,(sqrt (v i)*z i) • b i

omit [DecidableEq ι] in
private theorem synth_cont (b : OrthonormalBasis ι ℝ (E ι)) (v : ι→ℝ) :
    Continuous (synth b v) := by unfold synth;fun_prop

def Eigen (S : Matrix ι ι ℝ) (b : OrthonormalBasis ι ℝ (E ι)) (v : ι→ℝ) : Prop :=
  ∀ i,toEuclideanCLM (𝕜:=ℝ) S (b i)=v i • b i

theorem eigenbasis_exists (S : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    ∃ (b : OrthonormalBasis ι ℝ (E ι)) (v : ι→ℝ), (∀ i,0≤v i) ∧ Eigen S b v := by
  refine ⟨hS.1.eigenvectorBasis,hS.1.eigenvalues,hS.eigenvalues_nonneg,fun i => ?_⟩
  apply WithLp.ofLp_injective
  simpa using hS.1.mulVec_eigenvectorBasis i

omit [DecidableEq ι] in
theorem norm_synth (b : OrthonormalBasis ι ℝ (E ι)) (v : ι→ℝ) (hv : ∀ i,0≤v i) (z : ι→ℝ) :
    ‖synth b v z‖^2=energy v z := by
  let c : E ι := toLp 2 (fun i => sqrt (v i)*z i)
  have h : synth b v z=b.repr.symm c := by
    simpa [synth,c] using (b.sum_repr (b.repr.symm c))
  rw [h,b.repr.symm.norm_map,EuclideanSpace.real_norm_sq_eq]
  simp only [c,mul_pow,sq_sqrt (hv _),energy]

private theorem eigen_quad {S : Matrix ι ι ℝ} {b : OrthonormalBasis ι ℝ (E ι)} {v : ι→ℝ}
    (h : Eigen S b v) (t : E ι) : t ⬝ᵥ S *ᵥ t=∑ i,v i*(inner ℝ (b i) t)^2 := by
  rw [←inner_toEuclideanCLM]
  have act : toEuclideanCLM (𝕜:=ℝ) S t=∑ i, (b.repr t i*v i) • b i := by
    conv_lhs => arg 2; rw [←b.sum_repr t]
    simp only [map_sum,map_smul]
    apply sum_congr rfl;intro i _;rw [h i,smul_smul]
  rw [act,inner_sum]
  apply sum_congr rfl;intro i _
  rw [real_inner_smul_right,OrthonormalBasis.repr_apply_apply,real_inner_comm (b i) t];ring

/-- The Gaussian synthesis is precisely mathlib's centered multivariate Gaussian law
with the specified positive-semidefinite covariance, including zero eigenvalues. -/
theorem synthesis_law {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {b : OrthonormalBasis ι ℝ (E ι)}
    {v : ι→ℝ} (hv : ∀ i,0≤v i) (he : Eigen S b v) :
    MeasurePreserving (synth b v) (law ι) (multivariateGaussian 0 S) := by
  refine ⟨(synth_cont b v).measurable,Measure.ext_of_charFun ?_⟩
  ext t
  let d : E ι := toLp 2 (fun i => sqrt (v i)*inner ℝ (b i) t)
  have ip (z : ι→ℝ) : inner ℝ (synth b v z) t=inner ℝ (toLp 2 z : E ι) d := by
    rw [synth,sum_inner,PiLp.inner_apply]
    apply sum_congr rfl;intro i _
    change inner ℝ ((sqrt (v i)*z i) • b i) t=(sqrt (v i)*inner ℝ (b i) t)*z i
    rw [real_inner_smul_left];ring
  have er : ‖d‖^2=t ⬝ᵥ S *ᵥ t := by
    rw [eigen_quad he,EuclideanSpace.real_norm_sq_eq]
    simp only [d,mul_pow,sq_sqrt (hv _)]
  have cf : charFun ((law ι).map (synth b v)) t=charFun (stdGaussian (E ι)) d := by
    rw [←map_pi_eq_stdGaussian,charFun_apply,charFun_apply,
      integral_map (synth_cont b v).aemeasurable (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    simp_rw [ip]
  rw [cf,charFun_stdGaussian,charFun_multivariateGaussian hS,inner_zero_right,←er]
  push_cast;ring_nf

private theorem eigen_trace {S : Matrix ι ι ℝ} {b : OrthonormalBasis ι ℝ (E ι)} {v : ι→ℝ}
    (he : Eigen S b v) : S.trace=∑ i,v i := by
  have ht := S.trace_toLin_eq (EuclideanSpace.basisFun ι ℝ).toBasis
  rw [←ht,LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  rw [←Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply]
  change (∑ i,b.toBasis.repr (toEuclideanCLM (𝕜:=ℝ) S (b i)) i)=_
  apply sum_congr rfl;intro i _;rw [he i];simp

theorem trace_identities {S : Matrix ι ι ℝ} {b : OrthonormalBasis ι ℝ (E ι)} {v : ι→ℝ}
    (he : Eigen S b v) : S.trace=∑ i,v i ∧ (S^2).trace=∑ i,(v i)^2 := by
  refine ⟨eigen_trace he,eigen_trace (b:=b) (v:=fun i => v i^2) (fun i => ?_)⟩
  change toEuclideanCLM (𝕜:=ℝ) (S^2) (b i)=(v i)^2 • b i
  rw [sq,map_mul,mul_apply_eq_comp,he,map_smul,he,smul_smul,sq]

/-- Explicit mean and covariance of the synthesized vector, in the original coordinates. -/
theorem synthesized_gaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {b : OrthonormalBasis ι ℝ (E ι)} {v : ι→ℝ} (hv : ∀ i,0≤v i) (he : Eigen S b v) :
    let μ := (law ι).map (synth b v)
    (∫ x,x ∂μ)=0 ∧ ∀ i j, covariance (fun x : E ι => x i) (fun x => x j) μ=S i j := by
  dsimp only
  rw [(synthesis_law hS hv he).map_eq]
  exact ⟨integral_id_multivariateGaussian,fun _ _ => covariance_eval_multivariateGaussian hS _ _⟩

/-- Coordinate-free trace moments of the actual centered Gaussian's squared norm. -/
theorem norm_moments (S : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    (∫ x : E ι,‖x‖^2 ∂multivariateGaussian 0 S)=S.trace ∧
      variance (fun x : E ι => ‖x‖^2) (multivariateGaussian 0 S)=2*(S^2).trace := by
  obtain ⟨b,v,hv,he⟩ := eigenbasis_exists S hS
  have law_eq := synthesis_law hS hv he
  have var := law_eq.variance_fun_comp (f:=fun x => ‖x‖^2) (by fun_prop)
  have mean := law_eq.hasLaw.integral_comp (f:=fun x => ‖x‖^2) (by fun_prop)
  simp only [Function.comp_def,norm_synth b v hv] at mean var
  rw [←mean,←var,(trace_identities he).1,(trace_identities he).2]
  exact moments v

/-- Markov/Chebyshev relative movement bound in physical coordinates, for an arbitrary
seed-dependent displacement and observable upper budget on its squared norm. -/
theorem relative_tail (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (ht : 0<S.trace)
    (d : E ι→E ι) (B : E ι→ℝ) (hd : Measurable d) (hB : Measurable B)
    {Λ K : ℝ} (hΛ : 0≤Λ) (hK : 0≤K) (metric : ∀ x,‖d x‖^2≤Λ*B x) :
    (multivariateGaussian 0 S).real {x | 2*Λ*K*‖x‖^2<‖d x‖^2*S.trace} ≤
      (multivariateGaussian 0 S).real {x | K<B x}+8*(S^2).trace/S.trace^2 := by
  obtain ⟨b,v,hv,he⟩ := eigenbasis_exists S hS
  have h := synthesis_law hS hv he
  obtain ⟨t,t2⟩ := trace_identities he
  let A := {x : E ι | 2*Λ*K*‖x‖^2<‖d x‖^2*S.trace}
  let C := {x : E ι | K<B x}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) (by fun_prop)
  have hC : MeasurableSet C := measurableSet_lt measurable_const hB
  have transfer (U : Set (E ι)) (hU : MeasurableSet U) :
      (multivariateGaussian 0 S).real U=(law ι).real (synth b v ⁻¹' U) :=
    congrArg ENNReal.toReal (h.measure_preimage hU.nullMeasurableSet).symm
  change (multivariateGaussian 0 S).real A≤(multivariateGaussian 0 S).real C+_
  rw [transfer A hA,transfer C hC,t,t2]
  have pre : synth b v ⁻¹' A={z | 2*Λ*K*energy v z<‖d (synth b v z)‖^2*∑ i,v i} := by
    ext z;simp only [A,Set.mem_preimage,Set.mem_ofPred_eq,norm_synth b v hv,t]
  rw [pre]
  exact GaussianTraceBudget.relative_tail v (t ▸ ht) (fun z => B (synth b v z))
    (fun z => ‖d (synth b v z)‖^2) hΛ hK (fun z => metric (synth b v z))

omit [DecidableEq ι] in
/-- Physical squared norm of a displacement is at most the largest eigenvalue times the
squared norm after covariance whitening. All coordinates are in the supplied eigenbasis. -/
theorem displacement_metric (b : OrthonormalBasis ι ℝ (E ι)) (v : ι→ℝ)
    (hv : ∀ i,0<v i) {Λ : ℝ} (hΛ : ∀ i,v i≤Λ) (d : E ι) :
    ‖d‖^2≤Λ*∑ i,(b.repr d i)^2/v i := by
  rw [←b.repr.norm_map d,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum;intro i _
  have eqn : (b.repr d i)^2=v i*((b.repr d i)^2/v i) := by field_simp [(hv i).ne']
  exact eqn.le.trans (mul_le_mul_of_nonneg_right (hΛ i) (div_nonneg (sq_nonneg _) (hv i).le))

/-- Squared covariance-whitened norm, expressed in an orthonormal eigendecomposition. -/
def whitenedSq {S : Matrix ι ι ℝ} (hS : S.IsHermitian) (x : E ι) :=
  ∑ i,(hS.eigenvectorBasis.repr x i)^2/hS.eigenvalues i

/-- Equation (5) for varying dimensions and arbitrary positive-definite covariances. The
probabilities use the actual multivariate Gaussian in physical coordinates. The displacement
is any measurable function of the initialization; no independence is assumed. -/
theorem relative_in_probability {I : ℕ→Type*} [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
    (S : ∀ n,Matrix (I n) (I n) ℝ) (hs : ∀ n,(S n).PosDef)
    (d : ∀ n,E (I n)→E (I n)) (hd : ∀ n,Measurable (d n)) (Λ : ℕ→ℝ)
    (hΛ : ∀ n i,(hs n).1.eigenvalues i≤Λ n) (hΛ₀ : ∀ n,0≤Λ n)
    (ht : ∀ n,0<(S n).trace)
    (small : Filter.Tendsto (fun n => ((S n)^2).trace/(S n).trace^2) Filter.atTop (nhds 0))
    (tight : ∀ e>0,∃ K : ℝ,0≤K ∧ ∀ᶠ n in Filter.atTop,
      (multivariateGaussian 0 (S n)).real {x | K<whitenedSq (hs n).1 (d n x)}≤e) :
    ∀ e>0,∃ C : ℝ,0≤C ∧ ∀ᶠ n in Filter.atTop,
      (multivariateGaussian 0 (S n)).real {x | C*sqrt (Λ n/(S n).trace)<‖d n x‖/‖x‖}≤e := by
  intro e he
  obtain ⟨K,hK,hb⟩ := tight (e/2) (half_pos he)
  refine ⟨sqrt (2*K),sqrt_nonneg _,?_⟩
  filter_upwards [hb,small.eventually (gt_mem_nhds (show 0<e/16 by positivity))] with n hB hS
  have hmeas : Measurable (fun x => whitenedSq (hs n).1 (d n x)) := by
    unfold whitenedSq
    apply Finset.measurable_fun_sum
    intro i _
    exact (((PiLp.continuous_apply 2 _ i).measurable.comp
      ((hs n).1.eigenvectorBasis.repr.continuous.measurable.comp (hd n))).pow_const 2).div_const _
  have bound := relative_tail (S n) (hs n).posSemidef (ht n) (d n) _ (hd n) hmeas
    (hΛ₀ n) hK (fun x => displacement_metric _ _ (hs n).eigenvalues_pos (hΛ n) (d n x))
  have sub : {x | sqrt (2*K)*sqrt (Λ n/(S n).trace)<‖d n x‖/‖x‖} ⊆
      {x | 2*Λ n*K*‖x‖^2<‖d n x‖^2*(S n).trace} := by
    intro x hx
    change sqrt (2*K)*sqrt (Λ n/(S n).trace)<‖d n x‖/‖x‖ at hx
    have non := mul_nonneg (sqrt_nonneg (2*K)) (sqrt_nonneg (Λ n/(S n).trace))
    have nz : 0<‖x‖ := by
      by_contra! h
      rw [le_antisymm h (norm_nonneg _),div_zero] at hx
      exact (not_lt_of_ge non hx)
    have hh := (sq_lt_sq₀ (mul_nonneg non nz.le) (norm_nonneg _)).2 ((lt_div_iff₀ nz).mp hx)
    rw [mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt (div_nonneg (hΛ₀ n) (ht n).le)] at hh
    have eqn : 2*K*(Λ n/(S n).trace)*‖x‖^2=(2*Λ n*K*‖x‖^2)/(S n).trace := by ring
    rw [eqn] at hh
    exact (div_lt_iff₀ (ht n)).mp hh
  apply (measureReal_mono sub).trans (bound.trans ?_)
  change ((S n)^2).trace/(S n).trace^2<e/16 at hS
  rw [mul_div_assoc]
  linarith

end GaussianSpectralBudget
