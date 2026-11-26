module

public import SmoothTrainingLimit
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic

/-! Cramér–Wold limit of the actual finite-width Gaussian initialization,
with the possibly singular feature covariance. -/
@[expose] public section
noncomputable section
namespace SmoothGaussianLaw
open SmoothSeedLaw SmoothGramLimit TwoLayerNetwork Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped NNReal InnerProduct Topology Matrix
variable {d k : ℕ}

theorem signal_mean_vector {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : ∫ t, signal φ b x t ∂neuronLaw d = 0 := by
  ext i
  change (EuclideanSpace.proj i : Space k →L[ℝ] ℝ) (∫ t, signal φ b x t ∂neuronLaw d)=0
  rw [← ContinuousLinearMap.integral_comp_comm _ ((signal_mem h b x).integrable (by norm_num))]
  exact signal_mean φ b x i

theorem quadratic_variance {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (v : Space k) :
    Var[fun t => inner ℝ v (signal φ b x t);neuronLaw d] = v.ofLp ⬝ᵥ (Cmat φ b x *ᵥ v.ofLp) := by
  let s := signal φ b x
  let μ := neuronLaw d
  have m : MemLp s 2 μ := signal_mem h b x
  have rc (i j : Fin k) : cov[fun t => s t i,fun t => s t j;μ]=Cmat φ b x i j := by
    rw [covariance_eq_sub (m.eval_piLp i) (m.eval_piLp j)]
    change (∫ t, s t i*s t j ∂μ)-(∫ t, s t i ∂μ)*(∫ t, s t j ∂μ)=_
    rw [signal_mean φ b x i,zero_mul,sub_zero]
    exact signal_second φ b x i j
  have pm : MemLp id 2 (μ.map s) := (memLp_map_measure_iff aestronglyMeasurable_id m.aemeasurable).mpr m
  have eq : covarianceBilin (μ.map s) v v = Var[fun t => inner ℝ v (s t);μ] := by
    rw [covarianceBilin_apply_eq_cov pm,covariance_self (by fun_prop),variance_map]
    · rfl
    · fun_prop
    · exact m.aemeasurable
  rw [← eq]
  have p := covarianceBilin_apply_pi (X:=fun i t => s t i) (fun i => m.eval_piLp i) v v
  change covarianceBilin (μ.map s) v v = _ at p
  rw [p];simp_rw [rc]
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring

theorem covariance_psd {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : (Cmat φ b x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    change Cmat φ b x j i = Cmat φ b x i j
    simp [Cmat,mul_comm]
  · intro v
    simpa only [star_trivial] using (variance_nonneg (fun t => inner ℝ (WithLp.toLp 2 v : Space k) (signal φ b x t))
      (neuronLaw d)).trans_eq (quadratic_variance h b x (WithLp.toLp 2 v))

theorem projection_law {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (v : Space k) :
    let Y := fun ω : Draws d => inner ℝ v (signal φ b x (ω 0))
    HasLaw (innerSL ℝ v) (gaussianReal 0 (Var[Y;law d]).toNNReal)
      (multivariateGaussian 0 (Cmat φ b x)) := by
  intro Y
  let ν := multivariateGaussian (0:Space k) (Cmat φ b x)
  let L := innerSL ℝ v
  have hs := covariance_psd h b x
  have var' : Var[L;ν] = v.ofLp ⬝ᵥ (Cmat φ b x *ᵥ v.ofLp) := by
    have e := covarianceBilin_apply_eq_cov (μ:=ν) IsGaussian.memLp_two_id v v
    rw [covariance_self (by fun_prop)] at e
    exact e.symm.trans (covarianceBilin_multivariateGaussian hs v v)
  have m : ν[L]=0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id]
    dsimp only [ν]; rw [integral_id_multivariateGaussian,map_zero]
  have vy : Var[Y;law d] = Var[fun t => inner ℝ v (signal φ b x t);neuronLaw d] := by
    have l := eval_law (d:=d) 0
    let f := fun t : Neuron d => inner ℝ v (signal φ b x t)
    have c : Continuous f := (innerSL ℝ v).continuous.comp (signal_cont h b x)
    change Var[f ∘ (fun ω : Draws d => ω 0);law d]=Var[f;neuronLaw d]
    rw [←l.map_eq,variance_map c.aemeasurable l.aemeasurable]
  refine ⟨by fun_prop,?_⟩
  change ν.map L=_
  rw [IsGaussian.map_eq_gaussianReal,m,var',vy,quadratic_variance h b x]

/-- Initial predictions converge in distribution to the centered Gaussian
with covariance C, including C with a nontrivial null space. -/
theorem prediction_clt {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) :
    TendstoInDistribution (initPred φ b x) atTop (fun z : Space k => z)
      (fun _ => law d) (multivariateGaussian 0 (Cmat φ b x)) := by
  have hc := signal_cont h b x
  have meas (n : ℕ) : Measurable (initPred φ b x n) := by
    unfold initPred
    exact (Finset.measurable_fun_sum (Finset.range n) (fun i _ => hc.measurable.comp (measurable_pi_apply i))).const_smul ((Real.sqrt n)⁻¹)
  apply TendstoInDistribution.of_inner (by fun_prop) (fun n => (meas n).aemeasurable)
  intro v
  let L := innerSL ℝ v
  let f := fun t => L (signal φ b x t)
  let X := fun i (ω : Draws d) => f (ω i)
  have m : MemLp f 2 (neuronLaw d) := L.comp_memLp' (signal_mem h b x)
  have μ₀ : ∫ ω, X 0 ω ∂law d=0 := by
    rw [show (∫ ω, X 0 ω ∂law d)=∫ t, f t ∂neuronLaw d from (eval_law 0).integral_comp m.aestronglyMeasurable]
    rw [show (∫ t, f t ∂neuronLaw d)=L (∫ t, signal φ b x t ∂neuronLaw d) from
      L.integral_comp_comm ((signal_mem h b x).integrable (by norm_num)),signal_mean_vector h,map_zero]
  have iid := iid_observable f (L.continuous.comp hc).measurable
  have c := tendstoInDistribution_inv_sqrt_mul_sum_sub (X:=X) (projection_law h b x v)
    ((eval_law 0).memLp_comp m) iid.1 iid.2
  rw [μ₀] at c
  apply c.congr
  · intro n;apply ae_of_all;intro ω
    change (Real.sqrt n)⁻¹*((∑ i ∈ Finset.range n, L (signal φ b x (ω i)))-n*0)=
      inner ℝ (initPred φ b x n ω) v
    rw [real_inner_comm v (initPred _ _ _ _ _),show inner ℝ v (initPred φ b x n ω)= L _ from rfl,
      initPred,map_smul,map_sum];simp
  · exact ae_of_all _ fun z => real_inner_comm z v

end SmoothGaussianLaw
