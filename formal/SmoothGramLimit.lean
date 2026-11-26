module

public import SmoothSeedLaw
public import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! The empirical Gram of ordinary all-layer training converges to its
population operator under the iid Gaussian initialization. -/
@[expose] public section
noncomputable section
namespace SmoothGramLimit
open SmoothSeedLaw TwoLayerNetwork TwoLayerBudget MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProduct NNReal Topology
variable {n d k : ℕ}

def gramOp (D : Matrix (Fin k) (Fin k) ℝ) := Matrix.toEuclideanCLM (𝕜:=ℝ) D

def jac (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z : Params n d) :=
  matrixOp (rows φ b x z (smoothSlopes g b x z))

def gram (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z : Params n d) :=
  (jac φ g b x z).comp ((jac φ g b x z)†)

def empirical (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (n : ℕ) (ω : Draws d) :
    Matrix (Fin k) (Fin k) ℝ := fun j l => (∑ i : Fin n, atomEntry φ g b x j l (ω i))/n

theorem gram_rows (r : Fin k → Params n d) :
    (matrixOp r).comp ((matrixOp r)†) = gramOp (fun j l => inner ℝ (r j) (r l)/n) := by
  ext v j
  change (∑ p, r j p/Real.sqrt n*(((matrixOp r)†) v) p) = ∑ l, (inner ℝ (r j) (r l)/n)*v l
  simp_rw [transpose_apply,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro l _
  rw [PiLp.inner_apply,Finset.sum_div,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro p _
  change _ = (r l p*r j p/n)*v l
  rw [div_mul_div_comm,←sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

theorem raw_pair (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d)
    (ω : Draws d) (j l : Fin k) :
    let z := packed n ω
    let r := rows φ b x z (smoothSlopes g b x z)
    inner ℝ (r j) (r l) = ∑ i : Fin n, atomEntry φ g b x j l (ω i) := by
  intro z r
  rw [PiLp.inner_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [Fin.sum_univ_succ]
  change H φ (b l) (x l) (ω i).2 * H φ (b j) (x j) (ω i).2 + _ = _
  unfold atomEntry
  rw [mul_comm (H φ (b l) (x l) (ω i).2)]
  congr 1
  rw [PiLp.inner_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro t _
  change (b l*((ω i).1*H g (b l) (x l) (ω i).2)*x l t)*
    (b j*((ω i).1*H g (b j) (x j) (ω i).2)*x j t) = _
  simp only [Real.inner_apply];ring

theorem empirical_gram (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d)
    (n : ℕ) (ω : Draws d) : gram φ g b x (packed n ω) = gramOp (empirical φ g b x n ω) := by
  unfold gram jac
  rw [gram_rows]
  apply congrArg gramOp
  ext j l
  rw [raw_pair];rfl

theorem atom_cont {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (j l : Fin k) : Continuous (atomEntry φ g b x j l) := by
  have f : Continuous φ := continuous_iff_continuousAt.mpr fun z => (h.first z).continuousAt
  have gg := g_continuous h
  unfold atomEntry H
  fun_prop

theorem gramOp_continuous : Continuous (gramOp (k:=k)) :=
  (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin k)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

/-- Strong convergence in operator norm on one common iid realization. -/
theorem gaussian_gram_lln {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : ∀ᵐ ω ∂law d,
      Tendsto (fun n : ℕ => gram φ g b x (packed n ω)) atTop (𝓝 (gramOp (Γmat φ g b x))) := by
  have entry (j l : Fin k) : ∀ᵐ ω ∂law d, Tendsto (fun n => empirical φ g b x n ω j l) atTop
      (𝓝 (Γmat φ g b x j l)) := by
    have e := atom_integral h b x j l
    have p := observable_lln (atomEntry φ g b x j l) (atom_cont h b x j l).measurable e.1
    rw [e.2] at p
    filter_upwards [p] with ω hω
    apply hω.congr;intro n
    rw [empirical,Fin.sum_univ_eq_sum_range (fun i : ℕ => atomEntry φ g b x j l (ω i)) n]
    change _*_= _;ring
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (entry j))] with ω hω
  have mm : Tendsto (fun n => empirical φ g b x n ω) atTop (𝓝 (Γmat φ g b x)) :=
    tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun l => hω j l
  exact (gramOp_continuous.continuousAt.tendsto.comp mm).congr (fun n => (empirical_gram φ g b x n ω).symm)


theorem gram_measurable {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (n : ℕ) :
    Measurable (fun ω : Draws d => gram φ g b x (packed n ω)) := by
  simp_rw [empirical_gram]
  apply gramOp_continuous.measurable.comp
  apply Measurable.of_eval; intro j
  apply Measurable.of_eval; intro l
  unfold empirical
  exact (Finset.measurable_fun_sum Finset.univ (fun (i : Fin n) _ => (atom_cont h b x j l).measurable.comp (measurable_pi_apply (i:ℕ)))).div_const n

theorem gram_law {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) :
    TendstoInMeasure (law d) (fun n ω => gram φ g b x (packed n ω)) atTop (fun _ => gramOp (Γmat φ g b x)) :=
  tendstoInMeasure_of_tendsto_ae (fun n => (gram_measurable h b x n).aestronglyMeasurable) (gaussian_gram_lln h b x)

def initPred (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (n : ℕ) (ω : Draws d) : Space k :=
  (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, signal φ b x (ω i)

theorem initPred_coord (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (n : ℕ)
    (ω : Draws d) (j : Fin k) : initPred φ b x n ω j =
        (∑ i : Fin n, signal φ b x (ω i) j)/Real.sqrt n := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => signal φ b x (ω i) j) n]
  change (EuclideanSpace.proj j : Space k →L[ℝ] ℝ) ((Real.sqrt n)⁻¹ • _) = _
  rw [map_smul,map_sum];simp only [smul_eq_mul,EuclideanSpace.coe_proj];ring

theorem initial_residual (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (n : ℕ) (ω : Draws d) :
    residual φ b x y (packed n ω) 0 = initPred φ b x n ω-y := by
  ext j; change _ = initPred φ b x n ω j-y j
  rw [initPred_coord]
  simp [TwoLayerNetwork.residual,pred,signal,H]

theorem initPred_second {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (n : ℕ) (hn : 0<n) (j : Fin k) :
    let f := fun ω => initPred φ b x n ω j
    MemLp f 2 (law d) ∧ ∫ ω, f ω^2 ∂law d = Cmat φ b x j j := by
  intro f
  let Y := fun t => signal φ b x t j
  let V := fun i (ω : Draws d) => Y (ω i)
  have ymem : MemLp Y 2 (neuronLaw d) := (signal_mem h b x).eval_piLp j
  have ym : Measurable Y := ((EuclideanSpace.proj j : Space k →L[ℝ] ℝ).continuous.comp (signal_cont h b x)).measurable
  have vi (i : ℕ) : MemLp (V i) 2 (law d) := (eval_law i).memLp_comp ymem
  have μ (i : ℕ) : ∫ ω, V i ω ∂law d=0 :=
    ((eval_law i).integral_comp ymem.aestronglyMeasurable).trans (signal_mean φ b x j)
  have vv (i : ℕ) : ∫ ω, V i ω*V i ω ∂law d=Cmat φ b x j j := ((eval_law i).integral_comp
    (f:=fun t => Y t*Y t) (ym.mul ym).aestronglyMeasurable).trans (signal_second φ b x j j)
  have cross (i l : ℕ) (neq : i≠l) : ∫ ω, V i ω*V l ω ∂law d=0 := by
    have ind : IndepFun (V i) (V l) (law d) := (iid_observable Y ym).1.indepFun neq
    rw [ind.integral_fun_mul_eq_mul_integral (vi i).aestronglyMeasurable (vi l).aestronglyMeasurable,μ i,zero_mul]
  have sf (ω) : f ω=(∑ i : Fin n, V i ω)/Real.sqrt n := initPred_coord φ b x n ω j
  have req : f = fun ω => (∑ i : Fin n, V i ω)/Real.sqrt n := funext sf
  rw [req]
  constructor
  · simpa only [div_eq_mul_inv] using (memLp_finsetSum Finset.univ (fun (i : Fin n) _ => vi i)).mul_const (Real.sqrt n)⁻¹
  · have expan (ω) : ((∑ i : Fin n, V i ω)/Real.sqrt n)^2 = (∑ i : Fin n, ∑ l : Fin n, V i ω*V l ω)/n := by
      rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _),sq,Finset.sum_mul];simp_rw [Finset.mul_sum]
    simp_rw [expan]
    have ii (i l : Fin n) : Integrable (fun ω => V i ω*V l ω) (law d) := (vi i).integrable_mul (vi l)
    rw [integral_div,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => ii i l))]
    simp_rw [integral_finsetSum _ (fun l _ => ii _ l)]
    have row (i : Fin n) : ∑ l : Fin n, (∫ ω, V i ω*V l ω ∂law d) = Cmat φ b x j j := by
      rw [Finset.sum_eq_single i]
      · exact vv i
      · intro l _ neq;exact cross i l (fun h => neq (Fin.ext h.symm))
      · simp
    simp_rw [row];simp [ne_of_gt hn]

theorem residual_tail {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k) (n : ℕ) (hn : 0<n) {v : ℝ} (vp : 0<v) :
    (law d).real {ω | v ≤ ‖residual φ b x y (packed n ω) 0‖^2} ≤
      (2*(∑ j, Cmat φ b x j j)+2*‖y‖^2)/v := by
  let G := fun ω : Draws d => ∑ j, (2*(initPred φ b x n ω j)^2+2*(y j)^2)
  have m (j) := initPred_second h b x n hn j
  have fi (j) := (memLp_two_iff_integrable_sq (m j).1.aestronglyMeasurable).mp (m j).1
  have rI (j) : Integrable (fun ω => 2*(initPred φ b x n ω j)^2+2*(y j)^2) (law d) :=
    ((fi j).const_mul _).add (integrable_const _)
  have gi : Integrable G (law d) := integrable_finsetSum _ (fun j _ => rI j)
  have point (ω : Draws d) : ‖residual φ b x y (packed n ω) 0‖^2 ≤ G ω := by
    rw [initial_residual,EuclideanSpace.real_norm_sq_eq];apply Finset.sum_le_sum;intro j _
    change (initPred φ b x n ω j-y j)^2 ≤ _; nlinarith [sq_nonneg (initPred φ b x n ω j+y j)]
  have mean : ∫ ω, G ω ∂law d=2*(∑ j, Cmat φ b x j j)+2*‖y‖^2 := by
    rw [show G=_ from rfl,integral_finsetSum _ (fun j _ => rI j),EuclideanSpace.real_norm_sq_eq]
    simp_rw [integral_add ((fi _).const_mul _) (integrable_const _),integral_const_mul,
      integral_const,probReal_univ,one_smul,(m _).2]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  apply (measureReal_mono (fun ω hω => le_trans hω (point ω))).trans
  apply (le_div_iff₀ vp).mpr
  rw [mul_comm,←mean]
  exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun ω => (sq_nonneg _).trans (point ω))) gi v

end SmoothGramLimit
