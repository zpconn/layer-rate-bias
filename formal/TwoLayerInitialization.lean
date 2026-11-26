module

public import TwoLayerNetwork
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-! Finite-width Gaussian events for the actual packed two-layer initialization. -/
@[expose] public section
noncomputable section
namespace TwoLayerInitialization
open TwoLayerNetwork TwoLayerBudget ProbabilityTheory MeasureTheory Set
open scoped InnerProductSpace InnerProduct NNReal
variable {n d k : ℕ}

def liftHidden (i : Fin n) (x : Space d) : Params n d :=
  WithLp.toLp 2 fun p => if p.1 = i then Fin.cases 0 (fun j => x j) p.2 else 0

theorem lift_norm (i : Fin n) (x : Space d) : ‖liftHidden i x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Fin.sum_univ_succ]
    simp [liftHidden]
  · intro j _ hj
    simp [liftHidden,hj]
  · simp

theorem lift_inner (i : Fin n) (x : Space d) (z : Params n d) :
    inner ℝ (liftHidden i x) z = inner ℝ (hidden z i) x := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Fin.sum_univ_succ]
    simp [liftHidden,TwoLayerNetwork.hidden,mul_comm]
  · intro j _ hj
    simp [liftHidden,hj]
  · simp

theorem unit_law (u : Params n d) (h : ‖u‖=1) :
    HasLaw (innerSL ℝ u) (gaussianReal 0 1) (stdGaussian (Params n d)) := by
  refine ⟨by fun_prop,?_⟩
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,h]; simp

theorem preactivation_law (i : Fin n) (x : Space d) (hx : ‖x‖=1) :
    HasLaw (fun z : Params n d => inner ℝ (hidden z i) x) (gaussianReal 0 1)
      (stdGaussian (Params n d)) := by
  exact (show (fun z : Params n d => inner ℝ (hidden z i) x) = innerSL ℝ (liftHidden i x) by
    funext z; exact (lift_inner i x z).symm) ▸ unit_law (liftHidden i x) ((lift_norm i x).trans hx)

theorem readout_law (i : Fin n) :
    HasLaw (fun z : Params n d => readout z i) (gaussianReal 0 1) (stdGaussian (Params n d)) := by
  let u : Params n d := EuclideanSpace.single (i,0) (1:ℝ)
  have un : ‖u‖=1 := by simp [u]
  have eq : (fun z : Params n d => readout z i) = innerSL ℝ u := by
    ext z; simp [u,readout,EuclideanSpace.inner_single_left]
  rw [eq]
  exact unit_law _ un

/-- Joint failure probability for the initial readout and all fixed training
directions. The bound allows arbitrary dependence among the input directions. -/
theorem bad_seed (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) (M ε A : ℝ)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hA : 0 < A) :
    (stdGaussian (Params n d)).real {z |
      (∃ i, M ≤ |readout z i|) ∨
      ∃ j, A ≤ ((Finset.univ.filter (fun i => |inner ℝ (hidden z i) (x j)| ≤ ε)).card:ℝ)} ≤
      2*n*Real.exp (-M^2/2) + k*(2*n*ε/A) := by
  let μ := stdGaussian (Params n d)
  let B := fun j => {z : Params n d |
    A ≤ ((Finset.univ.filter (fun i => |inner ℝ (hidden z i) (x j)| ≤ ε)).card:ℝ)}
  have p (j) : μ.real (B j) ≤ 2*n*ε/A :=
    gaussian_near_count μ _ (fun i => preactivation_law i (x j) (hx j)) ε A hε hA
  have P : μ.real (⋃ j, B j) ≤ k*(2*n*ε/A) := by
    apply (measureReal_iUnion_fintype_le _).trans
    exact (Finset.sum_le_sum (s := Finset.univ) (fun j _ => p j)).trans_eq (by simp)
  have Q := gaussian_max μ (fun i z => readout z i) (fun i => readout_law i) M hM
  have eq : {z : Params n d | (∃ i, M ≤ |readout z i|) ∨ ∃ j, z ∈ B j} =
      {z | ∃ i, M ≤ |readout z i|} ∪ ⋃ j, B j := by ext z; simp
  change μ.real {z | (∃ i, M ≤ |readout z i|) ∨ ∃ j, z ∈ B j} ≤ _
  rw [eq]
  exact (measureReal_union_le _ _).trans (add_le_add Q P)


/-- Fixed-confidence form of the finite Gaussian estimates. At width n=u³,
M²=2 log(4n/p) controls every readout and 4ku²/p controls every near count. -/
theorem fixed_confidence (hn : 0<n) (hk : 0<k) (u p : ℝ) (up : 0<u) (width : (n:ℝ)=u^3)
    (hp : 0<p) (p1 : p≤1) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) :
    let M := Real.sqrt (2*Real.log (4*n/p))
    let A := 4*k*u^2/p
    (stdGaussian (Params n d)).real {z |
      (∃ i, M ≤ |readout z i|) ∨ ∃ j, A ≤
        ((Finset.univ.filter (fun i => |inner ℝ (hidden z i) (x j)| ≤ 1/u)).card:ℝ)} ≤ p := by
  intro M A
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have one : 1 ≤ (4*n/p:ℝ) := by
    apply (le_div_iff₀ hp).mpr
    have n1 : 1≤(n:ℝ) := by exact_mod_cast hn
    linarith
  have msq : M^2 = 2*Real.log (4*n/p) := Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg one))
  have ap : 0<A := by dsimp [A]; positivity
  apply (bad_seed x hx M (1/u) A (Real.sqrt_nonneg _) (by positivity) ap).trans_eq
  rw [msq,show -(2*Real.log (4*n/p))/2 = -Real.log (4*n/p) by ring,
    Real.exp_neg,Real.exp_log (by positivity)]
  dsimp [A]
  field_simp
  rw [width]
  ring

/-- At the same cutoff, the squared operator tolerance is controlled by
R²/n plus a term of order M²/u. The bound is uniform over the parameter ball. -/
theorem leaky_rate_mass (u : ℝ) (up : 0<u) (width : (n:ℝ)=u^3)
    (R M α C : ℝ) (b : Fin k → ℝ) (near : Fin k → ℕ) (h : ∀ j, (near j:ℝ) ≤ C*u^2) :
    (∑ j, 2*(b j)^2*(R^2+M^2*(1-α)^2*((near j:ℝ)+R^2/(1/u)^2))) ≤
      (n:ℝ)*(2*(∑ j, (b j)^2)*(R^2/n+M^2*(1-α)^2*((C+R^2)/u))) := by
  rw [width]
  have e : R^2/(1/u)^2 = R^2*u^2 := by field_simp
  simp_rw [e]
  calc
    _ ≤ ∑ j, 2*(b j)^2*(R^2+M^2*(1-α)^2*(C*u^2+R^2*u^2)) := by
      apply Finset.sum_le_sum; intro j _; gcongr; exact h j
    _ = _ := by simp only [← Finset.sum_mul,← Finset.mul_sum]; field_simp


/-- A width-uniform small lower tail for the initial readout energy. This
short proof uses the Gaussian marginal small-ball bound at a fixed cutoff. -/
theorem readout_energy_lower (hn : 0<n) (ε : ℝ) (he : 0<ε) :
    (stdGaussian (Params n d)).real {z | (∑ i, (readout z i)^2)/n ≤ ε^2/2} ≤ 4*ε := by
  let μ := stdGaussian (Params n d)
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have P := gaussian_near_count μ (fun i z => readout z i) (fun i => readout_law i)
    ε ((n:ℝ)/2) he.le (by positivity)
  apply (measureReal_mono (s₂ := {z : Params n d | (n:ℝ)/2 ≤
    ((Finset.univ.filter (fun i => |readout z i| ≤ ε)).card:ℝ)}) ?_).trans (P.trans_eq (by field_simp; ring))
  intro z hz
  let near := Finset.univ.filter (fun i => |readout z i| ≤ ε)
  let far := Finset.univ.filter (fun i => ¬ |readout z i| ≤ ε)
  have partition : (near.card:ℝ)+(far.card:ℝ) = n := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => |readout z i| ≤ ε)).trans (Fintype.card_fin n)
  have total : (far.card:ℝ)*ε^2 ≤ ∑ i, (readout z i)^2 := by
    calc _ = ∑ _i ∈ far, ε^2 := by simp
         _ ≤ ∑ i ∈ far, (readout z i)^2 := by
           apply Finset.sum_le_sum; intro i hi
           have h := lt_of_not_ge (Finset.mem_filter.mp hi).2
           simpa only [sq_abs] using pow_le_pow_left₀ he.le h.le 2
         _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have b := (div_le_iff₀ np).mp hz
  change _ ≤ (near.card:ℝ)
  nlinarith [sq_pos_of_pos he]

/-- Positive definiteness of the concrete empirical Gram with arbitrary
confidence, uniformly in width. The lower frame bound is on the fixed data. -/
theorem gram_conditioning (hn : 0<n) (α ell ε : ℝ) (hα : 0≤α) (he : 0≤ell) (ep : 0<ε)
    (b : Fin k → ℝ) (x : Fin k → Space d)
    (frame : ∀ y : Space k, ell*‖y‖^2 ≤ ‖∑ j, (y j*b j) • x j‖^2)
    (s : Params n d → Fin k → Fin n → ℝ) (g : ∀ z, gate α b x z (s z)) :
    (stdGaussian (Params n d)).real {z | ∃ u : Space k,
      ‖((matrixOp (rows (leaky α) b x z (s z)))†) u‖^2 < ell*α^2*(ε^2/2)*‖u‖^2} ≤ 4*ε := by
  apply (measureReal_mono ?_).trans (readout_energy_lower (d:=d) hn ε ep)
  rintro z ⟨u,h⟩
  change (∑ i, (readout z i)^2)/n ≤ ε^2/2
  by_contra! bad
  have h0 := leaky_gram_lower α ell hα he b x frame z (s z) (g z) u
  have a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bad.le (mul_nonneg he (sq_nonneg α))) (sq_nonneg ‖u‖)
  exact (not_lt_of_ge (a.trans h0)) h

end TwoLayerInitialization
