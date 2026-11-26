module

public import PhysicalTangentLaw
public import PhysicalInitialization
import all PhysicalInitialization
import all SmoothGramLimit
import all SmoothSeedLaw
import all TwoLayerNetwork
import all TwoLayerBudget
import Mathlib.Tactic

/-! Physical hidden displacement for a single-example tangent interpolation
step. Both sides use the same initialized neurons and the actual Jacobian. -/
public section
noncomputable section
namespace PhysicalTangentIdentity
open Real TwoLayerNetwork TwoLayerBudget SmoothSeedLaw PhysicalTangentLaw SmoothGramLimit
open scoped InnerProduct

variable {n d : ℕ}
private abbrev constRow {X : Type*} (x : X) := fun _ : Fin 1 => x

theorem initial_coord (α b : ℝ) (x : Space d) (n : ℕ) (ω : Draws d) :
    residual (leaky α) (fun _ : Fin 1 => b) (fun _ => x) 0 (packed n ω) 0 0 =
      initial α b x n ω := by
  rw [initial_residual,sub_zero,initPred_coord]
  change (∑ i : Fin n, signalAtom α b x (ω i))/sqrt n=_
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => signalAtom α b x (ω i)) n];rfl

/-- On the one-dimensional training space the full empirical Gram acts by
multiplication by the scalar empirical tangent kernel. -/
theorem gram_coord (α b : ℝ) (x : Space d) (hx : ‖x‖=1) (n : ℕ) (ω : Draws d) (v : Space 1) :
    let A := jac (leaky α) (slope α) (fun _ : Fin 1 => b) (fun _ => x) (packed n ω)
    A ((A†) v) 0 = kernel α b x n ω * v 0 := by
  intro A
  change gram (leaky α) (slope α) (constRow b) (constRow x) (packed n ω) v 0=_
  rw [empirical_gram]
  change (∑ j : Fin 1, empirical (leaky α) (slope α) (constRow b) (constRow x) n ω 0 j * v j)=_
  rw [Fin.sum_univ_one]
  apply congrArg (·*v 0)
  have e (i : ℕ) : atomEntry (leaky α) (slope α) (constRow b) (constRow x) 0 0 (ω i) =
      featureSq α b x (ω i)+b^2*gateSq α b x (ω i) := by
    simp only [atomEntry,constRow,real_inner_self_eq_norm_sq,hx,one_pow,mul_one,
      H,featureSq,gateSq,feature,derivFeature];ring
  simp only [empirical,e]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => featureSq α b x (ω i)+b^2*gateSq α b x (ω i)) n,
    Finset.sum_add_distrib,←Finset.mul_sum,kernel,average,average];ring

theorem hidden_adjoint (α b : ℝ) (x : Space d) (hx : ‖x‖=1) (n : ℕ) (ω : Draws d) (v : Space 1) :
    let A := jac (leaky α) (slope α) (fun _ : Fin 1 => b) (fun _ => x) (packed n ω)
    PhysicalInitialization.hiddenNorm ((A†) v) = |v 0| *sqrt ((b^2/(d:ℝ))*average (gateSq α b x) n ω) := by
  intro A
  have gate_non : 0≤average (gateSq α b x) n ω := by unfold average gateSq;positivity
  let c (i : Fin n) := (b*((ω i).1*derivFeature α b x (ω i).2)/sqrt n)*(v 0)
  have block (i : Fin n) : TwoLayerNetwork.hidden ((A†) v) i=c i • x := by
    ext j
    change ((matrixOp _)†) v (i,j.succ) = (c i)*(x j)
    rw [transpose_apply,Fin.sum_univ_one]
    change v 0*((b*((ω i).1*derivFeature α b x (ω i).2))*x j)/sqrt n=_
    dsimp only [c];ring
  unfold PhysicalInitialization.hiddenNorm
  apply (sq_eq_sq₀ (sqrt_nonneg _) (mul_nonneg (abs_nonneg _) (sqrt_nonneg _))).mp
  rw [sq_sqrt (by positivity),mul_pow,sq_abs,sq_sqrt (by positivity)]
  simp_rw [block,norm_smul,hx,mul_one,Real.norm_eq_abs,sq_abs]
  unfold average
  rw [←Fin.sum_univ_eq_sum_range (fun i : ℕ => gateSq α b x (ω i)) n]
  rw [show (v 0)^2*(b^2/(d:ℝ)*((∑ i : Fin n,gateSq α b x (ω i))/(n:ℝ))) =
    ((v 0)^2*b^2/(d:ℝ)/(n:ℝ))*(∑ i : Fin n,gateSq α b x (ω i)) by ring,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  simp only [c,gateSq,mul_pow,div_pow,sq_sqrt (Nat.cast_nonneg n)];ring

/-- The norm of the physical hidden block of the least-norm tangent step
is exactly the statistic whose limit is the scaled absolute Gaussian. -/
theorem identity (α b : ℝ) (x : Space d) (hx : ‖x‖=1) (n : ℕ) (ω : Draws d)
    (K : Space 1 ≃L[ℝ] Space 1) :
    let A := jac (leaky α) (slope α) (fun _ : Fin 1 => b) (fun _ => x) (packed n ω)
    let F := residual (leaky α) (fun _ : Fin 1 => b) (fun _ => x) 0 (packed n ω)
    (∀ v, K v=A ((A†) v)) →
      PhysicalInitialization.hiddenNorm ((A†) (K.symm (-F 0)))=tangentNorm α b x n ω := by
  intro A F hK
  let κ := kernel α b x n ω
  have gram' (v : Space 1) : (K v) 0=κ*v 0 := by rw [hK];exact gram_coord α b x hx n ω v
  have non : 0≤κ := by unfold κ kernel average featureSq gateSq;positivity
  have nz : κ≠0 := by
    let e : Space 1 := WithLp.toLp 2 (fun _ => (1:ℝ))
    have h := gram' (K.symm e)
    rw [K.apply_symm_apply] at h
    change 1=κ*_ at h
    intro h0;rw [h0,zero_mul] at h;norm_num at h
  let v := K.symm (-F 0)
  have scalar : v 0=-initial α b x n ω/κ := by
    have h := gram' v
    change (K (K.symm (-F 0))) 0=κ*v 0 at h
    rw [K.apply_symm_apply] at h
    change -(F 0 0)=κ*v 0 at h
    change -(residual (leaky α) (constRow b) (constRow x) 0 (packed n ω) 0 0)=_ at h
    rw [initial_coord] at h
    exact (eq_div_iff nz).mpr ((mul_comm _ _).trans h.symm)
  change PhysicalInitialization.hiddenNorm ((A†) v)=_
  rw [hidden_adjoint α b x hx n ω v,scalar,abs_div,abs_neg,abs_of_nonneg non]
  unfold tangentNorm factor;dsimp [κ];ring

end PhysicalTangentIdentity
