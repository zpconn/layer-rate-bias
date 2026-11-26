module

public import Movement
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-! Finite-dimensional linearized gradient descent, including inconsistent targets
and singular Gram matrices. -/
@[expose] public section
noncomputable section
namespace LinearLeastSquares
open Real Filter ContinuousLinearMap Submodule
open scoped InnerProductSpace Topology
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
local instance : CompleteSpace H := FiniteDimensional.complete ℝ H

/-- First project the target onto the range, then take the unique inverse
image orthogonal to the kernel. -/
def pinv (A : E →L[ℝ] H) : H →L[ℝ] E :=
  (A.kerᗮ.subtype.comp (A.ker.quotientEquivOrthogonal.toLinearEquiv.toLinearMap.comp
    (A.toLinearMap.quotKerEquivRange.symm.toLinearMap.comp A.range.orthogonalProjectionOnto.toLinearMap))).toContinuousLinearMap

theorem pinv_mem (A : E →L[ℝ] H) (y : H) : pinv A y∈A.kerᗮ :=
  (A.ker.quotientEquivOrthogonal (A.toLinearMap.quotKerEquivRange.symm (A.range.orthogonalProjectionOnto y))).property

theorem apply_pinv (A : E →L[ℝ] H) (y : H) : A (pinv A y)=A.range.starProjection y := by
  let q := A.toLinearMap.quotKerEquivRange.symm (A.range.orthogonalProjectionOnto y)
  have eq : Submodule.Quotient.mk (pinv A y) = q := by
    have m := A.ker.quotientEquivOrthogonal_symm_eq_mk (pinv A y) (pinv_mem A y)
    have red : (⟨pinv A y,pinv_mem A y⟩ : A.kerᗮ) = A.ker.quotientEquivOrthogonal q := rfl
    rw [red,LinearIsometryEquiv.symm_apply_apply] at m
    exact m.symm
  calc _ = ↑(A.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk (pinv A y))) :=
      (A.toLinearMap.quotKerEquivRange_apply_mk _).symm
       _ = _ := by rw [eq];simp [q]

theorem pinv_apply_on_row (A : E →L[ℝ] H) {x : E} (hx : x∈A.kerᗮ) : pinv A (A x)=x := by
  have proj : A.range.starProjection (A x)=A x := Submodule.starProjection_mem_subspace_eq_self (K:=A.range) ⟨A x,⟨x,rfl⟩⟩
  have kn : pinv A (A x)-x∈A.ker := by
    change A (pinv A (A x)-x)=0
    rw [map_sub,apply_pinv,proj,sub_self]
  have ro := A.kerᗮ.sub_mem (pinv_mem A (A x)) hx
  have inner := (Submodule.mem_orthogonal _ _).mp ro _ kn
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℝ)).mp inner)

theorem pinv_apply (A : E →L[ℝ] H) (x : E) : pinv A (A x)=A.kerᗮ.starProjection x := by
  let s := A.kerᗮ.starProjection x
  have k : x-s∈A.ker := by simpa only [Submodule.orthogonal_orthogonal] using
    (Submodule.sub_starProjection_mem_orthogonal (K:=A.kerᗮ) x)
  have as : A x=A s := sub_eq_zero.mp (by simpa only [map_sub] using (show A (x-s)=0 from k))
  rw [as];exact pinv_apply_on_row A (A.kerᗮ.orthogonalProjectionOnto x).property

/-- The minimum residual norm and the strict uniqueness of its least-norm
parameter representative. -/
theorem minimum_norm (A : E →L[ℝ] H) (y : H) :
    (∀ v, ‖y-A (pinv A y)‖≤‖y-A v‖) ∧
    ∀ v, (∀ z, ‖y-A v‖≤‖y-A z‖) → ‖v‖^2=‖pinv A y‖^2+‖v-pinv A y‖^2 := by
  have ortho : y-A (pinv A y)∈A.rangeᗮ := by rw [apply_pinv];exact sub_starProjection_mem_orthogonal _
  have normal : A.adjoint (y-A (pinv A y))=0 := by rwa [A.orthogonal_range] at ortho
  refine ⟨(A.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero _ _).mpr normal,?_⟩
  intro v best
  have nv := (A.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero _ _).mp best
  have ker : v-pinv A y∈A.ker := by
    rw [←A.ker_adjoint_comp_self]
    change A.adjoint (A (v-pinv A y))=0
    simp only [map_sub] at nv normal ⊢
    abel_nf at nv normal ⊢
    grind
  have iz := (Submodule.mem_orthogonal _ _).mp (pinv_mem A y) _ ker
  have sum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v-pinv A y) (pinv A y) iz
  rw [sub_add_cancel] at sum
  linarith

/-- No rank assumption is used, and the step bound also covers the zero operator. -/
theorem convergence (A : E →L[ℝ] H) (y : H) (h : ℝ) (hp : 0<h) (stable : h*‖A‖^2<2)
    (u : ℕ → E) (zero : u 0=0) (step : ∀ t, u (t+1)=u t+h • A.adjoint (y-A (u t))) :
    Tendsto u atTop (𝓝 (pinv A y)) ∧
    Tendsto (fun t => y-A (u t)) atTop (𝓝 (A.rangeᗮ.starProjection y)) := by
  let r t := y-A (u t)
  let g t := A.adjoint (r t)
  let f t := ‖r t‖^2
  let c := h*(2-h*‖A‖^2)
  have cp : 0<c := mul_pos hp (sub_pos.mpr stable)
  have recurrence (t : ℕ) : r (t+1)=r t-h • A (g t) := by
    change y-A (u (t+1))=(y-A (u t))-h • A (g t)
    rw [step,map_add,map_smul];abel
  have dec (t : ℕ) : c*‖g t‖^2≤f t-f (t+1) := by
    have adj : inner ℝ (r t) (A (g t))=‖g t‖^2 :=
      (A.adjoint_inner_left (g t) (r t)).symm.trans (real_inner_self_eq_norm_sq _)
    have op := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (g t)) 2
    rw [mul_pow] at op
    dsimp only [f,c];rw [recurrence,norm_sub_sq_real (r t) (h • A (g t)),real_inner_smul_right,adj,norm_smul,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left op (sq_nonneg h)]
  have anti : Antitone f := antitone_nat_of_succ_le (fun i => by linarith [dec i,mul_nonneg cp.le (sq_nonneg ‖g i‖)])
  have lim := tendsto_atTop_ciInf anti (show BddBelow (Set.range f) from ⟨0,fun _ ⟨t,e⟩ => e ▸ sq_nonneg _⟩)
  have diff : Tendsto (fun t => (f t-f (t+1))/c) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,sub_self,zero_div] using (lim.sub (lim.comp (tendsto_add_atTop_nat 1))).div_const c
  have small := squeeze_zero (fun t => sq_nonneg ‖g t‖)
    (fun t => (le_div_iff₀ cp).mpr (by simpa only [mul_comm] using dec t)) diff
  have grad : Tendsto g atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (by
    simpa only [sqrt_sq (norm_nonneg _),sqrt_zero,Function.comp_def] using (continuous_sqrt.tendsto 0).comp small)
  let K := A.adjoint.comp A
  have k : K.ker=A.ker := A.ker_adjoint_comp_self
  have gr (v : H) : A.adjoint v∈A.kerᗮ := (Submodule.mem_orthogonal _ _).mpr (fun x hx => by
    rw [A.adjoint_inner_right,show A x=0 from hx,inner_zero_left])
  have row (t : ℕ) : u t∈A.kerᗮ := by
    induction t with
    | zero => rw [zero];exact Submodule.zero_mem _
    | succ t ih => rw [step];exact A.kerᗮ.add_mem ih (A.kerᗮ.smul_mem _ (gr _))
  have nr : A.adjoint (y-A (pinv A y))=0 := by
    apply (A.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero _ _).mp
    exact (minimum_norm A y).1
  have repr (t : ℕ) : pinv K (g t)=pinv A y-u t := by
    have gp : g t=K (pinv A y-u t) := by
      change A.adjoint (y-A (u t))=A.adjoint (A (pinv A y-u t))
      simp only [map_sub] at nr ⊢
      rw [sub_eq_zero.mp nr]
    rw [gp]
    apply pinv_apply_on_row
    rw [k];exact A.kerᗮ.sub_mem (pinv_mem A y) (row t)
  have limu : Tendsto u atTop (𝓝 (pinv A y)) := by
    have eq : u=fun t => pinv A y-pinv K (g t) := by funext t;rw [repr];abel
    rw [eq]
    simpa only [Function.comp_apply,map_zero,sub_zero] using tendsto_const_nhds.sub (((pinv K).continuous.tendsto 0).comp grad)
  refine ⟨limu,?_⟩
  have res := (tendsto_const_nhds (x:=y) (f:=atTop (α:=ℕ))).sub ((A.continuous.tendsto _).comp limu)
  simpa only [Function.comp_apply,apply_pinv,Submodule.starProjection_orthogonal_val] using res

/-- Finite-dimensional Gram factorization of the Moore–Penrose inverse. -/
theorem gram_factor (A : E →L[ℝ] H) (y : H) :
    pinv A y=A.adjoint (pinv (A.comp A.adjoint) y) := by
  let K := A.comp A.adjoint
  have range : K.range=A.range := A.toLinearMap.range_self_comp_adjoint
  have row : A.adjoint (pinv K y)∈A.kerᗮ := (Submodule.mem_orthogonal _ _).mpr (fun x hx => by
    rw [A.adjoint_inner_right,show A x=0 from hx,inner_zero_left])
  have eq : A (A.adjoint (pinv K y))=A (pinv A y) := by
    change K (pinv K y)=A (pinv A y)
    rw [apply_pinv,apply_pinv]
    symm
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · rw [←range];exact (K.range.orthogonalProjectionOnto y).property
    · rw [←range];exact sub_starProjection_mem_orthogonal _
  calc _ = pinv A (A (pinv A y)) := (pinv_apply_on_row A (pinv_mem A y)).symm
       _ = _ := by rw [←eq,pinv_apply_on_row A row]

/-- Squared parameter movement in optimizer coordinates at the least-squares limit. -/
theorem movement_identity (A : E →L[ℝ] H) (y : H) :
    ‖pinv A y‖^2=inner ℝ y (pinv (A.comp A.adjoint) y) := by
  let K := A.comp A.adjoint
  let q := pinv K y
  have kr : K.ker=A.adjoint.ker := A.ker_self_comp_adjoint
  have qmem := pinv_mem K y
  rw [kr,←A.orthogonal_range,Submodule.orthogonal_orthogonal] at qmem
  have ortho := (Submodule.mem_orthogonal _ _).mp (sub_starProjection_mem_orthogonal (K:=A.range) y) q qmem
  rw [inner_sub_right,sub_eq_zero] at ortho
  calc _ = inner ℝ (pinv A y) (pinv A y) := (real_inner_self_eq_norm_sq _).symm
       _ = inner ℝ q (A (pinv A y)) := by nth_rw 1 [gram_factor];exact A.adjoint_inner_left _ _
       _ = inner ℝ q y := by rw [apply_pinv];exact ortho.symm
       _ = _ := real_inner_comm _ _

/-- Residual convention and step-size interval used by the training-movement
budget. The limit is valid for every rank and every initial residual. -/
theorem movement_limit (A : E →L[ℝ] H) (r₀ : H) (h : ℝ) (hp : 0<h) (stable : h<2/‖A‖^2)
    (u : ℕ → E) (zero : u 0=0) (step : ∀ t, u (t+1)=u t-h • A.adjoint (r₀+A (u t))) :
    Tendsto u atTop (𝓝 (-(pinv A r₀))) ∧
    Tendsto (fun t => r₀+A (u t)) atTop (𝓝 (A.rangeᗮ.starProjection r₀)) := by
  have pos : 0<‖A‖^2 := by
    by_contra! hh
    have hh' := le_antisymm hh (sq_nonneg ‖A‖)
    rw [hh',div_zero] at stable
    linarith
  have sub (t : ℕ) : u (t+1)=u t+h • A.adjoint (-r₀-A (u t)) := by
    rw [show -r₀-A (u t) = -(r₀+A (u t)) by abel,map_neg,smul_neg,step,sub_eq_add_neg]
  have c := convergence A (-r₀) h hp ((lt_div_iff₀ pos).mp stable) u zero sub
  refine ⟨by simpa only [map_neg] using c.1,?_⟩
  have neg := c.2.neg
  simpa only [neg_sub,sub_neg_eq_add,map_neg,neg_neg,add_comm] using neg

/-- A fixed whitening map transports the actual training limit. If its squared
singular values lie in [α,β], the two ratio bounds use the same Gram quadratic
form for every rank. -/
theorem whitened_budget {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] H) (C : E →L[ℝ] G) (r₀ : H) (h α β : ℝ) (hp : 0<h) (stable : h<2/‖A‖^2)
    (u : ℕ→E) (zero : u 0=0) (step : ∀ t, u (t+1)=u t-h • A.adjoint (r₀+A (u t)))
    (bounds : ∀ z, α*‖z‖^2≤‖C z‖^2 ∧ ‖C z‖^2≤β*‖z‖^2) :
    let q := pinv (A.comp A.adjoint) r₀
    Tendsto (fun t => ‖C (u t)‖^2) atTop (𝓝 (‖C (A.adjoint q)‖^2)) ∧
    α*inner ℝ r₀ q≤‖C (A.adjoint q)‖^2 ∧ ‖C (A.adjoint q)‖^2≤β*inner ℝ r₀ q := by
  intro q
  have eq : pinv A r₀=A.adjoint q := gram_factor A r₀
  have identity := movement_identity A r₀
  have est := bounds (pinv A r₀)
  rw [identity,eq] at est
  refine ⟨?_,est⟩
  simpa only [map_neg,norm_neg,eq] using TrainingPath.squared_budget_limit C u _
    (movement_limit A r₀ h hp stable u zero step).1

/-- Surjectivity gives exact interpolation and the unique minimum-norm exact fit. -/
theorem full_row_rank (A : E →L[ℝ] H) (onto : Function.Surjective A) (y : H) :
    A (pinv A y)=y ∧ ∀ x, A x=y → ‖x‖^2=‖pinv A y‖^2+‖x-pinv A y‖^2 := by
  obtain ⟨v,hv⟩ := onto y
  have fit : A (pinv A y)=y := by
    rw [apply_pinv];exact Submodule.starProjection_mem_subspace_eq_self (K:=A.range) ⟨y,⟨v,hv⟩⟩
  refine ⟨fit,fun x hx => (minimum_norm A y).2 x ?_⟩
  rw [hx,sub_self,norm_zero];exact fun _ => norm_nonneg _

end LinearLeastSquares
