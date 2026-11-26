module
public import CircleTeacherRKHS
import all CircleTeacherRKHS
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-! The sharp odd-grid teacher interval with its Gram solution and radius
slack constructed from a compatible covariance-space teacher. -/
public section
noncomputable section
namespace CircleDesignRadius
open Real MeasureTheory CircleTeacherRKHS CircleGridSpectrum CircleSpectrum
open scoped InnerProductSpace
variable {n : ℕ}

/-- Projection onto the finite design span realizes the Gram solution and the
exact least squared norm of any teacher realizing the observations. -/
theorem solution (n : ℕ) (h : H) (y : Fin (n+1)→ℝ)
    (labels : ∀ i, inner ℝ h (gridSection i)=y i) :
    ∃ t : Fin (n+1)→ℝ, (∀ i, ∑ j,t j*sampledMatrix 0 j i=y i) ∧
      ∑ i,t i*y i≤‖h‖^2 ∧ ∀ u : H, (∀ i, inner ℝ u (gridSection i)=y i) →
        ∑ i,t i*y i≤‖u‖^2 := by
  let a := @gridSection (n+1)
  let S := Submodule.span ℝ (Set.range a)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range a)
  obtain ⟨t,ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (S.starProjection_apply_mem h)
  have sec (i) : S.starProjection (a i) = a i :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨i,rfl⟩)
  have hl (i) : inner ℝ (S.starProjection h) (a i) = y i := by
    rw [Submodule.inner_starProjection_left_eq_right,sec,labels]
  have gram (i) : ∑ j,t j*sampledMatrix 0 j i=y i := by
    have v := hl i
    rw [←ht,sum_inner] at v
    simpa only [a,real_inner_smul_left,grid_covariance] using v
  have cost : (∑ i,t i*y i)=‖S.starProjection h‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    conv_rhs => lhs; rw [←ht]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left,real_inner_comm,hl]
  have minimal (u : H) (hu : ∀ i, inner ℝ u (gridSection i)=y i) : ∑ i,t i*y i ≤ ‖u‖^2 := by
    have hu' : inner ℝ (S.starProjection h) u = ∑ i,t i*y i := by
      rw [←ht,sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_left,real_inner_comm,hu]
    have cs := real_inner_le_norm (S.starProjection h) u
    rw [hu',cost] at cs
    rw [cost]
    nlinarith [sq_nonneg (‖S.starProjection h‖-‖u‖),norm_nonneg u,norm_nonneg (S.starProjection h)]
  exact ⟨t,gram,minimal h labels,minimal⟩

/-- Exact interval for every compatible teacher ball and every odd grid, with
no matrix inverse or external Gram solution supplied by the caller. -/
theorem exact_interval (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1))
    (y : Fin (n+1)→ℝ) (R : ℝ) (h : H) (cap : ‖h‖≤R)
    (labels : ∀ i,inner ℝ h (gridSection i)=y i) :
    ∃ t : Fin (n+1)→ℝ, (∀ i, ∑ j,t j*sampledMatrix 0 j i=y i) ∧
      (∑ i,t i*y i≤R^2) ∧
      (∀ f : H, ‖f‖≤R → (∀ i,inner ℝ f (gridSection i)=y i) →
        |(∫ u,inner ℝ f (sectionAt (2*π*u)) ∂CircleTangentDrift.angularLaw)-∑ i,designWeight n i*y i| ≤
          √(R^2-∑ i,t i*y i)*√(minVariance n)) ∧
      ∀ s : ℝ, |s|≤1 → ∃ f : H, ‖f‖≤R ∧ (∀ i, inner ℝ f (gridSection i)=y i) ∧
        (∫ u,inner ℝ f (sectionAt (2*π*u)) ∂CircleTangentDrift.angularLaw)=
          ∑ i,designWeight n i*y i+s*√(R^2-∑ i,t i*y i)*√(minVariance n) := by
  obtain ⟨t,fit,cost,_⟩ := solution n h y labels
  have bound := cost.trans (pow_le_pow_left₀ (norm_nonneg _) cap 2)
  refine ⟨t,fit,bound,?_,fun s hs => sharp_interval n hn ho t y R s ((norm_nonneg _).trans cap) hs fit bound⟩
  intro f hf hy
  simpa only [sub_self,abs_zero,zero_add,abs_sub_comm (∑ i,designWeight n i*y i)] using
    after_labels n hn ho f t y (∑ i,designWeight n i*y i) R hy hf fit
end CircleDesignRadius
