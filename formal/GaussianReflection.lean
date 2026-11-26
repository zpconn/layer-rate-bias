module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-! A known hyperplane reflection of a finite-dimensional standard Gaussian. -/
public section
noncomputable section
namespace TrainingLaws
open ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In every finite dimension, reflection in the hyperplane with unit normal
u preserves the full endpoint law and has squared movement of mean four. -/
theorem reflection_budget (u : E) (hu : ‖u‖=1) :
    (stdGaussian E).map (fun x => x-(2*(inner ℝ u x)) • u) = stdGaussian E ∧
    (∫ x, ‖(x-(2*(inner ℝ u x)) • u)-x‖^2 ∂stdGaussian E)=4 := by
  let D := (ℝ ∙ u)ᗮ.reflection
  have same : (fun x => x-(2*(inner ℝ u x)) • u) = ⇑D := by
    funext x
    dsimp [D]
    rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply,hu]
    simp only [neg_sub]
    rw [mul_smul]
    simp [two_smul]
  refine ⟨same ▸ stdGaussian_map D,?_⟩
  let L := (InnerProductSpace.toDualMap ℝ E) u
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.measurable.aemeasurable,integral_strongDual_stdGaussian] at h
  have hn : ‖L‖=1 := ((InnerProductSpace.toDualMap ℝ E).norm_map u).trans hu
  simp only [sub_zero,hn,one_pow] at h
  have sq (x : E) : ‖(x-(2*(inner ℝ u x)) • u)-x‖^2=4*(L x)^2 := by
    rw [sub_sub_cancel_left,norm_neg,norm_smul,hu,mul_one,Real.norm_eq_abs,sq_abs]
    change (2*(inner ℝ u x))^2=4*(inner ℝ u x)^2
    ring
  simp_rw [sq]
  rw [integral_const_mul,h,mul_one]
end TrainingLaws
