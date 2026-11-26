module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleReadoutMargin
import all CircleKernelIdentification
import all GaussianTraceBudget
import all CircleEscape
import all CircleTangentDrift
import Mathlib.Tactic

/-! Finite-width variance on a unit input and the dependence of the cross kernel on the
norm of an orthogonal test input. Both entries use the empirical tangent of the actual
jointly trained readout and hidden weights. -/
public section
noncomputable section
namespace CircleDiagonalTangent
open CircleInitializationConcentration CircleEscapeBridge CircleEscape MeasureTheory
  ProbabilityTheory Real
open scoped InnerProductSpace

private def gated (s a : ℝ) := if 0<s then s^2+a^2 else 0
private def total (z : Atom) := z 1^2+z 0^2

private theorem total_mem : MemLp total 2 atomLaw := by
  exact (GaussianTraceBudget.square_mem.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3=>gaussianReal 0 1) 1)).add
      (GaussianTraceBudget.square_mem.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3=>gaussianReal 0 1) 0))

private theorem total_moments :
    (∫ z,total z ∂atomLaw)=2 ∧ (∫ z,total z^2 ∂atomLaw)=8 := by
  let v : Fin 3→ℝ := ![1,1,0]
  have repr : total=GaussianTraceBudget.energy v := by
    ext z; simp [total,GaussianTraceBudget.energy,v,Fin.sum_univ_three,add_comm]
  have ht := GaussianTraceBudget.moments v
  change (∫ z,GaussianTraceBudget.energy v z ∂atomLaw)=_ ∧
    variance (GaussianTraceBudget.energy v) atomLaw=_ at ht
  rw [←repr] at ht
  norm_num [v,Fin.sum_univ_three] at ht
  have hv := ht.2
  rw [variance_eq_sub total_mem,ht.1] at hv
  change (∫ z,total z^2 ∂atomLaw)-2^2=4 at hv
  exact ⟨ht.1,by linarith⟩

private theorem diag_repr {x : ℂ} (hx : ‖x‖=1) (z : Atom) :
    tangentAtom x x z=gated (x.re*z 1+x.im*z 2) (z 0) := by
  have ip : inner ℝ (⟨z 1,z 2⟩:ℂ) x=x.re*z 1+x.im*z 2 := by
    simp [Complex.inner,Complex.mul_re]
  rw [tangentAtom,feature,gate,ip,real_inner_self_eq_norm_sq,hx]
  by_cases h : 0<x.re*z 1+x.im*z 2
  · simp [gated,h,max_eq_left h.le];ring
  · simp [gated,h,max_eq_right (le_of_not_gt h)]

private theorem diag_moment {x : ℂ} (hx : ‖x‖=1) (p : ℕ) (hp : p≠0)
    (hi : Integrable (fun z => total z^p) atomLaw) :
    (∫ z,(tangentAtom x x z)^p ∂atomLaw)=(∫ z,total z^p ∂atomLaw)/2 := by
  have hn : x.re^2+x.im^2=1 := by
    have h := Complex.sq_norm x
    rw [hx,Complex.normSq_apply] at h
    nlinarith only [h]
  simp_rw [diag_repr hx]
  rw [CircleReadoutMargin.rotate (x.re,x.im) hn (fun _ t a => gated t a^p)]
  have neg := CircleReadoutMargin.rotate (-1,0) (by norm_num) (fun _ t a => gated t a^p)
  simp only [neg_one_mul,zero_mul,add_zero] at neg
  have plus : Integrable (fun z : Atom => gated (z 1) (z 0)^p) atomLaw := by
    have h := hi.indicator (measurableSet_lt (measurable_const (a:=(0:ℝ))) (measurable_pi_apply 1))
    apply h.congr (ae_of_all _ fun z => ?_)
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,gated,ite_pow,zero_pow hp,total]
  have minus : Integrable (fun z : Atom => gated (-(z 1)) (z 0)^p) atomLaw := by
    have h := hi.indicator (measurableSet_lt (measurable_pi_apply 1) (measurable_const (a:=(0:ℝ))))
    apply h.congr (ae_of_all _ fun z => ?_)
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,gated,ite_pow,zero_pow hp,total,neg_pos,neg_sq]
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have ae : ∀ᵐ z ∂atomLaw,z 1≠0 :=
    (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) 1).quasiMeasurePreserving.ae
      ((gaussianReal 0 1).ae_ne 0)
  have pair : (fun z : Atom => gated (z 1) (z 0)^p+gated (-(z 1)) (z 0)^p)
      =ᵐ[atomLaw] fun z => total z^p := by
    filter_upwards [ae] with z hz
    rcases lt_or_gt_of_ne hz with h|h
    · simp [gated,h.not_gt,neg_pos.mpr h,total,hp]
    · simp [gated,h,not_lt_of_ge (neg_nonpos.mpr h.le),total,hp]
  have h := integral_congr_ae pair
  rw [integral_add plus minus,neg] at h
  linarith

/-- Exact finite-width mean, variance and standard deviation of the initialized tangent
diagonal, for every unit input and arbitrary positive width. -/
theorem empirical_diagonal (m : ℕ) (hm : 0<m) (x : ℂ) (hx : ‖x‖=1) :
    (∫ z : Seed m,gramEntry x x z ∂seedLaw m)=1 ∧
      variance (gramEntry (m:=m) x x) (seedLaw m)=3/(m:ℝ) ∧
      sqrt (variance (gramEntry (m:=m) x x) (seedLaw m))=sqrt (3/(m:ℝ)) := by
  have h1 := diag_moment hx 1 (by decide)
    (by simpa using total_mem.integrable (by norm_num : (1:ENNReal)≤2))
  have h2 := diag_moment hx 2 (by decide) total_mem.integrable_sq
  simp only [pow_one,total_moments.1] at h1
  rw [total_moments.2] at h2
  norm_num at h1 h2
  have var : variance (tangentAtom x x) atomLaw=3 := by
    rw [variance_eq_sub (tangentAtom_memLp _ _ hx.le hx.le),h1]
    change (∫ z,tangentAtom x x z^2 ∂atomLaw)-1^2=3
    rw [h2];norm_num
  rw [gramEntry_variance hm _ _ hx.le hx.le,var,gramEntry_expectation hm _ _ hx.le hx.le,populationEntry,h1]
  exact ⟨rfl,rfl,rfl⟩

private theorem atom_scale {c : ℝ} (hc : 0<c) (x y : ℂ) (z : Atom) :
    tangentAtom (c • x) y z=c*tangentAtom x y z := by
  have scale (t : ℝ) : max (c*t) 0=c*max t 0 := by rw [mul_max_of_nonneg _ _ hc.le,mul_zero]
  simp only [tangentAtom,feature,gate,real_inner_smul_right,real_inner_smul_left,
    mul_pos_iff_of_pos_left hc,scale]
  ring

/-- Even pathwise, replacing e₂ by 2e₂ doubles the cross entry against e₁. -/
theorem empirical_orthogonal (m : ℕ) (z : Seed m) :
    inner ℝ Complex.I (1:ℂ)=0 ∧ inner ℝ ((2:ℝ) • Complex.I) (1:ℂ)=0 ∧
    gramEntry ((2:ℝ) • Complex.I) 1 z=2*gramEntry Complex.I 1 z := by
  constructor
  · simp [Complex.inner]
  constructor
  · simp [Complex.inner]
  · simp only [gramEntry,atom_scale (by norm_num : (0:ℝ)<2),←Finset.mul_sum];ring

theorem population_orthogonal :
    populationEntry Complex.I 1=1/(2*π) ∧ populationEntry ((2:ℝ) • Complex.I) 1=1/π := by
  have hm := weightedAtom_cartesian 1 (π/2) 0
  rw [CircleKernelIdentification.cartesian_kernel_isotropic,zero_sub,abs_neg,abs_of_pos (by positivity),
    CircleKernelIdentification.angular_tangent 1 (π/2) (by positivity) (by linarith [pi_pos])] at hm
  have hentry : populationEntry Complex.I 1=1/(2*π) := by
    simpa [populationEntry,tangentAtom,weightedAtom,CircleTangentDrift.dot,feature,Complex.inner,
      Complex.mul_re] using hm
  refine ⟨hentry,?_⟩
  simp only [populationEntry,atom_scale (by norm_num : (0:ℝ)<2),integral_const_mul]
  rw [←populationEntry,hentry];ring

end CircleDiagonalTangent
