module
public import CircleInitializationConcentration
import all CircleInitializationConcentration
import Mathlib.Tactic

/-! Relative Euclidean displacement for a diagonal Gaussian covariance.
The exceptional budget may depend arbitrarily on the same initialization. -/
@[expose] public section
noncomputable section
namespace GaussianTraceBudget
open ProbabilityTheory MeasureTheory Real
open scoped ENNReal

variable {ι : Type*} [Fintype ι]
abbrev law (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
def energy (v : ι → ℝ) (z : ι → ℝ) := ∑ i, v i * z i ^ 2
private theorem energy_eq (v : ι → ℝ) : energy v = ∑ i, (fun z : ι → ℝ => v i*z i^2) := by
  ext z; simp [energy,Finset.sum_apply]
private theorem square_mem : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have h : MemLp id (4:ℕ) (gaussianReal 0 1) := memLp_id_gaussianReal' 4 (by norm_num)
  simpa [Real.norm_eq_abs, (by decide : Even 4).pow_abs, ← pow_mul] using h.integrable_norm_pow'
private theorem scalar_mean : ∫ x : ℝ, x^2 ∂gaussianReal 0 1=1 := by
  have h := CircleInitializationConcentration.gaussian_even_moment_succ 0
  norm_num at h
  exact h
private theorem scalar_var : variance (fun x : ℝ => x^2) (gaussianReal 0 1) = 2 := by
  rw [variance_eq_sub square_mem]
  change (∫ x : ℝ,(x^2)^2 ∂gaussianReal 0 1)-(∫ x : ℝ,x^2 ∂gaussianReal 0 1)^2=2
  simp_rw [←pow_mul]
  rw [scalar_mean,CircleInitializationConcentration.gaussian_fourth]
  norm_num

private theorem coordinate_mem (v : ι → ℝ) (i : ι) :
    MemLp (fun z : ι → ℝ => v i*z i^2) 2 (law ι) :=
  (square_mem.const_mul (v i)).comp_measurePreserving (measurePreserving_eval _ i)

theorem moments (v : ι → ℝ) :
    (∫ z, energy v z ∂law ι) = ∑ i, v i ∧
      variance (energy v) (law ι)=2*∑ i, (v i)^2 := by
  constructor
  · unfold energy
    rw [integral_finsetSum _ fun i _ => (coordinate_mem v i).integrable (by norm_num)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
      (f := fun x : ℝ => x^2) (by fun_prop)
    simpa [Function.comp_def,scalar_mean] using congrArg (fun t : ℝ => v i*t) h
  · have h := variance_sum_pi (μ:=fun _ : ι => gaussianReal 0 1)
        (X:=fun i (x:ℝ) => v i*x^2) (fun i => square_mem.const_mul (v i))
    rw [energy_eq]
    simpa [variance_const_mul,scalar_var,Finset.mul_sum,mul_comm] using h

/-- A lower-tail estimate for the squared Euclidean initialization norm. -/
theorem lower_tail (v : ι → ℝ) (ht : 0 < ∑ i, v i) :
    (law ι).real {z | energy v z ≤ (∑ i, v i)/2} ≤
      8*(∑ i,(v i)^2)/(∑ i,v i)^2 := by
  have mem : MemLp (energy v) 2 (law ι) := by
    rw [energy_eq]; exact memLp_finsetSum' _ fun i _ => coordinate_mem v i
  have h := meas_ge_le_variance_div_sq mem (half_pos ht)
  rw [(moments v).1,(moments v).2] at h
  have sub : {z | energy v z ≤ (∑ i, v i)/2} ⊆
      {z | (∑ i, v i)/2 ≤ |energy v z - ∑ i, v i|} := by
    intro z hz
    exact (show (∑ i, v i)/2 ≤ -(energy v z - ∑ i, v i) by
      change energy v z ≤ _ at hz; linarith).trans (neg_le_abs _)
  have bound := (measure_mono sub).trans h
  apply le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top bound)
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring_nf
  rfl

/-- Diagonal covariance converts a whitened square norm to a physical one. -/
theorem physical_le (v w : ι → ℝ) {Λ : ℝ} (h : ∀ i, v i ≤ Λ) :
    energy v w ≤ Λ * ∑ i, w i^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _))

/-- The diagonal metric bound and the Gaussian denominator imply (5): with
budget at most K away from a set of probability p, the squared relative
displacement exceeds 2 λ K / trace with probability at most p plus the
displayed trace error. Multiplication avoids a convention at the zero seed. -/
theorem relative_tail (v : ι → ℝ) (ht : 0 < ∑ i, v i)
    (B D : (ι → ℝ) → ℝ) {Λ K : ℝ} (hΛ : 0≤Λ) (hK : 0≤K)
    (metric : ∀ z, D z ≤ Λ*B z) :
    (law ι).real {z | 2*Λ*K*energy v z < D z * (∑ i,v i)} ≤
      (law ι).real {z | K < B z} + 8*(∑ i,(v i)^2)/(∑ i,v i)^2 := by
  have sub : {z | 2*Λ*K*energy v z < D z*(∑ i,v i)} ⊆
      {z | K < B z} ∪ {z | energy v z ≤ (∑ i,v i)/2} := by
    intro z hz
    by_cases hb : K < B z
    · exact Or.inl hb
    apply Or.inr
    change energy v z ≤ (∑ i,v i)/2
    by_contra! he
    have h1 := mul_le_mul_of_nonneg_right ((metric z).trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) hΛ)) ht.le
    have h2 := mul_le_mul_of_nonneg_left he.le (mul_nonneg hΛ hK)
    change 2*Λ*K*energy v z < D z*(∑ i,v i) at hz
    linarith
  exact (measureReal_mono sub).trans ((measureReal_union_le _ _).trans
    (add_le_add_right (lower_tail v ht) _))
/-- Explicit bounded-in-probability formulation of the squared version of
(5), for varying dimensions. All numerators may depend on the initial draw. -/
theorem relative_in_probability {I : ℕ → Type*} [∀ n,Fintype (I n)]
    (v : ∀ n, I n → ℝ) (w : ∀ n, (I n → ℝ) → I n → ℝ) (Λ : ℕ → ℝ)
    (ht : ∀ n, 0 < ∑ i, v n i) (hp : ∀ n, 0 ≤ Λ n) (hv : ∀ n i, v n i ≤ Λ n)
    (concentrates : Filter.Tendsto (fun n => (∑ i, (v n i)^2)/(∑ i,v n i)^2)
      Filter.atTop (nhds 0))
    (tight : ∀ e : ℝ, 0 < e → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in Filter.atTop,
      (law (I n)).real {z | K < ∑ i, (w n z i)^2} ≤ e) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in Filter.atTop,
      (law (I n)).real {z | C * Λ n * energy (v n) z <
        energy (v n) (w n z) * (∑ i, v n i)} ≤ e := by
  intro e he
  obtain ⟨K,hK,t⟩ := tight (e/2) (half_pos he)
  refine ⟨2*K,by positivity,?_⟩
  filter_upwards [t,concentrates.eventually (gt_mem_nhds (show 0 < e/16 by positivity))] with n hn hn'
  have h := relative_tail (v n) (ht n) (fun z => ∑ i,(w n z i)^2)
    (fun z => energy (v n) (w n z)) (hp n) hK (fun z => physical_le _ _ (hv n))
  rw [show 2*K*Λ n=2*Λ n*K by ring]
  apply h.trans
  change (∑ i, (v n i)^2)/(∑ i,v n i)^2 < e/16 at hn'
  rw [mul_div_assoc]
  linarith

end GaussianTraceBudget
