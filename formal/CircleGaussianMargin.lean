module

public import CircleKernelIdentification
import all CircleKernelIdentification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-! The marked near-kink mass of a three-dimensional standard Gaussian using
two planar polar changes of variables. The axial coordinate is listed first. -/

public section
noncomputable section
namespace CircleGaussianMargin
open CircleKernelIdentification Real MeasureTheory Set ProbabilityTheory

def angularMark (ρ t : ℝ) : ℝ := max (sin t) 0 * (if |cos t| ≤ ρ then 1 else 0)

theorem angular_mass (ρ : ℝ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) :
    (∫ t in Ioo (-π) π, angularMark ρ t) = 2*ρ := by
  let A := Icc (arccos ρ) (arccos (-ρ))
  have hplus : cos (arccos ρ) = ρ := cos_arccos (by linarith) hu
  have hminus : cos (arccos (-ρ)) = -ρ := cos_arccos (by linarith) (by linarith)
  have hsub : A ⊆ Icc (-π) π := fun t ht => ⟨by linarith [ht.1, arccos_nonneg ρ, pi_pos],
    ht.2.trans (arccos_le_pi _)⟩
  rw [← integral_Icc_eq_integral_Ioo]
  calc
    _ = ∫ t in Icc (-π) π, A.indicator sin t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      by_cases hn : t < 0
      · have hs : sin t ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hn.le ht.1
        have hx : t ∉ A := fun h => hn.not_ge ((arccos_nonneg ρ).trans h.1)
        simp [angularMark, max_eq_right hs, hx]
      · have ht₀ := le_of_not_gt hn
        have htπ := ht.2
        have equiv : |cos t| ≤ ρ ↔ t ∈ A := by
          rw [abs_le]
          constructor
          · rintro ⟨ha,hb⟩
            exact ⟨(arccos_le_arccos hb).trans_eq (arccos_cos ht₀ htπ),
              (arccos_cos ht₀ htπ).symm.trans_le (arccos_le_arccos ha)⟩
          · intro ha
            have hh₁ := strictAntiOn_cos.antitoneOn
              (show t ∈ Icc 0 π from ⟨ht₀,htπ⟩)
              (show arccos (-ρ) ∈ Icc 0 π from ⟨arccos_nonneg _, arccos_le_pi _⟩) ha.2
            have hh₂ := strictAntiOn_cos.antitoneOn
              (show arccos ρ ∈ Icc 0 π from ⟨arccos_nonneg _, arccos_le_pi _⟩)
              (show t ∈ Icc 0 π from ⟨ht₀,htπ⟩) ha.1
            exact ⟨hminus ▸ hh₁, hplus ▸ hh₂⟩
        by_cases ha : t ∈ A <;> simp [angularMark, max_eq_left (sin_nonneg_of_nonneg_of_le_pi ht₀ htπ), equiv, ha]
    _ = ∫ t in A, sin t := by rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
    _ = _ := by
      have hab := arccos_le_arccos (show -ρ ≤ ρ by linarith)
      unfold A
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_sin, hplus, hminus]
      ring

def mark (ρ : ℝ) (p : ℕ) (x E : ℝ) : ℝ := if |x| ≤ ρ*√E then E^p else 0

abbrev G := gaussianReal 0 1

private theorem radial_law (F : ℝ → ℝ) :
    (∫ w : ℝ × ℝ, F (w.1^2+w.2^2) ∂standardPair) =
      √(2*π) * ∫ y : ℝ, max y 0 * F (y^2) ∂G := by
  rw [standardPair_integral, gaussian_polar_separate _ (fun r => F (r^2)) (fun _ => 1)]
  · simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [pi_pos])]
    have hs : √(2*π) ≠ 0 := by positivity
    rw [G, integral_gaussianReal_eq_integral_smul (by norm_num)]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    let f (y : ℝ) := y*exp (-(1/2)*y^2)*F (y^2)
    have hfun (y : ℝ) : (√(2*π))⁻¹*exp (-y^2/2)*(max y 0 * F (y^2)) =
        (√(2*π))⁻¹*(Ioi (0:ℝ)).indicator f y := by
      by_cases hy : 0 < y
      · rw [indicator_of_mem (show y ∈ Ioi (0:ℝ) from hy), max_eq_left hy.le]
        unfold f
        rw [show -y^2/2 = -(1/2)*y^2 by ring]
        ring
      · rw [indicator_of_notMem (show y ∉ Ioi (0:ℝ) from hy), max_eq_right (le_of_not_gt hy)]
        ring
    simp_rw [hfun]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
    dsimp [f]
    field_simp [hs,pi_ne_zero]
    ring
  · intro r hr t
    rw [show (r*cos t)^2 + (r*sin t)^2 = r^2 by linear_combination r^2*(sin_sq_add_cos_sq t)]
    simp

def energy (z : ℝ × (ℝ × ℝ)) := z.1^2+(z.2.1^2+z.2.2^2)

private def moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) :=
  ∀ q : ENNReal, q ≠ ⊤ → MemLp f q μ

private theorem norm_pow_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : moments μ f) (d : ℕ) : moments μ (fun x => |f x|^d) := by
  intro p hp
  cases d with
  | zero => simpa using (memLp_const (μ:=μ) (p:=p) (1:ℝ))
  | succ d =>
    let q : ENNReal := (d+1 : ℕ)
    have hn : q ≠ 0 := by dsimp [q]; positivity
    have ht : q ≠ ⊤ := by dsimp [q]; finiteness
    have h := (hf (p*q) (ENNReal.mul_ne_top hp ht)).norm_rpow_div q
    rw [ENNReal.mul_div_cancel_right hn ht] at h
    have hq : q.toReal = (d+1:ℕ) := ENNReal.toReal_natCast _
    rw [hq] at h
    simpa only [Real.rpow_natCast, Real.norm_eq_abs] using h

private theorem sq_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : moments μ f) : moments μ (fun x => f x^2) := by
  simpa only [sq_abs] using norm_pow_moments hf 2

private theorem mark_mem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x E : Ω → ℝ} (hx : Measurable x) (he : Measurable E) (hn : ∀ a, 0 ≤ E a)
    (hm : moments μ E) (ρ : ℝ) (p : ℕ) : moments μ (fun a => mark ρ p (x a) (E a)) := by
  intro q hq
  have base := (norm_pow_moments hm p) q hq
  simp only [fun a => abs_of_nonneg (hn a)] at base
  apply base.of_le
  · unfold mark
    exact (Measurable.ite (measurableSet_le (show Measurable (fun a => |x a|) by fun_prop) (show Measurable (fun a => ρ*√(E a)) by fun_prop)) (he.pow_const p) measurable_const).aestronglyMeasurable
  · exact ae_of_all _ fun x => by unfold mark; split <;> simp

private theorem coordinate_pair :
    moments standardPair (fun z => z.1) ∧ moments standardPair (fun z => z.2) := by
  constructor <;> intro q hq
  · exact (memLp_id_gaussianReal' q hq).comp_measurePreserving measurePreserving_fst
  · exact (memLp_id_gaussianReal' q hq).comp_measurePreserving measurePreserving_snd

private theorem integrable_mark (ρ : ℝ) (p : ℕ) :
    Integrable (fun z => mark ρ p z.1 (energy z)) (G.prod standardPair) := by
  have h₁ : moments (G.prod standardPair) (fun z => z.1) :=
    fun q hq => (memLp_id_gaussianReal' q hq).comp_measurePreserving measurePreserving_fst
  have h₂ : moments (G.prod standardPair) (fun z => z.2.1) :=
    fun q hq => (coordinate_pair.1 q hq).comp_measurePreserving measurePreserving_snd
  have h₃ : moments (G.prod standardPair) (fun z => z.2.2) :=
    fun q hq => (coordinate_pair.2 q hq).comp_measurePreserving measurePreserving_snd
  have hE : moments (G.prod standardPair) energy := fun q hq =>
    ((sq_moments h₁) q hq).add (((sq_moments h₂) q hq).add ((sq_moments h₃) q hq))
  apply memLp_one_iff_integrable.mp
  exact mark_mem measurable_fst (by unfold energy; fun_prop) (by intro a; unfold energy; positivity)
    hE ρ p 1 (by norm_num)

private theorem integrable_plane (ρ : ℝ) (p : ℕ) :
    Integrable (fun z : ℝ × ℝ => max z.2 0 * mark ρ p z.1 (z.1^2+z.2^2)) standardPair := by
  have hE : moments standardPair (fun z => z.1^2+z.2^2) := fun q hq =>
    ((sq_moments coordinate_pair.1) q hq).add ((sq_moments coordinate_pair.2) q hq)
  have hm : MemLp (fun z : ℝ×ℝ => mark ρ p z.1 (z.1^2+z.2^2)) 2 standardPair :=
    mark_mem measurable_fst (by fun_prop) (by intro a; positivity) hE ρ p 2 (by norm_num)
  have hy : MemLp (fun z : ℝ×ℝ => max z.2 0) 2 standardPair :=
    (coordinate_pair.2 2 (by norm_num)).of_le (by fun_prop) (ae_of_all _ fun z => by
      change |max z.2 0| ≤ |z.2|
      rw [abs_of_nonneg (le_max_right z.2 0)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  exact memLp_one_iff_integrable.mp (hy.mul hm)

private theorem mark_factor (ρ : ℝ) (p : ℕ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) :
    (∫ z, mark ρ p z.1 (energy z) ∂G.prod standardPair) =
       √(2*π) * ((1/(2*π)) * (∫ r in Ioi (0:ℝ), r*exp (-(1/2)*r^2)*(r*(r^2)^p)) * (2*ρ)) := by
  rw [integral_prod _ (integrable_mark ρ p)]
  unfold energy
  have hinner (x : ℝ) := radial_law (fun E => mark ρ p x (x^2+E))
  dsimp only [Prod.fst,Prod.snd]
  simp_rw [hinner]
  rw [integral_const_mul]
  congr 1
  rw [← integral_prod _ (integrable_plane ρ p)]
  change (∫ z, max z.2 0 * mark ρ p z.1 (z.1^2+z.2^2) ∂standardPair) = _
  rw [standardPair_integral]
  rw [gaussian_polar_separate _ (fun r => r*(r^2)^p) (angularMark ρ), angular_mass ρ hρ hu]
  intro r hr t
  dsimp only [Prod.fst,Prod.snd]
  rw [show (r*cos t)^2+(r*sin t)^2=r^2 by linear_combination r^2*(sin_sq_add_cos_sq t)]
  unfold mark angularMark
  simp only [sqrt_sq hr.le, abs_mul, abs_of_pos hr, mul_comm ρ r, mul_le_mul_iff_right₀ hr]
  have hmax : max (r*sin t) 0 = r*max (sin t) 0 := by rw [mul_max_of_nonneg _ _ hr.le, mul_zero]
  rw [hmax]
  by_cases h : |cos t| ≤ ρ
  · simp [h]; ring
  · simp [h]

/-- The signed axial direction of an isotropic standard Gaussian in three
dimensions is uniform on [-1,1] independently of every radial power. -/
theorem aligned_energy_mark (ρ : ℝ) (p : ℕ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) :
    (∫ z, mark ρ p z.1 (energy z) ∂G.prod standardPair) =
      ρ * ∫ z, energy z ^ p ∂G.prod standardPair := by
  have hone (z : ℝ × (ℝ × ℝ)) : mark 1 p z.1 (energy z) = energy z^p := by
    have h : |z.1| ≤ √(energy z) := by
      apply Real.le_sqrt_of_sq_le
      rw [sq_abs]; unfold energy; nlinarith [sq_nonneg z.2.1,sq_nonneg z.2.2]
    simp [mark,h]
  simp_rw [← hone]
  rw [mark_factor ρ p hρ hu, mark_factor 1 p (by norm_num) (by norm_num)]
  ring

end CircleGaussianMargin
