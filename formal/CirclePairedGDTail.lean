module

public import CirclePairedGDCost
public import CirclePairedGDEndpoint
public import CirclePairedGDIntegrable
public import CirclePairedGDBox
import all CirclePairedGDEndpoint
import all CirclePairedCoefficient
import Mathlib.Tactic

/-! On a common narrow Gaussian box, the two genuine Euler endpoints
separate. Integrating the squared contrast on that box gives divergence
even after subtracting a uniformly square-integrable seed prediction. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDTail
open Real MeasureTheory Filter Topology CircleEscapeBridge CirclePairedGDEndpoint
  CirclePairedCoefficient CircleSynchronizedWidth CircleSynchronizedEscape CirclePairedGDIntegrable

private def gain := 2*log 2/3

private theorem gain_pos : 0<gain := by unfold gain; positivity

private theorem amplification (t : ℕ) :
    exp (gain*(3:ℝ)^(t+1)) = ((2:ℝ)^(3^t:ℕ))^2 := by
  have p : exp ((3:ℝ)^t * log 2) = (2:ℝ)^(3^t:ℕ) := by
    simpa [exp_log (by norm_num : (0:ℝ)<2)] using exp_nat_mul (log 2) (3^t)
  rw [←p,← exp_nat_mul, gain, pow_succ]
  congr 1
  push_cast
  ring

private theorem box_integral {N m t : ℕ} {η R : ℝ} (hN : 0<N) (hR : 0≤R)
    (amp : ∀ z ∈ syncBox N m (2*(t+1)) 1 (R/2),
      (2:ℝ)^(3^t:ℕ) ≤ |contrast N m (t+1) η z|) :
    exp (gain*3^(t+1)-cost N m (2*(t+1)) (R/2)) ≤
    ∫ z, (contrast N m (t+1) η z)^2 ∂seedLaw m := by
  have hF : MemLp (contrast N m (t+1) η) 2 (seedLaw m) :=
    contrast_memLp _ _ _ _ _ _ 2 (by norm_num)
  have mass := gaussian_box_probability N m (2*(t+1)) hN (R/2) 1 (by positivity) (by norm_num)
  have bound := CircleEscapeMoment.paired_second_moment_of_escape hF
    (memLp_const (0:ℝ) : MemLp (fun _ : Seed m => (0:ℝ)) 2 (seedLaw m))
    (measurable_syncBox ..) mass amp (B:=0) (fun _ _ => by simp)
  rw [sub_eq_add_neg,exp_add,amplification,mul_comm]
  simpa only [sub_zero, max_eq_left (by positivity : 0 ≤ (2:ℝ)^(3^t:ℕ))] using bound

private theorem growing_error (N m T : ℕ→ℕ) (d : ℕ→ℝ) (η R : ℝ) (hR : 0≤R)
    (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j)
    {D : ℝ} (hd : ∀ᶠ j in atTop, |d j|≤D)
    (small : Tendsto (fun j => CirclePairedGDCost.size (N j) (m j) (T j)/(3:ℝ)^(T j)) atTop (𝓝 0))
    (amp : ∀ᶠ j in atTop, ∀ t, T j=t+1 → ∀ z ∈ syncBox (N j) (m j) (2*(t+1)) 1 (R/2),
      (2:ℝ)^(3^t:ℕ) ≤ |contrast (N j) (m j) (t+1) η z|) :
    Tendsto (fun j => ∫ z, (contrast (N j) (m j) (T j) η z -
      (d j/(N j:ℝ)^2)*score (N j) (m j) z)^2 ∂seedLaw (m j)) atTop atTop := by
  have eg := CirclePairedGDCost.exponential N m T gain_pos R grow
    (valid.mono fun j v => by omega) small
  apply tendsto_atTop.2
  intro b
  let B := (D*CircleResidualSpectrum.modeConstant)^2
  filter_upwards [eg.eventually_ge_atTop (2*(b+B)),valid,hd,amp,grow.eventually_ge_atTop 1]
    with j hj v dcap box pos
  obtain ⟨t,ht⟩ : ∃ t, T j=t+1 := ⟨T j-1,by omega⟩
  have lower := box_integral (η:=η) (by omega : 0<N j) hR (box t ht)
  rw [←ht] at lower
  have hF : MemLp (contrast (N j) (m j) (T j) η) 2 (seedLaw (m j)) :=
    contrast_memLp _ _ _ _ _ _ 2 (by norm_num)
  have hG := scaledScore_memLp (d j) (N j) (m j) 2 (by norm_num)
  have minus := mse_lower (seedLaw (m j)) hF hG
  have cap := pow_le_pow_left₀ lpNorm_nonneg (scaledScore_lpNorm_le v.1 v.2.2 dcap) 2
  change _≤B at cap
  linarith only [hj,lower,cap,minus]

/-- The actual paired prediction has divergent unconditional mean-square error
for every fixed positive base step and every bounded coefficient sequence,
whenever the Gaussian-box log-cost is negligible on the cubic scale. -/
theorem of_small (N m T : ℕ→ℕ) (d : ℕ→ℝ) (η : ℝ) (hη : 0<η)
    (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j)
    {D : ℝ} (hd : ∀ᶠ j in atTop, |d j|≤D)
    (small : Tendsto (fun j => CirclePairedGDCost.size (N j) (m j) (T j)/(3:ℝ)^(T j))
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ z, (contrast (N j) (m j) (T j) η z -
      (d j/(N j:ℝ)^2)*score (N j) (m j) z)^2 ∂seedLaw (m j)) atTop atTop := by
  let R := max 32 (sqrt (16*(32/η+32)))
  have hR : 32≤R := le_max_left ..
  have hr : 16*(32/η+32) ≤ R^2 := by
    rw [← Real.sq_sqrt (by positivity : 0≤16*(32/η+32))]
    exact pow_le_pow_left₀ (sqrt_nonneg _) (le_max_right ..) 2
  apply growing_error N m T d η R (by linarith) grow valid hd small
  filter_upwards [valid,grow.eventually_ge_atTop 2] with j v steps
  intro t ht z box
  exact CirclePairedGDBox.box_contrast v.1 v.2.1 v.2.2 hη hR hr (by omega) box

/-- The manuscript criterion in its original ratio form. No additional growth
assumption on the width, grid size, or horizon is required. -/
theorem of_ratio (N m T : ℕ→ℕ) (d : ℕ→ℝ) (η : ℝ) (hη : 0<η)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j)
    {D : ℝ} (hd : ∀ᶠ j in atTop, |d j|≤D)
    (ratio : Tendsto (fun j => (3:ℝ)^(T j)/CirclePairedGDCost.size (N j) (m j) (T j))
      atTop atTop) :
    Tendsto (fun j => ∫ z, (contrast (N j) (m j) (T j) η z -
      (d j/(N j:ℝ)^2)*score (N j) (m j) z)^2 ∂seedLaw (m j)) atTop atTop := by
  obtain ⟨grow,small⟩ := CirclePairedGDCost.of_ratio N m T
    (valid.mono fun j v => ⟨by omega,v.2.2⟩) ratio
  exact of_small N m T d η hη grow valid hd small

end CirclePairedGDTail
