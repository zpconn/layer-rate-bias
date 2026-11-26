module

public import CircleWeightedDynamics
public import CirclePairedOrdering
import all CirclePairedCoefficient
import all CirclePairedOrdering
import all CircleScoreMargin
import all CircleResidualSpectrum
import all CircleComparison
import Mathlib.Tactic

/-! The measured difference is always the slow network minus the fast network
at the same update, from the same Gaussian weights. The probability bounds
below allow the seed space and its Gaussian law to vary with the grid. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDEndpoint
open MeasureTheory Real Filter Topology Set CircleEscapeBridge CircleFlowTracking
  CirclePairedCoefficient CirclePairedOrdering CircleWeightedDynamics

def contrast (N m T : ℕ) (η : ℝ) (z : Seed m) : ℝ :=
  learnerMean (1/2) η N z T - learnerMean 2 η N z T

abbrev gridWidth (n : ℕ) := (n+1)^32

def scaled (n : ℕ) (z : Seed (gridWidth n)) : ℝ :=
  ((n:ℝ)+1)^2 * contrast (n+1) (gridWidth n) (horizon ((n:ℝ)+1)) 1 z

def miss (n : ℕ) : Set (Seed (gridWidth n)) :=
  {z | scaled n z * score (n+1) (gridWidth n) z ≤ 0}

/-- The event needed to transfer the exact finite-grid coefficient to the
ordering and to the limiting coefficient. Both runs use the same event. -/
def Tracks (n : ℕ) : Prop :=
  ∃ G : Set (Seed (gridWidth n)), (seedLaw (gridWidth n)).real Gᶜ ≤ 2/√((n:ℝ)+1) ∧
    ∀ z ∈ G, |scaled n z - coefficient n * score (n+1) (gridWidth n) z|
      ≤ 10/((n:ℝ)+1)^(33/32:ℝ)

private theorem relaxed_error (n : ℕ) :
    10/((n:ℝ)+1)^(33/32:ℝ) ≤ 10/((n:ℝ)+1) := by
  have base : 1 ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have h := rpow_le_rpow_of_exponent_le base (show (1:ℝ) ≤ 33/32 by norm_num)
  rw [rpow_one] at h
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h

private theorem sqrt_inv_tends : Tendsto (fun n : ℕ => (√((n:ℝ)+1))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (CircleComparison.grown id tendsto_id))

theorem sign_of_tracks :
    ∀ᶠ n : ℕ in atTop, Tracks n →
      (seedLaw (gridWidth n)).real (miss n) ≤
        (2+2*CircleScoreMargin.densityBound)/√((n:ℝ)+1) := by
  have small := sqrt_inv_tends.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)
  have sep := (sqrt_inv_tends.const_mul 10).eventually_lt_const
    (show (10:ℝ)*0 < π^2/80 by rw [mul_zero]; positivity)
  filter_upwards [small, sep, coefficient_eventually] with n hsmall hsep hlo h
  obtain ⟨G,bad,inside⟩ := h
  let x := (n:ℝ)+1
  have xp : 0 < x := by dsimp [x]; positivity
  have sp : 0 < √x := sqrt_pos.2 xp
  have ss : √x * √x = x := mul_self_sqrt xp.le
  have cut : 10/x < coefficient n * (√x)⁻¹ := by
    have hs : 10 / √x < coefficient n := by simpa only [div_eq_mul_inv] using hsep.trans_le hlo
    calc
      10/x = (10/√x)/√x := by rw [div_div,ss]
      _ < coefficient n/√x := div_lt_div_of_pos_right hs sp
      _ = _ := div_eq_mul_inv ..
  have mark := CircleScoreMargin.sign_miss_bound (n+1) (gridWidth n) (scaled n)
    (coefficient n) ((√x)⁻¹) (coefficient_pos n) (inv_nonneg.mpr sp.le) hsmall.le
  simp_rw [←score_eq] at mark
  have sub : {z | coefficient n * (√x)⁻¹ ≤ |scaled n z-coefficient n*score (n+1) (gridWidth n) z|} ⊆ Gᶜ := by
    intro z hz hzG
    exact (not_lt_of_ge hz) (((inside z hzG).trans (relaxed_error n)).trans_lt cut)
  apply mark.trans
  calc
    _ ≤ 2/√((n:ℝ)+1) + 2*(√x)⁻¹*CircleScoreMargin.densityBound :=
      add_le_add ((measureReal_mono sub).trans bad) le_rfl
    _ = _ := by dsimp only [x]; ring

private theorem square_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) {ε : ℝ} (hp : 0<ε) :
    μ.real {z | ε ≤ |f z|} ≤ (lpNorm f 2 μ)^2 / ε^2 := by
  have mark := mul_meas_ge_le_integral_of_nonneg (μ:=μ) (ae_of_all _ fun z => sq_nonneg (f z))
    hf.integrable_sq (ε^2)
  have count := measureReal_mono (μ:=μ) (s₁:={z | ε ≤ |f z|}) (s₂:={z | ε^2 ≤ f z^2})
    (fun z hz => (pow_le_pow_left₀ hp.le hz 2).trans_eq (sq_abs _))
  have integ : (lpNorm f 2 μ)^2=∫ z, f z^2 ∂μ := by
    rw [←rms_of_mem _ hf, sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  rw [integ]
  exact count.trans ((le_div_iff₀ (sq_pos_of_pos hp)).mpr (by linarith only [mark]))

private theorem limit_bound (n : ℕ) (hn : 3≤n+1) (ε : ℝ) (he : 0<ε)
    (room : 10/((n:ℝ)+1) < ε/2) (h : Tracks n) :
    (seedLaw (gridWidth n)).real {z | ε ≤ |scaled n z - (π^2/40)*score (n+1) (gridWidth n) z|} ≤
      2/√((n:ℝ)+1) + (|coefficient n-π^2/40| * CircleResidualSpectrum.modeConstant)^2/(ε/2)^2 := by
  let μ := seedLaw (gridWidth n)
  let X := score (n+1) (gridWidth n)
  let d := coefficient n-π^2/40
  obtain ⟨G,bad,inside⟩ := h
  have parts : {z | ε ≤ |scaled n z - (π^2/40)*X z|} ⊆ Gᶜ ∪ {z | ε/2 ≤ |(d • X) z|} := by
    intro z hz
    by_cases hg : z ∈ G
    · right
      have tri := abs_add_le (scaled n z-coefficient n*X z) (d*X z)
      have iden : scaled n z-coefficient n*X z + d*X z = scaled n z-(π^2/40)*X z := by dsimp [d];ring
      rw [iden] at tri
      change ε ≤ _ at hz
      change ε/2 ≤ |d * X z|
      have er : |scaled n z-coefficient n*X z| < ε/2 :=
        ((inside z hg).trans (relaxed_error n)).trans_lt room
      linarith
    · exact Or.inl hg
  have hx := score_bound (N:=n+1) (m:=gridWidth n) hn (Nat.pow_pos (Nat.succ_pos n))
  have hX : MemLp X 2 μ := hx.1
  have tail := square_tail μ (hX.const_smul d) (half_pos he)
  have upper : lpNorm (d • X) 2 μ ≤ |d| * CircleResidualSpectrum.modeConstant := by
    rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
  exact (measureReal_mono parts).trans ((measureReal_union_le _ _).trans
    (add_le_add bad (tail.trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ lpNorm_nonneg upper 2) (sq_nonneg _)))))

/-- Convergence in probability on the varying product Gaussian spaces.
Every fixed accuracy threshold has vanishing exceedance probability. -/
theorem prediction_of_tracks (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (track : ∀ᶠ i in atTop, Tracks (n i)) (ε : ℝ) (he : 0<ε) :
    Tendsto (fun i => (seedLaw (gridWidth (n i))).real
      {z | ε ≤ |scaled (n i) z - (π^2/40)*score (n i+1) (gridWidth (n i)) z|}) atTop (𝓝 0) := by
  have rc : Tendsto (fun i => 10/((n i:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (CircleComparison.grown n grow)).const_mul (10:ℝ)
  have sc : Tendsto (fun i => 2/√((n i:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using (sqrt_inv_tends.comp grow).const_mul (2:ℝ)
  have hc : Tendsto (fun i => |coefficient (n i)-π^2/40| * CircleResidualSpectrum.modeConstant)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun i => coefficient (n i) - π^2/40) atTop (𝓝 (0:ℝ)) := by
      have hlim : Tendsto (fun i => coefficient (n i)) atTop (𝓝 (π^2/40)) :=
        CircleLayerRates.coefficient_limit.comp grow
      have hsub := hlim.sub (tendsto_const_nhds (x:=π^2/40))
      simpa only [sub_self] using hsub
    simpa only [abs_zero, zero_mul] using h0.abs.mul_const CircleResidualSpectrum.modeConstant
  have ub := sc.add ((hc.pow 2).div_const ((ε/2)^2))
  apply squeeze_zero' (.of_forall fun _ => measureReal_nonneg)
    (g:=fun i => 2/√((n i:ℝ)+1) + (|coefficient (n i)-π^2/40| * CircleResidualSpectrum.modeConstant)^2/(ε/2)^2)
  · filter_upwards [track, grow.eventually_ge_atTop 2, rc.eventually_lt_const (half_pos he)] with i hi hn room
    exact limit_bound _ (by omega) ε he room hi
  · simpa using ub

end CirclePairedGDEndpoint
