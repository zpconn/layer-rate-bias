module

public import CircleSpectrum
public import CircleLayerRates
import all CircleSpectrum
import Mathlib.Tactic

/-! Positive alias sums for the two layer rates. As in `CircleSpectrum`,
the grid size is N=n+1. The series identities hold for every positive size;
they represent the odd circular-grid kernel at odd N≥3. -/

public section
noncomputable section
namespace CircleFiniteCoefficient
open CircleSpectrum Filter Topology Real

/-- Two-sided (k²−1)⁻² alias, with k=2(n+1)(j+1). -/
def aliasATerm (n j : ℕ) : ℝ := 2 * (offset n j)^2 / (1-offset n j)^2

/-- Two-sided k²/(k²−1)² alias at the same frequency. -/
def aliasBTerm (n j : ℕ) : ℝ := 2 * offset n j / (1-offset n j)^2

def aliasA (n : ℕ) : ℝ := ∑' j, aliasATerm n j
def aliasB (n : ℕ) : ℝ := ∑' j, aliasBTerm n j

private theorem rp_bounds (i : ℕ) : 0 < rp 2 i ∧ rp 2 i ≤ 1 := by
  unfold rp
  constructor
  · positivity
  · apply div_le_one_of_le₀ <;> nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg (i:ℝ)]

private theorem off_bounds (n j : ℕ) : 0 < offset n j ∧ offset n j ≤ 1/4 := by
  unfold offset
  constructor
  · exact div_pos (mul_pos (rp_bounds n).1 (rp_bounds j).1) (by norm_num)
  · have h := mul_le_mul (rp_bounds n).2 (rp_bounds j).2 (rp_bounds j).1.le (by norm_num : (0:ℝ) ≤ 1)
    linarith

private theorem aliasBTerm_bounds (n j : ℕ) : 0 < aliasBTerm n j ∧ aliasBTerm n j ≤ rp 2 j := by
  obtain ⟨hz, hu⟩ := off_bounds n j
  have hd : 1/2 ≤ (1-offset n j)^2 := by nlinarith [sq_nonneg (offset n j)]
  have hx : 4 * offset n j ≤ rp 2 j := by
    unfold offset
    nlinarith [mul_le_mul_of_nonneg_right (rp_bounds n).2 (rp_bounds j).1.le]
  unfold aliasBTerm
  constructor
  · exact div_pos (by positivity) (by linarith)
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (rp_bounds j).1.le]

private theorem aliasATerm_bounds (n j : ℕ) : 0 ≤ aliasATerm n j ∧ aliasATerm n j ≤ aliasBTerm n j := by
  obtain ⟨hz,hu⟩ := off_bounds n j
  constructor
  · unfold aliasATerm; positivity
  · unfold aliasATerm aliasBTerm
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right (show offset n j ≤ 1 by linarith) hz.le]

private theorem aliasB_summable (n : ℕ) : Summable (aliasBTerm n) := by
  have hs : HasSum (rp 2) (π^2/6) := by
    change HasSum (fun j : ℕ => 1/((j:ℝ)+1)^2) _
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  exact hs.summable.of_nonneg_of_le (fun j => (aliasBTerm_bounds n j).1.le)
    (fun j => (aliasBTerm_bounds n j).2)

private theorem aliasA_summable (n : ℕ) : Summable (aliasATerm n) :=
  (aliasB_summable n).of_nonneg_of_le (fun j => (aliasATerm_bounds n j).1)
    (fun j => (aliasATerm_bounds n j).2)

theorem aliasA_nonneg (n : ℕ) : 0 ≤ aliasA n := tsum_nonneg (fun j => (aliasATerm_bounds n j).1)

theorem aliasB_pos (n : ℕ) : 0 < aliasB n :=
  (aliasB_summable n).tsum_pos (fun j => (aliasBTerm_bounds n j).1.le) 0 (aliasBTerm_bounds n 0).1

/-- Split the normalized tangent alias mass into feature and hidden-gradient terms. -/
theorem tangent_alias_split (τ : ℝ) (n : ℕ) :
    U τ n = ((2+τ)*aliasA n + τ*aliasB n)/π^2 := by
  unfold U scaledU aliasA aliasB
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← ((aliasA_summable n).mul_left (2+τ)).tsum_add ((aliasB_summable n).mul_left τ),
    ← tsum_div_const]
  apply tsum_congr
  intro j
  unfold aliasATerm aliasBTerm offset
  ring

/-- Exact finite-series form of the existing interpolation weight. -/
theorem weight_exact (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    weight τ n = 1 / (1+aliasA n + τ/(2+τ)*aliasB n) := by
  rw [weight, k0, tangent_alias_split]
  have h : 0 < 2+τ := by linarith
  have hμ := aliasA_nonneg n
  have hν := aliasB_pos n
  have hn : 0 < 1+aliasA n+τ/(2+τ)*aliasB n := by positivity
  have hd : 0 < (2+τ)/π^2+((2+τ)*aliasA n+τ*aliasB n)/π^2 := by positivity
  field_simp [hn.ne', hd.ne', h.ne', Real.pi_ne_zero]
  ring

/-- The unscaled paired coefficient at every positive grid size. -/
theorem weight_difference (n : ℕ) :
    weight (1/2) n - weight 2 n =
      (3/10)*aliasB n / ((1+aliasA n+aliasB n/5)*(1+aliasA n+aliasB n/2)) := by
  rw [weight_exact _ (by norm_num) n, weight_exact _ (by norm_num) n]
  have ha := aliasA_nonneg n
  have hb := aliasB_pos n
  norm_num
  field_simp
  ring

theorem weight_difference_pos (n : ℕ) : 0 < weight (1/2) n - weight 2 n := by
  rw [weight_difference]
  have := aliasA_nonneg n
  have := aliasB_pos n
  positivity

/-- Exact reference contrast for arbitrary initial means, with both rates
using the very same population mean and grid mean. -/
theorem paired_reference_exact (n : ℕ) (population grid : ℝ) :
    CircleLayerRates.reference population grid (weight (1/2) n) -
    CircleLayerRates.reference population grid (weight 2 n) =
    ((3/10)*aliasB n / ((1+aliasA n+aliasB n/5)*(1+aliasA n+aliasB n/2))) * (1-grid) := by
  rw [CircleLayerRates.reference_difference, weight_difference]

/-- The slow-hidden reference wins exactly on seeds with initial grid mean below one. -/
theorem paired_reference_slow_wins_iff (n : ℕ) (population grid : ℝ) :
    CircleLayerRates.reference population grid (weight 2 n) <
    CircleLayerRates.reference population grid (weight (1/2) n) ↔ grid < 1 := by
  rw [← sub_pos, CircleLayerRates.reference_difference,
    mul_pos_iff_of_pos_left (weight_difference_pos n), sub_pos]

/-- The first finite-grid correction in the gradient alias B. -/
theorem aliasB_correction :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 * (((n:ℝ)+1)^2 * aliasB n - π^2/12))
      atTop (𝓝 (π^4/360)) := by
  let f (n j : ℕ) := rp 4 j / 8 * ((2-offset n j)/(1-offset n j)^2)
  have hid (n : ℕ) : ((n:ℝ)+1)^2 * (((n:ℝ)+1)^2 * aliasB n - π^2/12) =
      ∑' j, f n j := by
    have hz : π^2/12 = ∑' j, rp 2 j / 2 := by rw [tsum_div_const, rp_two_sum.tsum_eq]; ring
    rw [aliasB, ← tsum_mul_left, hz,
      ← ((aliasB_summable n).mul_left _).tsum_sub (rp_two_sum.summable.div_const 2),
      ← tsum_mul_left]
    apply tsum_congr
    intro j
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have hj : (j:ℝ)+1 ≠ 0 := by positivity
    have hd : 1-offset n j ≠ 0 := by linarith [(off_bounds n j).2]
    unfold f aliasBTerm
    field_simp [hd]
    unfold offset rp
    field_simp
    ring
  have hf (j : ℕ) : Tendsto (fun n => f n j) atTop (𝓝 (rp 4 j/4)) := by
    have h := offset_zero j
    unfold f
    convert (((tendsto_const_nhds (x := (2:ℝ))).sub h).div
      (((tendsto_const_nhds (x := (1:ℝ))).sub h).pow 2) (by norm_num)).const_mul (rp 4 j/8) using 1
    norm_num
    ring
  have hb (n j : ℕ) : ‖f n j‖ ≤ rp 4 j := by
    obtain ⟨hz,hu⟩ := off_bounds n j
    have hd : (1/2:ℝ) ≤ (1-offset n j)^2 := by nlinarith [sq_nonneg (offset n j)]
    have hr : 0 ≤ rp 4 j := by unfold rp; positivity
    have hp : 0 ≤ (2-offset n j)/(1-offset n j)^2 := div_nonneg (by linarith) (sq_nonneg _)
    have hq : (2-offset n j)/(1-offset n j)^2 ≤ 8 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    unfold f
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hp)]
    nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ rp 4 j/8 by positivity)]
  simp_rw [hid]
  have ht := tendsto_tsum_of_dominated_convergence rp_four_sum.summable hf (Eventually.of_forall hb)
  rw [tsum_div_const, rp_four_sum.tsum_eq] at ht
  convert ht using 2
  ring

/-- The summands in the frequency notation of the discrete-grid calculation. -/
theorem alias_terms_at_frequency (n j : ℕ) :
    let k := 2*((n:ℝ)+1)*((j:ℝ)+1)
    aliasATerm n j = 2/(k^2-1)^2 ∧ aliasBTerm n j = 2*k^2/(k^2-1)^2 := by
  dsimp only
  rw [aliasATerm, aliasBTerm, sub_offset]
  unfold offset rp
  constructor <;> field_simp <;> ring

/-- Increasing the hidden-layer rate strictly decreases the interpolation weight. -/
theorem weight_strict_decrease {τ σ : ℝ} (hτ : 0 ≤ τ) (h : τ < σ) (n : ℕ) :
    weight σ n < weight τ n := by
  have hσ : 0 ≤ σ := by linarith
  have ha := aliasA_nonneg n
  have hb := aliasB_pos n
  have ht : τ/(2+τ) < σ/(2+σ) :=
    (div_lt_div_iff₀ (by linarith) (by linarith)).mpr (by nlinarith)
  rw [weight_exact _ hσ, weight_exact _ hτ]
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith [mul_lt_mul_of_pos_right ht hb]

private theorem ratio_correction (t A B : ℕ → ℝ) (b d : ℝ)
    (hp : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 0))
    (ha : Tendsto (fun n => A n/t n) atTop (𝓝 0))
    (hb : Tendsto (fun n => B n/t n) atTop (𝓝 b))
    (hd : Tendsto (fun n => (B n/t n-b)/t n) atTop (𝓝 d)) :
    Tendsto (fun n => ((3/10)*(B n/t n)/((1+A n+B n/5)*(1+A n+B n/2))-3/10*b)/t n)
      atTop (𝓝 (3/10*(d-7/10*b^2))) := by
  let x := fun n => A n+B n/5
  let y := fun n => A n+B n/2
  have hx : Tendsto (fun n => x n/t n) atTop (𝓝 (b/5)) := by
    convert ha.add (hb.div_const 5) using 1
    · funext n; dsimp [x]; ring
    · simp
  have hy : Tendsto (fun n => y n/t n) atTop (𝓝 (b/2)) := by
    convert ha.add (hb.div_const 2) using 1
    · funext n; dsimp [y]; ring
    · simp
  have hx0 : Tendsto x atTop (𝓝 0) := by
    simpa [fun n => div_mul_cancel₀ (x n) (hp n).ne', Pi.mul_def] using hx.mul ht
  have hy0 : Tendsto y atTop (𝓝 0) := by
    simpa [fun n => div_mul_cancel₀ (y n) (hp n).ne', Pi.mul_def] using hy.mul ht
  have h1x : Tendsto (fun n => 1+x n) atTop (𝓝 1) := by simpa using hx0.const_add 1
  have h1y : Tendsto (fun n => 1+y n) atTop (𝓝 1) := by simpa using hy0.const_add 1
  have h := (((hd.sub (((hx.mul h1y).add hy).const_mul b)).const_mul (3/10 : ℝ)).div
    (h1x.mul h1y) (by norm_num : (1:ℝ)*1 ≠ 0))
  have h' : (3/10:ℝ)*(d-b*(b/5*1+b/2))/(1*1) = 3/10*(d-7/10*b^2) := by ring
  rw [← h']
  apply h.congr'
  filter_upwards [h1x.eventually_ne (by norm_num : (1:ℝ) ≠ 0), h1y.eventually_ne (by norm_num : (1:ℝ) ≠ 0)] with n hn kn
  change (3/10:ℝ)*((B n/t n-b)/t n-b*(x n/t n*(1+y n)+y n/t n))/((1+x n)*(1+y n)) = _
  rw [show 1+A n+B n/5=1+x n by dsimp [x]; ring,show 1+A n+B n/2=1+y n by dsimp [y]; ring]
  field_simp [hn,kn,(hp n).ne']
  ring

/-- Second-order coefficient for the actual existing `CircleSpectrum.weight`.
In the odd-grid model, N²(c_N−π²/40) → −π⁴/1600. -/
theorem coefficient_second_order :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 *
      (((n:ℝ)+1)^2 * (weight (1/2) n - weight 2 n) - π^2/40))
      atTop (𝓝 (-π^4/1600)) := by
  have hd : Tendsto (fun n => (aliasB n/rp 2 n - π^2/12)/rp 2 n) atTop (𝓝 (π^4/360)) := by
    simpa [rp, div_eq_mul_inv, mul_comm] using aliasB_correction
  have hb : Tendsto (fun n => aliasB n/rp 2 n) atTop (𝓝 (π^2/12)) := by
    have h := (hd.mul rp_two_zero).add_const (π^2/12)
    simpa [Pi.mul_def, fun n => div_mul_cancel₀ ((aliasB n/rp 2 n)-π^2/12) (rp_bounds n).1.ne'] using h
  have ha : Tendsto (fun n => aliasA n/rp 2 n) atTop (𝓝 0) := by
    have hid (n : ℕ) : aliasA n/rp 2 n = π^2/2 * scaledU 0 n := by
      calc
        aliasA n/rp 2 n = π^2/2 * (U 0 n /rp 2 n) := by
          rw [tangent_alias_split]; field_simp [Real.pi_ne_zero]; ring
        _ = _ := by simp [U, (rp_bounds n).1.ne']
    simp_rw [hid]
    simpa using (scaledU_limit 0 (by norm_num)).const_mul (π^2/2)
  have h := ratio_correction (rp 2) aliasA aliasB _ _ (fun n => (rp_bounds n).1) rp_two_zero ha hb hd
  convert h using 2
  · rw [weight_difference]
    unfold rp
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  · ring

end CircleFiniteCoefficient
