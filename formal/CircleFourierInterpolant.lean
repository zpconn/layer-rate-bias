module

public import CircleGridSpectrum
import all CircleGridSpectrum
import Mathlib.Tactic

/-! Fourier coefficients of the circle tangent-kernel interpolant for arbitrary grid data. -/
@[expose] public section
noncomputable section
namespace CircleFourierInterpolant
open Real MeasureTheory AddCircle Finset CircleGridSpectrum

abbrev Angle := AddCircle (π - -π)
local instance : Fact (0 < π - -π) := ⟨by linarith [pi_pos]⟩
variable {N : ℕ} [NeZero N]

private theorem shifted_coeff (τ : ℝ) (j : ZMod N) (k : ℤ) :
    fourierCoeff (fun x : Angle => periodicTangent τ (x-gridAngle j)) k =
      char ((-k:ℤ):ZMod N) j * (tangentCoeff τ k:ℂ) := by
  have fac (x : Angle) : fourier (-k) x = fourier (-k) (gridAngle j)*fourier (-k) (x-gridAngle j) := by
    have phase (u v : Angle) : fourier (-k) (u+v) = fourier (-k) u * fourier (-k) v := by
      simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]
    rw [← phase,add_sub_cancel]
  unfold fourierCoeff
  change (∫ x : Angle, fourier (-k) x * periodicTangent τ (x-gridAngle j) ∂haarAddCircle) = _
  calc
    _ = ∫ x : Angle, fourier (-k) (gridAngle j) *
        (fourier (-k) (x-gridAngle j)*periodicTangent τ (x-gridAngle j)) ∂haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only; rw [←mul_assoc,←fac]
    _ = _ := by
      rw [integral_const_mul,integral_sub_right_eq_self (fun x : Angle => fourier (-k) x*periodicTangent τ x)]
      rw [CircleGridSpectrum.sampled_fourier]
      exact congrArg (fun c : ℂ => char ((-k:ℤ):ZMod N) j*c) (periodicTangent_coeff τ k)

/-- The correction is a linear combination of translated tangent sections that interpolates
the given residual on the grid. Its continuous Fourier coefficient at every integer frequency
is the normalized discrete residual coefficient times the frequency's share of its alias sum. -/
theorem interpolation (hn : 3≤N) (ho : Odd N) {τ : ℝ} (lo : 1/2≤τ) (hi : τ≤2)
    (residual : ZMod N → ℂ) :
    ∃ a : ZMod N → ℂ,
      let correction := fun x : Angle => ∑ j : ZMod N, a j*periodicTangent τ (x-gridAngle j)
      (∀ i, correction (gridAngle i) = residual i) ∧
      ∀ k : ℤ, fourierCoeff correction k =
        (tangentCoeff τ k:ℂ)/(aliasValue (tangentCoeff τ) (k:ZMod N):ℂ)*
        (ZMod.dft residual (k:ZMod N)/(N:ℂ)) := by
  let d (r : ZMod N) := (aliasValue (tangentCoeff τ) r : ℂ)
  have dn (r : ZMod N) : d r ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le (by positivity) (tangent_gap hn ho τ lo hi r)))
  let v := ZMod.dft.symm (fun r => ZMod.dft residual r/d r)
  have spec (r : ZMod N) : ZMod.dft v r = ZMod.dft residual r/d r := by
    exact congrFun (ZMod.dft.apply_symm_apply _) r
  let a (j : ZMod N) := v j/(N:ℂ)
  refine ⟨a,?_,?_⟩
  · intro i
    simp_rw [←CircleGridSpectrum.gridAngle_sub]
    change (∑ j, v j/(N:ℂ)*periodicTangent τ (gridAngle (i-j))) = _
    rw [show (∑ j, v j/(N:ℂ)*periodicTangent τ (gridAngle (i-j))) =
      convolution (fun x => periodicTangent τ (gridAngle x)) v i by
      simp only [convolution,Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring]
    rw [CircleGridSpectrum.convolution_synthesis _ v _ (sampled_character_eigenvalue τ (by linarith) hi)]
    rw [CircleGridSpectrum.synthesis residual i]
    apply Finset.sum_congr rfl
    intro r _
    rw [spec r]
    change _ * (d r * _) = _
    field_simp [dn]
  · intro k
    let f (j : ZMod N) := fun x : Angle => a j*periodicTangent τ (x-gridAngle j)
    have cont (j : ZMod N) : Continuous (f j) := continuous_const.mul
      ((periodicTangent τ).continuous.comp (continuous_id.sub continuous_const))
    have eq : (fun x : Angle => ∑ j, a j*periodicTangent τ (x-gridAngle j)) = ∑ j, f j := by
      funext x; rw [Finset.sum_apply]
    rw [eq,fourierCoeff.sum _ f (fun j _ => (cont j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),Finset.sum_apply]
    have term (j : ZMod N) : fourierCoeff (f j) k =
        (tangentCoeff τ k:ℂ) / (N:ℂ) * (ZMod.stdAddChar (-(j*(k:ZMod N))) * v j) := by
      rw [show f j = fun x : Angle => a j*periodicTangent τ (x-gridAngle j) by rfl,
        fourierCoeff.const_mul,shifted_coeff]
      simp only [a,char,Int.cast_neg,neg_mul,mul_comm (k:ZMod N) j]
      ring
    simp_rw [term]
    rw [←Finset.mul_sum]
    change (tangentCoeff τ k:ℂ)/(N:ℂ) * ZMod.dft v (k:ZMod N) = _
    rw [spec]
    dsimp only [d]
    ring

/-- For an arbitrary continuous initial output and target, the mean of the
fitted kernel correction equals a single quadrature weight times the grid
deficit. The target is allowed to have different grid and population means. -/
theorem target_mean (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) {τ : ℝ}
    (lo : 1/2≤τ) (hi : τ≤2) (initial target : C(Angle,ℂ)) :
    ∃ a : ZMod (n+1) → ℂ,
      let correction := fun x : Angle => ∑ j : ZMod (n+1), a j*periodicTangent τ (x-gridAngle j)
      let deficit := (∑ j : ZMod (n+1), (target (gridAngle j)-initial (gridAngle j))) / (n+1:ℕ)
      (∀ j : ZMod (n+1), initial (gridAngle j)+correction (gridAngle j) = target (gridAngle j)) ∧
      (∫ x, correction x ∂haarAddCircle) = (CircleSpectrum.weight τ n:ℂ)*deficit := by
  let r := fun j : ZMod (n+1) => target (gridAngle j)-initial (gridAngle j)
  obtain ⟨a,fit,modes⟩ := interpolation hn ho lo hi r
  refine ⟨a,?_,?_⟩
  · intro j; rw [fit]; dsimp only [r]; ring
  · have zero := modes 0
    have w := weight_from_grid_alias n hn ho τ (by linarith) hi
    simp only [fourierCoeff,neg_zero,fourier_zero,one_smul,Int.cast_zero,
      ZMod.dft_apply_zero] at zero
    have hz : tangentCoeff τ 0 = CircleSpectrum.k0 τ := by
      simp [tangentCoeff,CircleSpectrum.ntkEven,CircleSpectrum.k0]
    simpa only [r,w,Complex.ofReal_div,hz] using zero

end CircleFourierInterpolant
