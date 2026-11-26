module

public import CircleEscape
import all CircleEscape
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-! First and second moments of real projections on the uniform circle grid. -/
public section
noncomputable section
namespace CircleGridMoments
open CircleEscape
open scoped ComplexConjugate

private theorem harmonic (N k : ℕ) (hk : 0 < k) (hN : k < N) :
    ∑ i : Fin N, gridPoint N i ^ k = 0 := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  have prim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp _ (by omega)
  have grid (i : Fin N) : gridPoint N i = ζ ^ (i:ℕ) := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have eq : (i.val : ℂ) * (2 * Real.pi * Complex.I / N) =
        (((2*Real.pi/(N:ℝ))*(i:ℕ):ℝ):ℂ) * Complex.I := by push_cast; ring
    rw [eq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;> simp only [gridPoint, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring
  simp_rw [grid, ← pow_mul, Nat.mul_comm _ k, pow_mul]
  rw [Fin.sum_univ_eq_sum_range]
  have g := geom_sum_mul (ζ^k) N
  rw [← pow_mul, Nat.mul_comm k N, pow_mul, prim.pow_eq_one, one_pow, sub_self] at g
  exact (mul_eq_zero.mp g).resolve_right
    (sub_ne_zero.mpr (prim.pow_ne_one_of_pos_of_lt hk.ne' hN))

theorem projection_sum (N : ℕ) (h : 3 ≤ N) (w : ℂ) :
    ∑ i : Fin N, inner ℝ w (gridPoint N i) = 0 := by
  have g : ∑ i : Fin N, gridPoint N i = 0 := by simpa using harmonic N 1 (by decide) (by omega)
  rw [← inner_sum, g, inner_zero_right]

theorem projection_sq_sum (N : ℕ) (h : 3 ≤ N) (w : ℂ) :
    ∑ i : Fin N, (inner ℝ w (gridPoint N i))^2 = (N:ℝ) * ‖w‖^2 / 2 := by
  let u (i : Fin N) := gridPoint N i * conj w
  have sqr (i : Fin N) : (inner ℝ w (gridPoint N i))^2 =
      ‖w‖^2 / 2 + ((u i)^2).re / 2 := by
    have hn : ‖u i‖ = ‖w‖ := by simp [u, grid_norm]
    have hi : inner ℝ w (gridPoint N i) = (u i).re := by rw [Complex.inner]
    have scalar (v : ℂ) : v.re^2 = ‖v‖^2 / 2 + (v^2).re / 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, sq v, Complex.mul_re]
      ring
    rw [hi, ← hn]
    exact scalar (u i)
  have sum2 : ∑ i : Fin N, (u i)^2 = 0 := by
    simp only [u, mul_pow, ← Finset.sum_mul, harmonic N 2 (by decide) (by omega), zero_mul]
  have realSum : ∑ i : Fin N, ((u i)^2).re = 0 := by
    simpa using congrArg Complex.re sum2
  simp_rw [sqr]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, realSum, zero_div, add_zero]
  simp

end CircleGridMoments
