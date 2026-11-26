module

public import CircleSpectralPathLength
public import CircleKernelGD
import all CircleKernelGD
import all CircleSpectralPathLength
import all CircleKernelIdentification
import all CircleGridSpectrum
import all CircleSpectrum
import all CircleTangentDrift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The fourth Fourier projection and its exact population eigenvalue for
short-horizon fitting comparisons. -/
public section
noncomputable section
namespace CircleFourthEigen
open CircleGridSpectrum CircleSpectralPathLength CircleKernelIdentification CircleSpectrum
  CircleTangentDrift Real Finset Filter Topology

/-- Absolute convergence collapses a fixed residue class to its original
Fourier coefficient as the grid spacing tends to zero. -/
theorem general_alias_limit {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (a : ℤ→E) (ha : Summable (fun j => ‖a j‖)) (k : ℤ) :
    Tendsto (fun N : ℕ => ∑' j : ℤ, if (j:ZMod N)=(k:ZMod N) then a j else 0) atTop (𝓝 (a k)) := by
  let F (N : ℕ) (j : ℤ) := if (j:ZMod N)=(k:ZMod N) then a j else 0
  let f (j : ℤ) := if j=k then a j else 0
  have h (j : ℤ) : Tendsto (fun N => F N j) atTop (𝓝 (f j)) := by
    by_cases hj : j=k
    · simp [F,f,hj]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (j-k).natAbs] with N hN
      have hn : (j:ZMod N)≠(k:ZMod N) := by
        intro ht
        have hd : (N:ℤ) ∣ j-k := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simp [ht])
        obtain ⟨l,hl⟩ := hd
        have dl : N ∣ (j-k).natAbs := ⟨l.natAbs,by rw [hl,Int.natAbs_mul,Int.natAbs_natCast]⟩
        exact (not_le_of_gt hN) (Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr hj)) dl)
      simp [F,f,hn,hj]
  have ht := tendsto_tsum_of_dominated_convergence ha h (Eventually.of_forall fun N j => by
    dsimp [F]; split <;> simp)
  simpa [F,f,tsum_ite_eq'] using ht

theorem alias_limit (a : ℤ→ℝ) (ha : Summable (fun j => ‖a j‖)) (k : ℤ) :
    Tendsto (fun N : ℕ => aliasValue a (k:ZMod N)) atTop (𝓝 (a k)) := general_alias_limit a ha k

theorem complex_alias_limit (a : ℤ→ℂ) (ha : Summable (fun j => ‖a j‖)) (k : ℤ) :
    Tendsto (fun N : ℕ => ∑' j : ℤ, if (j:ZMod N)=(k:ZMod N) then a j else 0) atTop (𝓝 (a k)) :=
  general_alias_limit a ha k

theorem fourth_eigen_limit (τ : ℝ) (hτ : 0≤τ) (hu : τ≤2) :
    Tendsto (fun N : ℕ => aliasValue (tangentCoeff τ) (4:ZMod N)) atTop (𝓝 ((2+17*τ)/(225*π^2))) := by
  have h := alias_limit (tangentCoeff τ) (tangentCoeff_summable τ hτ hu).norm 4
  convert h using 2
  · simp
  · norm_num [tangentCoeff,ntkEven];ring

theorem fourth_eigen_lt : ∀ᶠ N : ℕ in atTop, aliasValue (tangentCoeff 1) (4:ZMod N) < (1:ℝ)/100 := by
  apply (fourth_eigen_limit 1 (by norm_num) (by norm_num)).eventually (eventually_lt_nhds ?_)
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith [sq_nonneg (π-3),pi_gt_three]

theorem fourth_eigen_lt_sixtieth (τ : ℝ) (hτ : 0≤τ) (hu : τ≤2) :
    ∀ᶠ N : ℕ in atTop, aliasValue (tangentCoeff τ) (4:ZMod N) < (1:ℝ)/60 := by
  apply (fourth_eigen_limit τ hτ hu).eventually (eventually_lt_nhds ?_)
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith [sq_nonneg (π-3.14),Real.pi_gt_d2]

/-- The same grid-size threshold works for every layer rate in the interval. -/
theorem fourth_eigen_uniform : ∀ᶠ N : ℕ in atTop, ∀ τ ∈ Set.Icc (0:ℝ) 2,
    aliasValue (tangentCoeff τ) (4:ZMod N)<1/60 := by
  filter_upwards [fourth_eigen_lt_sixtieth 2 (by norm_num) le_rfl] with N hN
  intro τ hτ
  have hs (σ : ℝ) (h : 0≤σ) (hu : σ≤2) : Summable (fun k : ℤ =>
      if (k:ZMod N)=4 then tangentCoeff σ k else 0) := by
    refine ((tangentCoeff_summable σ h hu).indicator {k : ℤ | (k:ZMod N)=4}).congr fun k => ?_
    simp [Set.indicator_apply]
  apply lt_of_le_of_lt _ hN
  apply (hs τ hτ.1 hτ.2).tsum_le_tsum _ (hs 2 (by norm_num) le_rfl)
  intro k
  by_cases hr : (k:ZMod N)=4
  · simp only [hr,ite_true,tangentCoeff,ntkEven]
    split
    · apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      exact add_le_add_right (mul_le_mul_of_nonneg_right hτ.2 (by positivity)) _
    · split <;> linarith [hτ.2]
  · simp [hr]

variable {N : ℕ} [NeZero N]

private def c (i : Fin N) := (char (4:ZMod N) (ZMod.finEquiv N i)).re

def fourthRow (N : ℕ) [NeZero N] := rowOp (c (N:=N))
theorem fourthRow_contract : ‖fourthRow N‖≤1 := rowOp_norm (NeZero.pos _) zero_le_one (fun i =>
  (Complex.abs_re_le_norm _).trans (by simp [char,AddChar.norm_apply]))

private theorem matrix_char (τ : ℝ) (hτ : 0≤τ) (hu : τ≤2) (i : Fin N) :
    (∑ j : Fin N, sampledMatrix τ i j*c j)/(N:ℝ)=eigen τ (4:ZMod N)*c i := by
  let a (s : ZMod N) : ℂ := if s=4 then 1 else 0
  have h := matrix_synth τ hτ hu a i
  simpa [synth,a,c,ite_mul,Finset.sum_ite_eq',Complex.re_ofReal_mul] using h

theorem fourthRow_gram (τ : ℝ) (hτ : 0≤τ) (hu : τ≤2) (v : EuclideanSpace ℝ (Fin N)) :
    fourthRow N (gramOp (sampledMatrix τ) v) = eigen τ (4:ZMod N)*fourthRow N v := by
  have hsym (i j : Fin N) : sampledMatrix τ i j=sampledMatrix τ j i := by simp [sampledMatrix_cartesian,cartesian_kernel_isotropic,abs_sub_comm]
  rw [fourthRow,rowOp_apply,rowOp_apply]
  simp_rw [gramOp_apply,←mul_div_assoc,Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm]
  have he (j : Fin N) : ∑ i : Fin N, c i*(sampledMatrix τ i j*v j)= (eigen τ (4:ZMod N)*c j*N)*v j := by
    rw [←(div_eq_iff (NeZero.ne (N:ℝ))).mp (matrix_char τ hτ hu j),Finset.sum_mul]
    apply sum_congr rfl; intro i _;rw [hsym i j];ring
  simp_rw [he]
  field_simp [NeZero.ne (N:ℝ),sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos N))]
  simp only [Finset.mul_sum]
  apply sum_congr rfl;intros;ring

theorem fourthRow_update_pow (t : ℕ) (v : EuclideanSpace ℝ (Fin N)) :
    fourthRow N (((CircleKernelGD.update N)^t) v)=(1-eigen 1 (4:ZMod N))^t*fourthRow N v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ',mul_apply_eq_comp]
    change fourthRow N (((CircleKernelGD.update N)^t) v - CircleKernelGD.gram N (((CircleKernelGD.update N)^t) v)) = _
    rw [map_sub,CircleKernelGD.gram,fourthRow_gram 1 (by norm_num) (by norm_num), ih,pow_succ']
    ring

/-- The projection is the real fourth DFT coefficient of the unscaled physical
residual when represented in the learner's Euclidean RMS coordinates. -/
theorem fourthRow_rms (v : Fin N→ℝ) : fourthRow N (rmsCoordinates v) = (normalizedCoeff v (4:ZMod N)).re := by
  rw [fourthRow,rowOp_rms,normalizedCoeff,ZMod.dft_apply,Complex.div_natCast_re,Complex.re_sum]
  congr 1
  rw [←CircleGridSpectrum.fin_sum]
  apply sum_congr rfl
  intro i _
  simp [c,char,smul_eq_mul,AddChar.map_neg_eq_conj,Complex.mul_re,mul_comm]

end CircleFourthEigen
