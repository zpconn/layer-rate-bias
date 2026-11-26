module

public import CircleKernelIdentification
public import CircleTangentDrift
public import CircleSpectrum
import all CircleTangentDrift
import all CircleSpectrum
import all CircleKernelIdentification
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! Circulant grid convolution for the circle kernel. Each discrete Fourier
character sees the sum of all continuum coefficients of its residue. -/

public section
noncomputable section
namespace CircleGridSpectrum
open CircleSpectrum Real Finset Filter

def tangentCoeff (τ : ℝ) (k : ℤ) : ℝ :=
  if Even k then ntkEven τ k else if k.natAbs=1 then (1+τ)/8 else 0

theorem tangentCoeff_nonneg {τ : ℝ} (hτ : 0≤τ) (k : ℤ) : 0≤tangentCoeff τ k := by
  unfold tangentCoeff ntkEven
  split
  · exact div_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · split <;> positivity

private theorem abs_large {k : ℤ} (h : k ≤ -2 ∨ 2 ≤ k) : 4 ≤ (k:ℝ)^2 := by
  rcases h with h|h
  · have h' : (k:ℝ) ≤ -2 := by exact_mod_cast h
    nlinarith [mul_nonneg (show 0≤-(k:ℝ)-2 by linarith) (show 0≤-(k:ℝ)+2 by linarith)]
  · have h' : (2:ℝ) ≤ k := by exact_mod_cast h
    nlinarith [mul_nonneg (show 0≤(k:ℝ)-2 by linarith) (show 0≤(k:ℝ)+2 by linarith)]

theorem tangentCoeff_summable (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) : Summable (tangentCoeff τ) := by
  have hd := (Real.summable_one_div_int_pow.mpr (by decide : 1<2)).mul_left (16/π^2)
  apply hd.of_norm_bounded_eventually
  filter_upwards [(Finset.Icc (-1:ℤ) 1).finite_toSet.compl_mem_cofinite] with k hk
  have hk' : ¬ (-1≤k ∧ k≤1) := by simpa using hk
  have hz := abs_large (show k≤ -2 ∨ 2≤k by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (tangentCoeff_nonneg hτ k)]
  by_cases he : Even k
  · simp only [tangentCoeff, he, ite_true, ntkEven]
    have hn : 2+τ*(1+(k:ℝ)^2) ≤ 4*(k:ℝ)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hτ' (show 0≤1+(k:ℝ)^2 by positivity)]
    have hz1 : 0<(k:ℝ)^2-1 := by linarith
    have hdiv : (0:ℝ)<π^2*((k:ℝ)^2-1)^2 := by positivity
    rw [show 16/π^2*(1/(k:ℝ)^2) = 16/(π^2*(k:ℝ)^2) by ring]
    apply (div_le_div_iff₀ hdiv (mul_pos (sq_pos_of_pos pi_pos) (by linarith : 0<(k:ℝ)^2))).2
    have hh : (2+τ*(1+(k:ℝ)^2))*(k:ℝ)^2 ≤ 16*((k:ℝ)^2-1)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg (k:ℝ)),
        mul_nonneg (show 0≤(k:ℝ)^2-4 by linarith) (sq_nonneg (k:ℝ))]
    linarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg π)]
  · have ho : k.natAbs ≠ 1 := by omega
    simp only [tangentCoeff, he, ho, ite_false]
    positivity

variable {N : ℕ} [NeZero N]

def char (r i : ZMod N) : ℂ := ZMod.stdAddChar (r*i)
def series (a : ℤ → ℂ) (i : ZMod N) : ℂ := ∑' k : ℤ, a k*char (k:ZMod N) i
def convolution (K f : ZMod N → ℂ) (i : ZMod N) : ℂ :=
  (∑ j : ZMod N, K (i-j)*f j)/(N:ℂ)
def aliasValue (a : ℤ → ℝ) (r : ZMod N) : ℝ :=
  ∑' k : ℤ, if (k:ZMod N)=r then a k else 0

private theorem char_mean (s : ZMod N) :
    (∑ j : ZMod N, char s j)/(N:ℂ) = if s=0 then 1 else 0 := by
  by_cases hs : s=0
  · simp [hs,char,AddChar.map_zero_eq_one,ZMod.card,NeZero.ne (N:ℂ)]
  · have hh : ∑ j : ZMod N, ZMod.stdAddChar (s*j) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hs)
    simp [hs,char,hh]

/-- Diagonalization of the normalized convolution on every residue for any
absolutely summable complex Fourier series. -/
theorem character_eigenvalue (a : ℤ → ℂ) (ha : Summable (fun k => ‖a k‖)) (r i : ZMod N) :
    convolution (series a) (char r) i =
      (∑' k : ℤ, if (k:ZMod N)=r then a k else 0)*char r i := by
  have hsum (j : ZMod N) : Summable (fun k : ℤ => a k*char (k:ZMod N) (i-j)*char r j) :=
    ha.of_norm_bounded (fun k => by simp [char,AddChar.norm_apply])
  have phase (k : ℤ) (j : ZMod N) :
      char (k:ZMod N) (i-j) * char r j = char (k:ZMod N) i * char (r-(k:ZMod N)) j := by
    unfold char
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold convolution series
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun j _ => hsum j), div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro k
  simp_rw [mul_assoc (a k),phase,←mul_assoc (a k)]
  rw [← Finset.mul_sum, mul_assoc, ←div_eq_mul_inv, char_mean]
  by_cases hk : (k:ZMod N)=r
  · simp [hk]
  · simp [hk,sub_ne_zero.mpr (Ne.symm hk)]

private theorem even_mode_lower {τ : ℝ} (hτ : 0≤τ) {k : ℤ} (he : Even k) (hn : k≠0) :
    τ/(π^2*(k:ℝ)^2) ≤ tangentCoeff τ k := by
  have hk : k≤ -2 ∨ 2≤k := by rcases he with ⟨j,hj⟩; omega
  have hz := abs_large hk
  have hz1 : 0<(k:ℝ)^2-1 := by linarith
  have hz0 : 0<(k:ℝ)^2 := by linarith
  simp only [tangentCoeff,he,ite_true,ntkEven]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have h : τ*((k:ℝ)^2-1)^2 ≤ (2+τ*(1+(k:ℝ)^2))*(k:ℝ)^2 := by
    nlinarith [mul_nonneg hτ (show 0≤(k:ℝ)^2-1 by linarith)]
  linarith only [mul_le_mul_of_nonneg_left h (sq_nonneg π)]

private theorem reciprocal_pair {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    8/(x+y)^2 ≤ 1/x^2 + 1/y^2 := by
  have hh := mul_nonneg (sq_nonneg (x-y)) (show 0≤x^2+4*x*y+y^2 by positivity)
  field_simp
  nlinarith only [hh]

private theorem even_representative (hN : Odd N) (r : ZMod N) (hr : r≠0) :
    ∃ j : ℕ, 0<j ∧ j<2*N ∧ Even j ∧ (j:ZMod N)=r := by
  have hv := r.val_lt
  have hpos : 0<r.val := by
    by_contra! h
    apply hr
    rw [←ZMod.natCast_zmod_val r, show r.val=0 by omega, Nat.cast_zero]
  by_cases he : Even r.val
  · exact ⟨r.val,hpos,by omega,he,ZMod.natCast_zmod_val r⟩
  · refine ⟨r.val+N,by omega,by omega,(Nat.not_even_iff_odd.mp he).add_odd hN,?_⟩
    simp

/-- Each odd-grid residue has alias weight at least the shared gap used in
the fitted-flow theorem. In nonzero residues the two even representatives
are distinct, have opposite signs, and both contribute. -/
theorem tangent_gap (hN : 3≤N) (hodd : Odd N) (τ : ℝ) (hτ : 1/2≤τ) (hτ' : τ≤2)
    (r : ZMod N) : 1/(π*N)^2 ≤ aliasValue (tangentCoeff τ) r := by
  let a := tangentCoeff τ
  let f (k : ℤ) : ℝ := if (k:ZMod N)=r then a k else 0
  have ht : 0≤τ := by linarith
  have ha := tangentCoeff_summable τ ht hτ'
  have hf : Summable f := by
    refine (ha.indicator {k : ℤ | (k:ZMod N)=r}).congr fun k => ?_
    simp [Set.indicator_apply,f,a]
  have hpos (k : ℤ) : 0≤f k := by
    dsimp only [f,a]
    split <;> simp_all only [tangentCoeff_nonneg ht,le_refl]
  change _ ≤ ∑' k, f k
  have hn : (3:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  by_cases hr : r=0
  · have hsum := hf.le_tsum 0 (fun j _ => hpos j)
    apply le_trans _ hsum
    simp [f,a,tangentCoeff,hr,ntkEven]
    rw [←one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos pi_pos hn0)) (sq_pos_of_pos pi_pos)).2
    have hnn : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ (by linarith)
    have hc : (1:ℝ) ≤ (2+τ)*(N:ℝ)^2 := one_le_mul_of_one_le_of_one_le (by linarith) hnn
    linarith only [mul_le_mul_of_nonneg_left hc (sq_nonneg π)]
  · obtain ⟨j,hj,hjN,he,hjr⟩ := even_representative hodd r hr
    let q : ℤ := (j:ℤ)-2*N
    have hneg : q<0 := by dsimp [q]; omega
    have hji : (0:ℤ)<j := by exact_mod_cast hj
    have hqer : (q:ZMod N)=r := by simp [q,hjr]
    have hje : Even (j:ℤ) := by obtain ⟨a,ha⟩ := he; exact ⟨a,by exact_mod_cast ha⟩
    have hqe : Even q := by
      obtain ⟨x,hx⟩ := hje
      exact ⟨x-N,by dsimp [q]; omega⟩
    have hs := hf.sum_le_tsum ({(j:ℤ),q}: Finset ℤ) (fun k _ => hpos k)
    rw [Finset.sum_pair (by omega : (j:ℤ)≠q)] at hs
    simp only [f,Int.cast_natCast,hjr,hqer,ite_true,a] at hs
    apply le_trans _ hs
    have h1 := even_mode_lower ht hje hji.ne'
    have h2 := even_mode_lower ht hqe hneg.ne
    have hj0 : (0:ℝ)<j := by exact_mod_cast hj
    have hq0 : (0:ℝ)< -(q:ℝ) := by exact_mod_cast (by omega : (0:ℤ)< -q)
    have hh := reciprocal_pair hj0 hq0
    have heq : (j:ℝ)+ -(q:ℝ)=2*(N:ℝ) := by dsimp [q]; push_cast; ring
    rw [heq,neg_sq] at hh
    simp only [Int.cast_natCast] at h1
    apply le_trans _ (add_le_add h1 h2)
    have heq' : 1/(π*(N:ℝ))^2 = (1/2/π^2)*(8/(2*(N:ℝ))^2) := by ring
    rw [heq']
    calc
      _ ≤ (τ/π^2)*(1/(j:ℝ)^2+1/(q:ℝ)^2) := by gcongr
      _ = _ := by ring

theorem tangent_eigenvalue (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (r i : ZMod N) :
    convolution (series (fun k => (tangentCoeff τ k:ℂ))) (char r) i =
      (aliasValue (tangentCoeff τ) r:ℂ)*char r i := by
  have h := (tangentCoeff_summable τ hτ hτ').norm
  rw [character_eigenvalue _ (by simpa using h),aliasValue,Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro k
  split <;> simp_all

open CircleKernelIdentification
local instance hp : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩

/-- The actual polar tangent-kernel integral on the period, extended
continuously across its seam using the even angular distance. -/
def periodicTangent (τ : ℝ) : C(AddCircle (π - -π), ℂ) where
  toFun := AddCircle.liftIoc (π - -π) (-π) (fun x => (polarNTK τ |x| : ℂ))
  continuous_toFun := by
    apply AddCircle.liftIoc_continuous
    · simp
    · have hc : Continuous (fun x : ℝ => (distanceFormula τ |x| : ℂ)) := by
        unfold distanceFormula
        fun_prop
      apply hc.continuousOn.congr
      intro x hx
      have hu : x ≤ π := by simpa using hx.2
      exact congrArg Complex.ofReal (distanceFormula_agrees τ (abs_le.mpr ⟨hx.1, hu⟩)).symm

theorem periodicTangent_coeff (τ : ℝ) (k : ℤ) :
    fourierCoeff (periodicTangent τ) k = (tangentCoeff τ k:ℂ) := by
  change tangentFourier τ k = _
  exact tangentFourier_piecewise τ k

def gridAngle (i : ZMod N) : AddCircle (π- -π) := ((π- -π)*(i.val:ℝ)/N : ℝ)

private theorem sampled_fourier (k : ℤ) (i : ZMod N) :
    fourier k (gridAngle i) = char (k:ZMod N) i := by
  have hn : (N:ℂ) ≠ 0 := NeZero.ne _
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  rw [gridAngle, fourier_coe_apply]
  unfold char
  rw [show (k:ZMod N)*i = ((k*(i.val:ℤ):ℤ):ZMod N) by simp, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- Pointwise reconstruction identifies the actual sampled angular kernel
with its absolutely convergent series, before applying the discrete transform. -/
theorem sampled_tangent_eq_series (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (i : ZMod N) :
    periodicTangent τ (gridAngle i) = series (fun k => (tangentCoeff τ k:ℂ)) i := by
  have h : Summable (fourierCoeff (periodicTangent τ)) := by
    exact (Complex.ofRealCLM.summable (tangentCoeff_summable τ hτ hτ')).congr fun k =>
      (periodicTangent_coeff τ k).symm
  have hh := (has_pointwise_sum_fourier_series_of_summable h (gridAngle i)).tsum_eq
  simpa only [series,←sampled_fourier,periodicTangent_coeff,smul_eq_mul] using hh.symm

theorem sampled_character_eigenvalue (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (r i : ZMod N) :
    convolution (fun d => periodicTangent τ (gridAngle d)) (char r) i =
      (aliasValue (tangentCoeff τ) r:ℂ)*char r i := by
  simpa only [sampled_tangent_eq_series τ hτ hτ'] using tangent_eigenvalue τ hτ hτ' r i

open scoped ComplexConjugate

private theorem synthesis (v : ZMod N → ℂ) (i : ZMod N) :
    v i = ∑ r : ZMod N, (ZMod.dft v r / (N:ℂ))*char r i := by
  calc
    _ = ZMod.dft.symm (ZMod.dft v) i := congrFun (ZMod.dft.symm_apply_apply v).symm i
    _ = _ := by
      rw [ZMod.invDFT_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [smul_eq_mul,char]
      ring

private theorem convolution_synthesis (K v : ZMod N → ℂ) (d : ZMod N → ℝ)
    (hd : ∀ r i, convolution K (char r) i = (d r:ℂ)*char r i) (i : ZMod N) :
    convolution K v i = ∑ r : ZMod N, (ZMod.dft v r/(N:ℂ))*((d r:ℂ)*char r i) := by
  calc
    _ = (∑ j : ZMod N, K (i-j)*(∑ r : ZMod N,(ZMod.dft v r/(N:ℂ))*char r j))/N := by
      unfold convolution
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [←synthesis v j]
    _ = ∑ r : ZMod N, (ZMod.dft v r/(N:ℂ))*convolution K (char r) i := by
      simp only [convolution,Finset.mul_sum]
      rw [Finset.sum_comm,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      rw [←mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp_rw [hd]

private theorem adjoint_character_sum (v : ZMod N → ℂ) (r : ZMod N) :
    ∑ i : ZMod N, conj (v i)*char r i = conj (ZMod.dft v r) := by
  rw [ZMod.dft_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul,map_mul,←AddChar.map_neg_eq_conj,neg_neg,char]
  rw [mul_comm i r, mul_comm]

/-- Fourier inversion turns a real lower bound on every convolution
eigenvalue into an inequality for every complex test vector. -/
theorem rayleigh_of_character_gap (K v : ZMod N → ℂ) (d : ZMod N → ℝ) (g : ℝ)
    (hd : ∀ r i, convolution K (char r) i = (d r:ℂ)*char r i) (hg : ∀ r, g≤d r) :
    g*(∑ i, ‖v i‖^2) ≤ (∑ i : ZMod N, conj (v i)*convolution K v i).re := by
  let a (r : ZMod N) := ZMod.dft v r/(N:ℂ)
  have diff (i : ZMod N) : convolution K v i - (g:ℂ)*v i =
      ∑ r : ZMod N, (d r-g:ℝ)*a r*char r i := by
    rw [convolution_synthesis K v d hd i, synthesis v i, Finset.mul_sum, ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [a]
    push_cast
    ring
  have eqn : (∑ i : ZMod N, conj (v i)*(convolution K v i-(g:ℂ)*v i)) =
      (↑(∑ r : ZMod N, (d r-g)*‖ZMod.dft v r‖^2/(N:ℝ)) : ℂ) := by
    simp_rw [diff,Finset.mul_sum]
    rw [Finset.sum_comm,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = (d r-g:ℝ)*a r*(∑ i : ZMod N, conj (v i)*char r i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [adjoint_character_sum]
        dsimp [a]
        push_cast
        rw [←Complex.conj_mul']
        ring
  have nonneg : 0≤(∑ i : ZMod N, conj (v i)*(convolution K v i-(g:ℂ)*v i)).re := by
    rw [eqn,Complex.ofReal_re]
    exact Finset.sum_nonneg fun r _ => div_nonneg (mul_nonneg (sub_nonneg.mpr (hg r))
      (sq_nonneg _)) (Nat.cast_nonneg _)
  have idn (i : ZMod N) : conj (v i)*((g:ℂ)*v i) = (↑(g*‖v i‖^2):ℂ) := by
    rw [mul_left_comm,Complex.conj_mul']; push_cast; rfl
  simp only [mul_sub,idn, Finset.sum_sub_distrib,←Complex.ofReal_sum,Complex.sub_re,
    Complex.ofReal_re,←Finset.mul_sum] at nonneg
  linarith

/-- Coercivity of the actual polar grid operator, valid for all complex
vectors and hence in particular all real residuals. Both sides use the
same unnormalized sum in the quadratic form. -/
theorem sampled_tangent_rayleigh (hN : 3≤N) (hodd : Odd N) (τ : ℝ)
    (hτ : 1/2≤τ) (hτ' : τ≤2) (v : ZMod N → ℂ) :
    (1/(π*N)^2)*(∑ i, ‖v i‖^2) ≤
      (∑ i : ZMod N, conj (v i)*convolution (fun x => periodicTangent τ (gridAngle x)) v i).re :=
  rayleigh_of_character_gap _ v _ _ (sampled_character_eigenvalue τ (by linarith) hτ')
    (tangent_gap hN hodd τ hτ hτ')

/-- Real quadratic-form version in the normalization of the training residual. -/
theorem sampled_tangent_real_rayleigh (hN : 3≤N) (hodd : Odd N) (τ : ℝ)
    (hτ : 1/2≤τ) (hτ' : τ≤2) (v : ZMod N → ℝ) :
    (1/(π*N)^2)*(∑ i, (v i)^2) ≤
      ∑ i : ZMod N, v i*((∑ j : ZMod N, (periodicTangent τ (gridAngle (i-j))).re*v j)/N) := by
  have h := sampled_tangent_rayleigh hN hodd τ hτ hτ' (fun i => (v i:ℂ))
  have hc (z : ℂ) : (z/(N:ℂ)).re = z.re/(N:ℝ) := by
    simp
  simpa only [convolution,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.re_sum,
    Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
    sub_zero,hc] using h

omit [NeZero N] in
/-- On an odd grid, the entire constant-mode alias sum consists of zero and the
two reflected streams at positive multiples of 2N. -/
theorem constant_alias_eq (hN : 3≤N) (ho : Odd N) (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) :
    aliasValue (tangentCoeff τ) (0:ZMod N) =
      k0 τ + ∑' j : ℕ, 2*ntkEven τ (2*(N:ℝ)*((j:ℝ)+1)) := by
  let f (k : ℤ) : ℝ := if (k:ZMod N)=0 then tangentCoeff τ k else 0
  let g (j : ℤ) : ℤ := 2*(N:ℤ)*j
  let F (j : ℤ) : ℝ := ntkEven τ (2*(N:ℝ)*(j:ℝ))
  have hni : (0:ℤ)<N := by exact_mod_cast (by omega : 0<N)
  have hg : Function.Injective g := mul_right_injective₀ (by positivity)
  have hf : Summable f := by
    refine ((tangentCoeff_summable τ hτ hτ').indicator {k : ℤ | (k:ZMod N)=0}).congr fun k => ?_
    simp [Set.indicator_apply,f]
  have hno : ¬Even (N:ℤ) := by
    rcases ho with ⟨u,h⟩
    rw [h]
    push_cast
    rintro ⟨k,hk⟩
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro k hk
    change f k ≠ 0 at hk
    have hd : (k:ZMod N)=0 := by
      by_contra h
      exact hk (by simp [f,h])
    obtain ⟨l,hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k N).mp hd
    have he : Even k := by
      by_contra h
      have hd1 : k.natAbs ≠ 1 := by
        rw [hl,Int.natAbs_mul,Int.natAbs_natCast]
        intro h1
        have hh := Nat.eq_one_of_dvd_one (show N ∣ 1 from ⟨_,h1.symm⟩)
        omega
      exact hk (by simp [f,hd,tangentCoeff,h,hd1])
    obtain ⟨z,hz⟩ := (Int.even_mul.mp (hl ▸ he)).resolve_left hno
    exact ⟨z,by dsimp [g]; rw [hl,hz]; ring⟩
  have hval (j : ℤ) : f (g j)=F j := by
    have he : Even (g j) := ⟨(N:ℤ)*j,by dsimp [g]; ring⟩
    have hd : ((g j:ℤ):ZMod N)=0 := by simp [g]
    simp [f,hd,tangentCoeff,he,F,g]
  have hev : Function.Even F := by intro j; simp [F,ntkEven]
  have hF := (hf.comp_injective hg).congr hval
  calc
    _ = ∑' j:ℤ, f (g j) := (hg.tsum_eq hsupp).symm
    _ = ∑' j:ℤ, F j := tsum_congr hval
    _ = F 0 + 2 • ∑' j:ℕ+, F (j:ℕ) := tsum_int_eq_zero_add_two_mul_tsum_pnat hev hF
    _ = _ := by
      rw [tsum_pnat_eq_tsum_succ (f:=fun n:ℕ => F (n:ℤ)),←Nat.cast_smul_eq_nsmul ℝ,
        smul_eq_mul,←tsum_mul_left]
      simp [F,k0,ntkEven]

theorem weight_from_grid_alias (n : ℕ) (hN : 3≤n+1) (ho : Odd (n+1)) (τ : ℝ)
    (hτ : 0≤τ) (hτ' : τ≤2) :
    weight τ n = k0 τ / aliasValue (tangentCoeff τ) (0:ZMod (n+1)) := by
  rw [constant_alias_eq hN ho τ hτ hτ',weight,U_eq_alias_sum]
  push_cast
  rfl

open MeasureTheory CircleTangentDrift

omit [NeZero N] in
/-- Each population test row integrates to exactly the zeroth Fourier coefficient. -/
theorem integrated_row (τ : ℝ) (y : AddCircle (π- -π)) :
    (∫ x, (periodicTangent τ (x-y)).re ∂AddCircle.haarAddCircle) = k0 τ := by
  rw [integral_sub_right_eq_self (fun x => (periodicTangent τ x).re)]
  have h := congrArg Complex.re (periodicTangent_coeff τ 0)
  have hi : Integrable (fun x => periodicTangent τ x) AddCircle.haarAddCircle :=
    (periodicTangent τ).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, Complex.reCLM (periodicTangent τ x) ∂AddCircle.haarAddCircle) = _
  rw [Complex.reCLM.integral_comp_comm hi]
  have hz : tangentCoeff τ 0=k0 τ := by simp [tangentCoeff,ntkEven,k0]
  rw [hz] at h
  simpa [fourierCoeff] using h

/-- Concrete matrix in the `Fin N` order used by the network. -/
def sampledMatrix (τ : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (periodicTangent τ (gridAngle (ZMod.finEquiv N i - ZMod.finEquiv N j))).re

private theorem fin_sum (f : ZMod N → ℝ) : (∑ i : Fin N, f (ZMod.finEquiv N i))=∑ i, f i :=
  (ZMod.finEquiv N).toEquiv.sum_comp f

/-- The actual normalized matrix has the coercivity needed for the residual differential equation. -/
theorem gramOp_gap (hN : 3≤N) (ho : Odd N) (τ : ℝ) (hτ : 1/2≤τ) (hτ' : τ≤2)
    (v : EuclideanSpace ℝ (Fin N)) :
    (1/(π*N)^2)*‖v‖^2 ≤ inner ℝ v (gramOp (sampledMatrix τ) v) := by
  let f (i : ZMod N) := v ((ZMod.finEquiv N).symm i)
  have hf (i : Fin N) : f (ZMod.finEquiv N i)=v i := by simp [f]
  have h := sampled_tangent_real_rayleigh hN ho τ hτ hτ' f
  rw [←fin_sum,←fin_sum] at h
  simp only [hf] at h
  rw [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply,star_trivial] at *
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,gramOp_apply,←fin_sum]
  simp [sampledMatrix,hf]

/-- The same constant eigenvalue is the normalized column sum of each sampled matrix. -/
theorem sampled_column (τ : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (j : Fin N) :
    (∑ i : Fin N, sampledMatrix τ i j)/N = aliasValue (tangentCoeff τ) (0:ZMod N) := by
  let F (x : ZMod N) := (periodicTangent τ (gridAngle x)).re
  have h := congrArg Complex.re (sampled_character_eigenvalue τ hτ hτ' (0:ZMod N) 0)
  simp only [convolution,char,zero_mul,AddChar.map_zero_eq_one,mul_one,zero_sub,
    Complex.div_natCast_re,Complex.re_sum,Complex.ofReal_re] at h
  change (∑ i : Fin N, F (ZMod.finEquiv N i-ZMod.finEquiv N j))/N = _
  rw [fin_sum (fun i => F (i-ZMod.finEquiv N j))]
  have shift : ∑ i : ZMod N, F (i-ZMod.finEquiv N j) = ∑ i, F i := (Equiv.subRight (ZMod.finEquiv N j)).sum_comp F
  rw [shift]
  convert h using 1
  exact congrArg (fun z : ℝ => z/N) (Equiv.sum_comp (Equiv.neg (ZMod N)) F).symm

/-- A constant population row is a left eigenrow, with the exact grid alias eigenvalue. -/
theorem gramOp_eigenrow (τ b : ℝ) (hτ : 0≤τ) (hτ' : τ≤2) (v : EuclideanSpace ℝ (Fin N)) :
    rowOp (fun _ => b) (gramOp (sampledMatrix τ) v) =
      aliasValue (tangentCoeff τ) (0:ZMod N)*rowOp (fun _ => b) v := by
  simp only [rowOp_apply,gramOp_apply,←Finset.mul_sum]
  rw [←Finset.sum_div,Finset.sum_comm]
  have h (j : Fin N) : ∑ i : Fin N, sampledMatrix τ i j*v j =
      (aliasValue (tangentCoeff τ) (0:ZMod N)*N)*v j := by
    rw [←Finset.sum_mul,←sampled_column τ hτ hτ' j]
    field_simp [NeZero.ne (N:ℝ)]
  simp_rw [h,←Finset.mul_sum]
  field_simp [NeZero.ne (N:ℝ), Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos N))]

private theorem gridAngle_sub (i j : ZMod N) : gridAngle (i-j) = gridAngle i-gridAngle j := by
  let s := AddCircle.equivAddCircle (1:ℝ) (π- -π) one_ne_zero hp.out.ne'
  have hs (i : ZMod N) : gridAngle i = s (ZMod.toAddCircle i) := by
    rw [ZMod.toAddCircle_apply,AddCircle.equivAddCircle_apply_mk]
    unfold gridAngle
    congr 1
    ring
  simp [hs]

def physicalAngle (i : Fin N) := (2*π/(N:ℝ))*(i:ℕ)

private theorem gridAngle_fin (i : Fin N) : gridAngle (ZMod.finEquiv N i) = (physicalAngle i:ℝ) := by
  have hv : (ZMod.finEquiv N i).val=i.val := by cases N with | zero => exact (NeZero.ne 0 rfl).elim | succ n => rfl
  unfold gridAngle physicalAngle
  rw [hv]
  congr 1
  ring

omit [NeZero N] in
theorem periodicTangent_cartesian (τ u v : ℝ) :
    (periodicTangent τ ((v-u:ℝ):AddCircle (π- -π))).re = cartesianKernel τ u v := by
  let G (s : ℝ) := cartesianKernel τ 0 s
  have hG : Function.Periodic G (π- -π) := by
    intro t
    rw [show t+(π- -π)=t+2*π by ring]
    simp [G,cartesianKernel,cartesianProduct,projection]
  let y : AddCircle (π- -π) := ((v-u:ℝ):AddCircle (π- -π))
  let z := AddCircle.equivIoc (π- -π) (-π) y
  have hz : ((z:ℝ):AddCircle (π- -π))=y := AddCircle.coe_equivIoc
  have h1 : (periodicTangent τ y).re=G z := by
    rw [←hz]
    change (AddCircle.liftIoc (π- -π) (-π) (fun x => (polarNTK τ |x|:ℂ)) (z:ℝ)).re = _
    rw [AddCircle.liftIoc_coe_apply z.property]
    simp [G,cartesian_kernel_isotropic]
  have h2 : hG.lift ((z:ℝ):AddCircle (π- -π)) = hG.lift y := congrArg hG.lift hz
  change G z=G (v-u) at h2
  exact (h1.trans h2).trans (by simp [G,cartesian_kernel_isotropic])

theorem sampledMatrix_cartesian (τ : ℝ) (i j : Fin N) :
    sampledMatrix τ i j = cartesianKernel τ (physicalAngle i) (physicalAngle j) := by
  unfold sampledMatrix
  rw [gridAngle_sub,gridAngle_fin,gridAngle_fin,←AddCircle.coe_sub,periodicTangent_cartesian]
  simp [cartesian_kernel_isotropic,abs_sub_comm]

/-- The scalar test row integrated over the actual uniform parametrization of one turn. -/
theorem cartesian_integrated_row (τ a : ℝ) :
    (∫ u, cartesianKernel τ a (2*π*u) ∂angularLaw) = k0 τ := by
  let P := π- -π
  let y : AddCircle (π- -π) := a
  let F (x : ℝ) := (periodicTangent τ ((x: AddCircle (π- -π))-y)).re
  have hi := integrated_row τ y
  have hh := AddCircle.intervalIntegral_preimage P 0
    (fun x : AddCircle (π- -π) => (periodicTangent τ (x-y)).re)
  rw [AddCircle.volume_eq_smul_haarAddCircle,integral_smul_measure,
    ENNReal.toReal_ofReal hp.out.le,hi] at hh
  have hF (u : ℝ) : cartesianKernel τ a (2*π*u) = F ((2*π)*u) := by
    unfold F y
    rw [←AddCircle.coe_sub,periodicTangent_cartesian]
  simp_rw [hF]
  rw [angularLaw,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_comp_mul_left _ (show 2*π≠0 by positivity)]
  change _ = k0 τ
  simp only [zero_add,smul_eq_mul] at hh
  simp only [mul_one,mul_zero,smul_eq_mul]
  change (2*π)⁻¹*(∫ x in 0..2*π, F x) = _
  have hP : P=2*π := by dsimp [P]; ring
  change (∫ x in 0..P, F x) = P*k0 τ at hh
  rw [hP] at hh
  rw [hh]
  field_simp

theorem population_row_factorization (n : ℕ) (hN : 3≤n+1) (ho : Odd (n+1)) (τ : ℝ)
    (hτ : 1/2≤τ) (hτ' : τ≤2) :
    rowOp (fun _ : Fin (n+1) => k0 τ) = (rowOp (fun _ => weight τ n)).comp (gramOp (sampledMatrix τ)) := by
  ext v
  rw [ContinuousLinearMap.comp_apply,gramOp_eigenrow τ _ (by linarith) hτ',
    weight_from_grid_alias n hN ho τ (by linarith) hτ']
  have hg := tangent_gap hN ho τ hτ hτ' (0:ZMod (n+1))
  have hd : aliasValue (tangentCoeff τ) (0:ZMod (n+1)) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hg)
  simp only [rowOp_apply,←Finset.mul_sum]
  field_simp [hd]

end CircleGridSpectrum
