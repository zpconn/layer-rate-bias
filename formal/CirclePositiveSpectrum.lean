module
public import CircleKernelGD
public import CircleFiniteCoefficient
import all CircleGridSpectrum
import all CircleKernelGD
import all CircleKernelIdentification
import all CircleFlowTracking
import all CircleTangentDrift
import all CircleSpectrum
import Mathlib.Tactic

/-! Odd-grid spectrum and fixed-step contraction for every nonnegative hidden rate. -/
public section
noncomputable section
namespace CirclePositiveSpectrum
open CircleGridSpectrum CircleKernelIdentification CircleSpectrum CircleTangentDrift Real Finset
private local instance hp : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩
variable {N : ℕ} [NeZero N]

theorem summable (τ : ℝ) : Summable (tangentCoeff τ) := by
  have a := tangentCoeff_summable 0 (by norm_num) (by norm_num)
  have b := tangentCoeff_summable 1 (by norm_num) (by norm_num)
  apply (a.add ((b.sub a).mul_left τ)).congr
  intro k
  unfold tangentCoeff
  split_ifs <;> simp [ntkEven] <;> ring

theorem alias_gap (hN : 3≤N) (hodd : Odd N) (τ : ℝ) (hτ : 0≤τ)
    (r : ZMod N) : τ/(π*N)^2 ≤ aliasValue (tangentCoeff τ) r := by
  let a := tangentCoeff τ
  let f (k : ℤ) : ℝ := if (k:ZMod N)=r then a k else 0
  have ht : 0≤τ := by linarith
  have ha := summable τ
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
    apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos pi_pos hn0)) (sq_pos_of_pos pi_pos)).2
    have hnn : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ (by linarith)
    have hc : τ ≤ (2+τ)*(N:ℝ)^2 := (by linarith : τ≤2+τ).trans
      (le_mul_of_one_le_right (by linarith) hnn)
    nlinarith only [mul_le_mul_of_nonneg_left hc (sq_nonneg π)]
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
    have heq' : τ/(π*(N:ℝ))^2 ≤ (τ/π^2)*(8/(2*(N:ℝ))^2) := by
      have nn : 0≤τ/(π*(N:ℝ))^2 := by positivity
      convert le_add_of_nonneg_right nn using 1; ring
    apply heq'.trans
    calc
      _ ≤ (τ/π^2)*(1/(j:ℝ)^2+1/(q:ℝ)^2) := by gcongr
      _ = _ := by ring

private theorem series_eigen (τ : ℝ) (r i : ZMod N) :
    convolution (series (fun k => (tangentCoeff τ k:ℂ))) (char r) i =
      (aliasValue (tangentCoeff τ) r:ℂ)*char r i := by
  have h := (summable τ).norm
  rw [character_eigenvalue _ (by simpa using h),aliasValue,Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro k
  split <;> simp_all

private theorem reconstruct (τ : ℝ) (i : ZMod N) :
    periodicTangent τ (gridAngle i) = series (fun k => (tangentCoeff τ k:ℂ)) i := by
  have h : Summable (fourierCoeff (periodicTangent τ)) := by
    exact (Complex.ofRealCLM.summable (summable τ)).congr fun k =>
      (periodicTangent_coeff τ k).symm
  have hh := (has_pointwise_sum_fourier_series_of_summable h (gridAngle i)).tsum_eq
  simpa only [series,←sampled_fourier,periodicTangent_coeff,smul_eq_mul] using hh.symm

theorem character (τ : ℝ) (r i : ZMod N) :
    convolution (fun d => periodicTangent τ (gridAngle d)) (char r) i =
      (aliasValue (tangentCoeff τ) r:ℂ)*char r i := by
  simpa only [reconstruct τ] using series_eigen τ r i


open scoped ComplexConjugate
private theorem complex_rayleigh (hN : 3≤N) (hodd : Odd N) (τ : ℝ)
    (hτ : 0≤τ) (v : ZMod N → ℂ) :
    (τ/(π*N)^2)*(∑ i, ‖v i‖^2) ≤
      (∑ i : ZMod N, conj (v i)*convolution (fun x => periodicTangent τ (gridAngle x)) v i).re :=
  rayleigh_of_character_gap _ v _ _ (character τ)
    (alias_gap hN hodd τ hτ)

/-- Real quadratic-form version in the normalization of the training residual. -/
private theorem real_rayleigh (hN : 3≤N) (hodd : Odd N) (τ : ℝ)
    (hτ : 0≤τ) (v : ZMod N → ℝ) :
    (τ/(π*N)^2)*(∑ i, (v i)^2) ≤
      ∑ i : ZMod N, v i*((∑ j : ZMod N, (periodicTangent τ (gridAngle (i-j))).re*v j)/N) := by
  have h := complex_rayleigh hN hodd τ hτ (fun i => (v i:ℂ))
  have hc (z : ℂ) : (z/(N:ℂ)).re = z.re/(N:ℝ) := by
    simp
  simpa only [convolution,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.re_sum,
    Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
    sub_zero,hc] using h

theorem coercive (hN : 3≤N) (ho : Odd N) (τ : ℝ) (hτ : 0≤τ)
    (v : EuclideanSpace ℝ (Fin N)) :
    (τ/(π*N)^2)*‖v‖^2 ≤ inner ℝ v (gramOp (sampledMatrix τ) v) := by
  let f (i : ZMod N) := v ((ZMod.finEquiv N).symm i)
  have hf (i : Fin N) : f (ZMod.finEquiv N i)=v i := by simp [f]
  have h := real_rayleigh hN ho τ hτ f
  rw [←fin_sum,←fin_sum] at h
  simp only [hf] at h
  rw [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply,star_trivial] at *
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,gramOp_apply,←fin_sum]
  simp [sampledMatrix,hf]

private theorem entry_bound (τ : ℝ) (ht : 0≤τ) (i j : Fin N) : |sampledMatrix τ i j|≤(1+τ)/2 := by
  let y := gridAngle (ZMod.finEquiv N i-ZMod.finEquiv N j)
  let a := AddCircle.equivIoc (π- -π) (-π) y
  have hp : 0≤|(a:ℝ)| := abs_nonneg _
  have ha : |(a:ℝ)|≤π := abs_le.mpr ⟨a.property.1.le,by simpa using a.property.2⟩
  have eq : sampledMatrix τ i j = polarNTK τ |(a:ℝ)| := rfl
  rw [eq,angular_tangent τ _ hp ha,abs_div,abs_of_pos (show 0<2*π by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  apply (abs_add_le _ _).trans
  have hsin : |sin (|(a:ℝ)|)| ≤ |(a:ℝ)| := by simpa using (abs_sin_le_abs (x:=|(a:ℝ)|))
  have hd : 0 ≤ (1+τ)*(π-|(a:ℝ)|) := mul_nonneg (by linarith) (sub_nonneg.mpr ha)
  rw [abs_mul,abs_of_nonneg hd]
  have hc := mul_le_mul_of_nonneg_left (abs_cos_le_one |(a:ℝ)|) hd
  nlinarith only [hc,hsin,mul_nonneg ht hp]

theorem operator_upper (τ : ℝ) (ht : 0≤τ) : ‖gramOp (N:=N) (sampledMatrix τ)‖≤(1+τ)/2 :=
  gramOp_norm (NeZero.pos N) (by positivity) (entry_bound τ ht)

private theorem symmetric (τ : ℝ) : (gramOp (N:=N) (sampledMatrix τ)).toLinearMap.IsSymmetric := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j => sampledMatrix τ i j / N
  change (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin N) A).toLinearMap.IsSymmetric
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.isSymmetric_toEuclideanLin_iff]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial]
  dsimp only [A]
  rw [sampledMatrix_cartesian,sampledMatrix_cartesian,cartesian_kernel_isotropic,cartesian_kernel_isotropic,abs_sub_comm]


theorem contraction (hN : 3≤N) (odd : Odd N) (τ η : ℝ) (hp : 0<τ) (he : 0≤η)
    (stable : η*(1+τ)≤2) (v : EuclideanSpace ℝ (Fin N)) :
    ‖v-η • gramOp (sampledMatrix τ) v‖ ≤ (1-η*(τ/(π*(N:ℝ))^2))*‖v‖ := by
  let A := gramOp (N:=N) (sampledMatrix τ)
  let U := (1 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) - η • A
  have hs : U.toLinearMap.IsSymmetric := LinearMap.IsSymmetric.id.sub ((symmetric τ).smul (show (starRingEnd ℝ) η = η by simp))
  apply (U.le_opNorm v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro u
  have h0 := A.le_opNorm u
  have hg := h0.trans (mul_le_mul_of_nonneg_right (operator_upper τ hp.le) (norm_nonneg u))
  have hi := (real_inner_le_norm (A u) u).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg u))
  have ub : η*inner ℝ (A u) u ≤ ‖u‖^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hi he,mul_le_mul_of_nonneg_right stable (sq_nonneg ‖u‖)]
  have lo := coercive hN odd τ hp.le u
  rw [real_inner_comm] at lo
  have eq : U.reApplyInnerSelf u = ‖u‖^2 - η*inner ℝ (A u) u := by
    change inner ℝ (u-η • A u) u = _
    rw [inner_sub_left,real_inner_self_eq_norm_sq,real_inner_smul_left]
  by_cases hz : u=0
  · have gap : τ/(π*(N:ℝ))^2 ≤ (1+τ)/2 := by
      have hot : 2≤(π*(N:ℝ))^2 := by
        have h : (3:ℝ)≤π*(N:ℝ) := by
          exact pi_gt_three.le.trans (le_mul_of_one_le_right pi_pos.le (by exact_mod_cast (show 1≤N by omega)))
        nlinarith [sq_nonneg (π*N-3)]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hot (show 0≤1+τ by positivity)]
    simp only [hz,ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      map_zero,inner_zero_right,abs_zero,zero_div]
    linarith only [mul_le_mul_of_nonneg_left gap he,stable]
  · show |U.reApplyInnerSelf u/‖u‖^2| ≤ _
    rw [eq,abs_of_nonneg (div_nonneg (sub_nonneg.mpr ub) (sq_nonneg _))]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
    change τ/(π*(N:ℝ))^2*‖u‖^2 ≤ inner ℝ (A u) u at lo
    linarith only [mul_le_mul_of_nonneg_left lo he]


/-- The unit step can cross the origin on individual eigenspaces. For
hidden multipliers at most two, its negative Rayleigh values stay above
minus one half, so the smallest eigenvalue still controls contraction. -/
theorem unit_contraction (hN : 3≤N) (odd : Odd N) (τ : ℝ) (hp : 0<τ) (hτ : τ≤2)
    (v : EuclideanSpace ℝ (Fin N)) :
    ‖v-(1:ℝ) • gramOp (sampledMatrix τ) v‖ ≤ (1-1*(τ/(π*(N:ℝ))^2))*‖v‖ := by
  simp only [one_smul, one_mul]
  let A := gramOp (N:=N) (sampledMatrix τ)
  let U := (1 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) - A
  have hs : U.toLinearMap.IsSymmetric := LinearMap.IsSymmetric.id.sub (symmetric τ)
  have base : (3:ℝ) ≤ π*(N:ℝ) :=
    pi_gt_three.le.trans (le_mul_of_one_le_right pi_pos.le (by exact_mod_cast (show 1≤N by omega)))
  have denom : (4:ℝ) ≤ (π*(N:ℝ))^2 := by nlinarith [sq_nonneg (π*(N:ℝ)-3)]
  have gap : τ/(π*(N:ℝ))^2 ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  apply (U.le_opNorm v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro u
  by_cases hz : u=0
  · simp only [hz,ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      map_zero,inner_zero_right,abs_zero,zero_div]
    linarith
  · have qpos : 0<‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have hi := (real_inner_le_norm (A u) u).trans (mul_le_mul_of_nonneg_right
      ((A.le_opNorm u).trans (mul_le_mul_of_nonneg_right (operator_upper τ hp.le) (norm_nonneg u)))
      (norm_nonneg u))
    have lo := coercive hN odd τ hp.le u
    rw [real_inner_comm] at lo
    change τ/(π*(N:ℝ))^2*‖u‖^2 ≤ inner ℝ (A u) u at lo
    have eq : U.reApplyInnerSelf u = ‖u‖^2 - inner ℝ (A u) u := by
      change inner ℝ (u-A u) u = _
      rw [inner_sub_left,real_inner_self_eq_norm_sq]
    show |U.reApplyInnerSelf u/‖u‖^2| ≤ _
    rw [eq,abs_div,abs_of_pos qpos,div_le_iff₀ qpos]
    apply abs_le.mpr
    constructor
    · have avg : (1+τ)/2 ≤ 2-τ/(π*(N:ℝ))^2 := by linarith
      nlinarith only [hi,mul_le_mul_of_nonneg_right avg qpos.le]
    · linarith

/-- The population kernel row is the physical-rate interpolation weight
times the empirical grid row mean, for any positive hidden multiplier. -/
theorem weighted_column (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (τ : ℝ) (hp : 0≤τ)
    (j : Fin (n+1)) :
    weight τ n * ((∑ i : Fin (n+1), sampledMatrix τ i j)/(n+1:ℕ)) = k0 τ := by
  let C (t : ℝ) := (∑ i, sampledMatrix t i j)/(n+1:ℕ)
  have cell (t : ℝ) (i : Fin (n+1)) :
      sampledMatrix t i j = sampledMatrix 0 i j + t*(sampledMatrix 1 i j-sampledMatrix 0 i j) := by
    simp only [sampledMatrix_cartesian,cartesian_kernel_isotropic,polarNTK];ring
  have aff : C τ = C 0 + τ*(C 1-C 0) := by
    dsimp [C]
    conv_lhs => enter [1,2,i]; rw [cell τ i]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_sub_distrib]
    ring
  have initial (t : ℝ) (lo : 0≤t) (hi : t≤2) : C t = k0 t+U t n := by
    dsimp [C]
    rw [sampled_column t lo hi,constant_alias_eq hn odd t lo hi,U_eq_alias_sum];push_cast;rfl
  rw [initial 0 (by norm_num) (by norm_num),initial 1 (by norm_num) (by norm_num)] at aff
  have id : C τ=k0 τ+U τ n := by
    rw [aff];simp only [k0,CircleFiniteCoefficient.tangent_alias_split];ring
  change weight τ n * C τ = k0 τ
  rw [id,weight,div_mul_cancel₀]
  have p := CircleFiniteCoefficient.aliasA_nonneg n
  have q := CircleFiniteCoefficient.aliasB_pos n
  rw [k0,CircleFiniteCoefficient.tangent_alias_split];positivity

end CirclePositiveSpectrum
