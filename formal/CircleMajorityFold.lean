module

public import CircleMajorityCF
public import CircleFoldedIntegral
import all CircleMajorityCF
import all CircleGridSpectrum
import all CircleEscape
import Mathlib.Tactic

/-! The uniform odd training grid folds a unit ReLU feature to a cosine on a single cell. -/
public section
noncomputable section
namespace CircleMajorityFold
open Real MeasureTheory Set CircleMajorityCF CircleGridSpectrum

/-- Half the length of a cell for the absolute-cosine sum on an odd training grid. -/
def halfCell (N : ℕ) : ℝ := π/(2*N)

def amplitude (N : ℕ) : ℝ := 1/(2*N*sin (halfCell N))

private theorem sum_abs {N : ℕ} (hn : 3≤N) (θ : ℝ) :
    angular N θ = (∑ i : Fin N, |cos (θ-physicalAngle i)|)/(2*N) := by
  have cz : (∑ i : Fin N, cos (θ-physicalAngle i)) = 0 := by
    convert CircleGridMoments.projection_sum N hn (⟨cos θ,sin θ⟩:ℂ) using 1
    apply Finset.sum_congr rfl; intro i _
    simp only [cos_sub,Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,
      CircleEscape.gridPoint,physicalAngle]; ring
  have h (a : ℝ) : max a 0 = (a+|a|)/2 := by
    rcases le_total a 0 with h|h
    · rw [max_eq_right h,abs_of_nonpos h]; ring
    · rw [max_eq_left h,abs_of_nonneg h]; ring
  simp only [angular,h,←Finset.sum_div,Finset.sum_add_distrib,cz,zero_add]
  ring

private def center {N : ℕ} (hn : 0<N) (M : ℕ) (i : Fin N) : Fin N :=
  ⟨(2*i.val+M)%N,Nat.mod_lt _ hn⟩

private theorem centered {N M : ℕ} (hn : 3≤N) (ho : Odd N) (θ : ℝ) :
    angular N θ = (∑ k ∈ Finset.range N, |cos (θ+π*M/N-π*k/N)|)/(2*N) := by
  have hn' : 0<N := by omega
  have n0 : (N:ℝ)≠0 := by positivity
  let C := center hn' M
  have inj : Function.Injective C := by
    intro i j h
    have c : 2*i.val+M ≡ 2*j.val+M [MOD N] := congrArg Fin.val h
    exact Fin.ext ((Nat.ModEq.cancel_left_of_coprime ho.coprime_two_right
      (Nat.ModEq.add_right_cancel' M c)).eq_of_lt_of_lt i.isLt j.isLt)
  let e := Equiv.ofBijective C (Finite.injective_iff_bijective.mp inj)
  let F (k : ℕ) := |cos (θ+π*M/N-π*k/N)|
  rw [sum_abs hn,←Fin.sum_univ_eq_sum_range F N,←e.sum_comp (fun i : Fin N => F i.val)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let k := (2*i.val+M)/N
  have r : ((e i).val:ℝ)+(N:ℝ)*k=2*(i.val:ℝ)+M := by
    exact_mod_cast Nat.mod_add_div (2*i.val+M) N
  change _ = |cos (θ+π*M/N-π*(e i).val/N)|
  have arg : θ-physicalAngle i = (θ+π*M/N-π*(e i).val/N)-k*π := by
    unfold physicalAngle; field_simp; linear_combination π*r
  rw [arg,cos_sub_nat_mul_pi,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]

private def centerAngle (N M : ℕ) (θ : ℝ) (k : ℕ) := θ+π*M/N-π*k/N

/-- On the central cell the absolute cosine sum has one elementary expression. -/
theorem angular_on_cell {N : ℕ} (hn : 3≤N) (ho : Odd N) {θ : ℝ}
    (hθ : θ ∈ Icc (-(halfCell N)) (halfCell N)) : angular N θ = amplitude N*cos θ := by
  obtain ⟨M,hM⟩ := ho
  have nr : (N:ℝ)=2*(M:ℝ)+1 := by exact_mod_cast hM
  have np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let d := halfCell N
  have dp : 0<d := by unfold d halfCell; positivity
  have small : d<π/2 := by
    unfold d halfCell; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith [pi_pos,show (3:ℝ)≤N by exact_mod_cast hn, mul_pos pi_pos (show 0<(N:ℝ)-1 by linarith [show (3:ℝ)≤N by exact_mod_cast hn])]
  have dp' : sin d ≠ 0 := (sin_pos_of_pos_of_lt_pi dp (by linarith [pi_pos])).ne'
  have dn : d*N=π/2 := by dsimp [d,halfCell]; field_simp
  have md : π*(M:ℝ)/N+d=π/2 := by
    apply (mul_right_cancel₀ np.ne'); field_simp [np.ne'] at dn ⊢; nlinarith [congrArg (fun x : ℝ => π*x) nr]
  have dif (k : ℕ) : centerAngle N M θ (k+1) = centerAngle N M θ k - 2*d := by
    unfold centerAngle; push_cast; unfold d halfCell; ring
  have full (k : ℕ) (hk : k<N) : 0≤cos (centerAngle N M θ k) := by
    apply cos_nonneg_of_mem_Icc
    have hk' : (k:ℝ)≤2*(M:ℝ) := by exact_mod_cast (by omega : k≤2*M)
    have km : π*(k:ℝ)/N≤2*(π*M/N) := by
      rw [←mul_div_assoc,←mul_assoc]; exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hk' pi_pos.le]) np.le
    change -d≤θ ∧ θ≤d at hθ
    unfold centerAngle; constructor <;> linarith [hθ.1,hθ.2,show 0≤π*(k:ℝ)/N by positivity]
  have term (k : ℕ) (hk : k<N) : 2*sin d*|cos (centerAngle N M θ k)| =
      sin (centerAngle N M θ k+d)-sin (centerAngle N M θ (k+1)+d) := by
    rw [abs_of_nonneg (full k hk),dif,show centerAngle N M θ k-2*d+d=centerAngle N M θ k-d by ring,
      sin_add,sin_sub]; ring
  have s : 2*sin d * (∑ k ∈ Finset.range N, |cos (centerAngle N M θ k)|) = 2*cos θ := by
    rw [Finset.mul_sum]
    trans ∑ k ∈ Finset.range N, (sin (centerAngle N M θ k+d)-sin (centerAngle N M θ (k+1)+d))
    · exact Finset.sum_congr rfl (fun k hk => term k (Finset.mem_range.mp hk))
    rw [Finset.sum_range_sub' (fun k => sin (centerAngle N M θ k+d))]
    simp only [centerAngle,Nat.cast_zero,mul_zero,zero_div,sub_zero]
    rw [show θ+π*M/N+d=θ+π/2 by linarith,
      show θ+π*M/N-π*N/N+d=θ-π/2 by field_simp [np.ne'] at md ⊢; linarith,
      sin_add_pi_div_two,sin_sub_pi_div_two]; ring
  rw [centered (M:=M) hn ⟨M,hM⟩,amplitude]
  change (∑ k ∈ Finset.range N, |cos (centerAngle N M θ k)|)/(2*N) = 1/(2*N*sin d)*cos θ
  field_simp [np.ne',dp']; linarith

/-- Oddness of the grid doubles the symmetry of its ReLU average. -/
theorem angular_periodic {N : ℕ} (hn : 3≤N) (ho : Odd N) :
    Function.Periodic (angular N) (2*halfCell N) := by
  have np : (N:ℝ)≠0 := by positivity
  intro θ
  let p := π/(N:ℝ)
  have eq : 2*halfCell N=p := by unfold halfCell p; ring
  rw [eq,centered (M:=0) hn ho,centered (M:=0) hn ho]
  congr 1
  let f (k : ℕ) := |cos (θ+p-π*k/N)|
  have h1 (k : ℕ) : |cos (θ+p+π*(0:ℕ)/N-π*k/N)|=f k := by simp [f]
  have h2 (k : ℕ) : |cos (θ+π*(0:ℕ)/N-π*k/N)|=f (k+1) := by
    simp only [Nat.cast_zero,mul_zero,zero_div,add_zero,f,Nat.cast_succ]
    unfold p; congr 2; ring
  simp_rw [h1,h2]
  apply sub_eq_zero.mp
  rw [←Finset.sum_sub_distrib,Finset.sum_range_sub']
  simp only [f,Nat.cast_zero,mul_zero,zero_div,sub_zero,mul_div_cancel_right₀ _ np,
    cos_sub_pi,abs_neg,sub_self]

/-- Rotating the entire grid reduces every continuous angular expectation to the central cell. -/
theorem angular_average {N : ℕ} (hn : 3≤N) (ho : Odd N) (F : ℝ→ℝ) (hF : Continuous F) :
    (1/(2*π))*(∫ θ in Ioo (-π) π, F (angular N θ)) =
      (∫ θ in -(halfCell N)..halfCell N, F (amplitude N*cos θ))/(2*halfCell N) := by
  let d := halfCell N
  let f (θ : ℝ) := F (angular N θ)
  have np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have dp : 0<d := by unfold d halfCell; positivity
  have hp : Function.Periodic f (2*d) := (angular_periodic hn ho).comp F
  have hc : Continuous f := hF.comp (CircleMajorityCF.angular_cont N)
  let k : ℤ := 2*N
  have kp : k • (2*d) = 2*π := by
    dsimp [k,d,halfCell]; rw [zsmul_eq_mul]; push_cast; field_simp
  have big : Function.Periodic f (2*π) := kp ▸ hp.zsmul k
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith [pi_pos])]
  change (1/(2*π))*(∫ θ in -π..π, f θ) = _
  have shift := big.intervalIntegral_add_eq (-π) (-d)
  rw [show -π+2*π=π by ring] at shift
  have cycles := hp.intervalIntegral_add_zsmul_eq k (-d) hc.intervalIntegrable
  rw [kp,show -d+2*d=d by ring] at cycles
  rw [shift,cycles,zsmul_eq_mul]
  have central : (∫ θ in -d..d, f θ) = ∫ θ in -d..d, F (amplitude N*cos θ) := by
    apply intervalIntegral.integral_congr
    intro θ h; rw [uIcc_of_le (by linarith)] at h
    exact congrArg F (angular_on_cell hn ho h)
  rw [central]; dsimp [k,d,halfCell]; push_cast; field_simp

/-- Closed finite-grid characteristic function for the actual finite learner, including
both grid sizes and every numerical width in `paper/majority.py`. -/
theorem gridMean_charFun_closed {N : ℕ} (hn : 3≤N) (ho : Odd N) (m : ℕ) (t : ℝ) :
    let d := halfCell N
    let b := sqrt (1+((t/sqrt (m:ℝ))*amplitude N)^2)
    MeasureTheory.charFun ((CircleEscapeBridge.seedLaw m).map (CircleScoreMargin.gridMean N m)) t =
      ((arctan (tan d/b)/(d*b) : ℝ):ℂ)^m := by
  dsimp only
  rw [gridMean_charFun,angular_average hn ho (fun x => 1/(1+((t/sqrt (m:ℝ))*x)^2))]
  · congr 2
    have np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have small : halfCell N<π/2 := by
      unfold halfCell; apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [pi_pos,mul_pos pi_pos (show 0<(N:ℝ)-1 by linarith [show (3:ℝ)≤N by exact_mod_cast hn])]
    convert CircleFoldedIntegral.folded_integral ((t/sqrt (m:ℝ))*amplitude N) (halfCell N)
      (by unfold halfCell; positivity) small using 1
    congr 1; apply intervalIntegral.integral_congr; intro θ _; dsimp only; rw [one_div,←mul_pow,←mul_assoc]
  · apply Continuous.div (by fun_prop) (by fun_prop); intro x; positivity

end CircleMajorityFold
