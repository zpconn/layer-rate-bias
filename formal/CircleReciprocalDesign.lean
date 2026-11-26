module

public import CircleShortGDTails
public import CircleDiscreteMoments
import all CircleShortGDTails
import all CircleGaussianTracking
import all CircleActualTracking
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! A high probability event for the full reciprocal step at the early cap. -/
@[expose] public section
noncomputable section
namespace CircleReciprocalDesign
open Real Filter MeasureTheory Set CircleEscapeBridge CircleShortGDTails CircleTangentDrift
open CircleGaussianTracking CircleActualTracking CircleSharpInitialization CircleGridSpectrum CircleSpectrum

def residualCap (N : ℕ) := 66*(N:ℝ)^6
def tolerance (N : ℕ) := 1/(N:ℝ)^10
def radius (N : ℕ) := 4224*(earlyCap N:ℝ)/(N:ℝ)^10
def trackingConstant : ℝ := 24*132*(126720*1089+99)

theorem clock (N : ℕ) (hn : 1≤N) : (earlyCap N:ℝ)≤33*sqrt N := by
  have one : (1:ℝ)≤N := by exact_mod_cast hn
  have pos : (0:ℝ)<N := by linarith
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr pos)
  rw [log_sqrt pos.le] at h
  have t := (Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg π) (log_nonneg one))).le
  change (earlyCap N:ℝ)≤π^2*log N+1 at t
  have pp : π^2 ≤ 16 := by nlinarith [pi_pos,pi_lt_four]
  linarith [mul_le_mul_of_nonneg_right pp (log_nonneg one),one_le_sqrt.mpr one]

theorem design_sizes (N : ℕ) (hn : 2000000000≤N) :
    0≤radius N ∧ radius N≤1 ∧ 0≤tolerance N ∧ tolerance N≤1/(1000:ℝ) ∧
    (earlyCap N:ℝ)*(64/sqrt (N^32:ℕ)*residualCap N)≤radius N ∧
    (earlyCap N:ℝ)*(2*(30*radius N+3*tolerance N))≤1/8 ∧
    24*(2*(30*radius N+3*tolerance N))*residualCap N*(earlyCap N:ℝ)≤trackingConstant/(N:ℝ)^3 := by
  have hN : (2000000000:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have n1 : (1:ℝ)≤N := by linarith
  have t := clock N (by omega)
  let T := (earlyCap N:ℝ)
  have t0 : 0≤T := Nat.cast_nonneg _
  have sq : T^2≤1089*(N:ℝ) := (pow_le_pow_left₀ t0 t 2).trans_eq (by rw [mul_pow,sq_sqrt np.le];norm_num)
  have tr : T≤33*(N:ℝ) := t.trans (mul_le_mul_of_nonneg_left ((sqrt_le_iff).mpr ⟨np.le,by nlinarith [mul_nonneg (sub_nonneg.mpr n1) np.le]⟩) (by norm_num))
  have n9 : (N:ℝ)≤(N:ℝ)^9 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤9)
  have n10 : (N:ℝ)≤(N:ℝ)^10 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤10)
  have x : sqrt ((N^32:ℕ):ℝ)=(N:ℝ)^16 := by rw [Nat.cast_pow,show 32=16*2 by decide,pow_mul,sqrt_sq (by positivity)]
  change 0≤4224*T/(N:ℝ)^10 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨by positivity,?_,by dsimp [tolerance];positivity,?_,?_,?_,?_⟩
  · change 4224*T/(N:ℝ)^10≤1
    apply (div_le_one (by positivity)).mpr
    calc _ ≤ 139392*(N:ℝ) := by linarith
         _ ≤ (N:ℝ)^9*N := mul_le_mul_of_nonneg_right (by linarith : (139392:ℝ)≤(N:ℝ)^9) np.le
         _ = _ := by ring
  · unfold tolerance
    apply one_div_le_one_div_of_le (by norm_num) (by linarith)
  · unfold radius residualCap
    rw [x]
    apply le_of_eq
    field_simp
    ring
  · change T*(2*(30*(4224*T/(N:ℝ)^10)+3*(1/(N:ℝ)^10)))≤1/8
    field_simp
    calc _ ≤ 2210000000*(N:ℝ) := by nlinarith only [sq,tr]
         _ ≤ (N:ℝ)^9*N := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((N:ℝ)-2000000000), pow_le_pow_right₀ n1 (by decide : 2≤9)] : (2210000000:ℝ)≤(N:ℝ)^9) np.le
         _ = _ := by ring
  · change 24*(2*(30*(4224*T/(N:ℝ)^10)+3*(1/(N:ℝ)^10)))*(66*(N:ℝ)^6)*T≤trackingConstant/(N:ℝ)^3
    have alg : 24*(2*(30*(4224*T/(N:ℝ)^10)+3*(1/(N:ℝ)^10)))*(66*(N:ℝ)^6)*T =
        (24*132*(126720*T^2+3*T))/(N:ℝ)^4 := by field_simp;ring
    rw [alg]
    apply (div_le_iff₀ (by positivity)).mpr
    have eq : trackingConstant/(N:ℝ)^3*(N:ℝ)^4=trackingConstant*N := by field_simp
    rw [eq]
    dsimp [trackingConstant]
    linarith

private theorem probability_cost (N : ℕ) (hn : 2000000000≤N) :
    ((((N:ℝ)+1)^2+1)*(2*exp (-(N:ℝ)^12/36864))+2*N*exp (-(N:ℝ)^12))≤exp (-(N:ℝ)^12/1000000) := by
  have hN : (2000000000:ℝ)≤N := by exact_mod_cast hn
  have one : (1:ℝ)≤N := by linarith
  have s0 : 0≤(N:ℝ)^12 := by positivity
  have po := exp_le_exp.mpr (show -(N:ℝ)^12≤ -(N:ℝ)^12/36864 by linarith)
  let C := 2*(((N:ℝ)+1)^2+1)+2*N
  have linear : C ≤ (N:ℝ)^12/100000 := by
    have sq : (N:ℝ)^2≤(N:ℝ)^11 := pow_le_pow_right₀ one (by decide)
    have cube : (N:ℝ)^3 ≤ (N:ℝ)^12 := pow_le_pow_right₀ one (by decide)
    dsimp [C]
    nlinarith only [cube,mul_nonneg (sub_nonneg.mpr hN) (sq_nonneg (N:ℝ)), mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr one),one]
  have pref := linear.trans ((by linarith : (N:ℝ)^12/100000≤(N:ℝ)^12/100000+1).trans (add_one_le_exp _))
  calc _ ≤ C*exp (-(N:ℝ)^12/36864) := by dsimp [C]; nlinarith only [mul_le_mul_of_nonneg_left po (show 0≤2*(N:ℝ) by positivity)]
       _ ≤ exp ((N:ℝ)^12/100000)*exp (-(N:ℝ)^12/36864) := mul_le_mul_of_nonneg_right pref (exp_pos _).le
       _ ≤ _ := by rw [←exp_add,exp_le_exp];linarith

theorem event (N : ℕ) [NeZero N] (hn : 2000000000≤N) :
    ∃ E : Set (Seed (N^32)), MeasurableSet E ∧ (seedLaw (N^32)).real Eᶜ ≤ exp (-(N:ℝ)^12/1000000) ∧
      ∀ z∈E, GoodInit 1 (radius N) (tolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z ∧
        ‖gridR N z‖≤residualCap N := by
  let μ := seedLaw (N^32)
  let I := {z : Seed (N^32) | ¬GoodInit 1 (radius N) (tolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z}
  let R := {z : Seed (N^32) | 2+64*(N:ℝ)^6 < initialRms N (N^32) z}
  have hN : (2000000000:ℝ)≤N := by exact_mod_cast hn
  have one : (1:ℝ)≤N := by linarith
  have np : (0:ℝ)<N := by linarith
  have s := design_sizes N hn
  have hm : 0<N^32 := pow_pos (by omega) _
  have gi := CircleGaussianBernstein.goodInit_exponential (N:=N) hm (by norm_num : |(1:ℝ)|≤2) s.1 s.2.1 s.2.2.1 (s.2.2.2.1.trans (by norm_num))
  have x : sqrt ((N^32:ℕ):ℝ)=(N:ℝ)^16 := by rw [Nat.cast_pow,show 32=16*2 by decide,pow_mul,sqrt_sq (by positivity)]
  have rr := initialRms_tail_exp (N:=N) (m:=N^32) (by omega) hm (by positivity : 0≤64*(N:ℝ)^6) (by
    rw [x]
    exact mul_le_mul (by norm_num) (pow_le_pow_right₀ one (by decide : 6≤16)) (by positivity) (by norm_num))
  have a : -((N^32:ℕ):ℝ)*(tolerance N)^2/36864= -(N:ℝ)^12/36864 := by unfold tolerance;push_cast;field_simp
  have b : -(64*(N:ℝ)^6)^2/4096= -(N:ℝ)^12 := by ring
  rw [a] at gi
  rw [b] at rr
  refine ⟨(toMeasurable μ (I∪R))ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ (I∪R))ᶜ)ᶜ≤_
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    exact ((measureReal_union_le _ _).trans (add_le_add gi rr)).trans (probability_cost N hn)
  · intro z hz
    have hh : z∉I∪R := fun h => hz (subset_toMeasurable _ _ h)
    have hj : z∉I ∧ z∉R := by simpa only [mem_union,not_or] using hh
    have ini : ‖gridR N z‖ ≤ 2+64*(N:ℝ)^6 := le_of_not_gt hj.2
    exact ⟨not_not.mp hj.1,ini.trans (by unfold residualCap;linarith [one_le_pow₀ one (n:=6)])⟩

end CircleReciprocalDesign
