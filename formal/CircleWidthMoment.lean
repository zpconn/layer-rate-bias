module

public import CircleShortGDTails
import all CircleShortGDTails
import all CircleEscape
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleFlowMoments
import Mathlib.Tactic

/-! All-seed fourth envelope for every deterministic step in [0,1]. -/
@[expose] public section
noncomputable section
namespace CircleWidthMoment
open Real MeasureTheory CircleEscape CircleEscapeBridge CircleInitializationCheck CircleSeedIntegrability
open CircleShortGDTails
variable {N m : ℕ}

private theorem actual_bound {η : ℝ} (hη : 0≤η) (hc : η≤1) (hN : 0 < N) (hm : 0 < m) (t : ℕ) (ω : Seed m) :
    CircleSeedIntegrability.Bounded (path N m η ω t) (B m t ω) := by
  have ns : 0 < (N:ℝ) := by exact_mod_cast hN
  have ms : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have sr : 1 ≤ √(m:ℝ) := one_le_sqrt.mpr ms
  have sp : 0 < √(m:ℝ) := lt_of_lt_of_le zero_lt_one sr
  induction t with
  | zero =>
    have e : B m 0 ω = 2*radius ω := by simp [B]; ring
    rw [e]
    exact CircleSeedIntegrability.initial_bound ω
  | succ t ih =>
    let c := 1/√(m:ℝ)
    let k := η/((N:ℝ)*√(m:ℝ))
    have h := CircleSeedIntegrability.bound_step c k (B m t ω) (path N m η ω t) (B_one t ω) ih
      (gridPoint N) (fun i => 1+(gridPoint N i).re) (fun i => (grid_norm N i).le) (by
        intro i; exact CircleFlowMoments.circle_label_abs N i)
    have d : 1+|k| *N*(|c| *m+2) ≤ 4 := by
      rw [abs_of_nonneg (by dsimp [k];positivity),abs_of_nonneg (by dsimp [c];positivity)]
      have km : k≤1/((N:ℝ)*√(m:ℝ)) := div_le_div_of_nonneg_right hc (by positivity)
      apply (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right km ns.le)
        (show 0≤c*(m:ℝ)+2 by dsimp [c];positivity)) 1).trans
      dsimp [c]
      field_simp
      nlinarith [mul_nonneg ns.le (sub_nonneg.mpr sr),Real.sq_sqrt (show 0 ≤ (m:ℝ) by positivity)]
    have ub : (1+|k| *N*(|c| *m+2))*(B m t ω)^3 ≤ B m (t+1) ω := by
      apply (mul_le_mul_of_nonneg_right d (pow_nonneg (zero_le_one.trans (B_one t ω)) _)).trans_eq
      simp [B,pow_succ 3,pow_mul]
      ring
    intro j
    exact ⟨(h j).1.trans ub,(h j).2.trans ub⟩

def rawError (N m t : ℕ) (η b : ℝ) (ω : Seed m) :=
  trainedMean (path N m η) t ω - reference N m b ω

theorem raw_envelope {η : ℝ} (hη : 0≤η) (hc : η≤1) (hN : 0 < N) (hm : 0 < m) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) (t : ℕ) (ω : Seed m) :
    |rawError N m t η b ω| ≤ (5*m:ℝ)*(4*radius ω)^(2*3^t) := by
  have ms : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have sr : 1 ≤ √(m:ℝ) := one_le_sqrt.mpr ms
  have cr : 1/√(m:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr sr
  have cp : |(1/√(m:ℝ))/π| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_self (by positivity) (by linarith [pi_gt_three])).trans cr
  have y := CircleSeedIntegrability.mean_cap (1/√(m:ℝ)) _ (zero_le_one.trans (B_one t ω)) _ (actual_bound hη hc hN hm t ω)
  have ar := CircleSeedIntegrability.radius_one ω
  have rs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Coord m) _ => show ω i ^2 ≤ (radius ω)^2 by
    have sq := pow_le_pow_left₀ (abs_nonneg _) (radius_coord ω i) 2
    simpa [sq_abs] using sq)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at rs
  have tr := CircleFlowMoments.reference_cap ω hN hb hb'
  have bb := mul_le_mul cr rs (Finset.sum_nonneg (fun i _ => sq_nonneg (ω i))) (by norm_num)
  change _ ≤ 1+1/√(m:ℝ)*(∑ i, (ω i)^2) at tr
  have low : (radius ω)^2 ≤ (4*radius ω)^(2*3^t) := by
    calc
      _ ≤ (4*radius ω)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by exact Nat.le_mul_of_pos_right 2 (by positivity))
  have b4 : (B m t ω)^2 ≤ (4*radius ω)^(2*3^t) := by
    rw [B,div_pow,show 2*3^t=3^t*2 by omega,pow_mul]
    nlinarith [sq_nonneg ((4*radius ω)^(3^t))]
  have hroot := mul_le_mul (mul_le_mul_of_nonneg_right cp (Nat.cast_nonneg m)) b4 (sq_nonneg _) (by positivity : 0 ≤ 1*(m:ℝ))
  have zr := mul_le_mul_of_nonneg_left low (show 0 ≤ (m:ℝ) by positivity)
  have z1 : 1 ≤ (m:ℝ)*(4*radius ω)^(2*3^t) :=
    one_le_mul_of_one_le_of_one_le ms (one_le_pow₀ (by linarith))
  exact (abs_sub _ _).trans (by change |populationMean (1/√(m:ℝ)) (path N m η ω t)| + |reference N m b ω| ≤ _; nlinarith only [y,tr,bb,hroot,zr,z1])


theorem raw_mem4 (N m t : ℕ) (η b : ℝ) : MemLp (rawError N m t η b) 4 (seedLaw m) :=
  (trained_memLp N m t η 4 (by norm_num)).sub (reference_memLp N m b 4 (by norm_num))

/-- The fourth moment of the true unconstrained iteration grows at most like
exp(O(3^t (log(m+1)+t))). No screen or trajectory tube is assumed. -/
theorem raw_fourth {η : ℝ} (hη : 0≤η) (hc : η≤1) (hN : 0 < N) (hm : 0 < m) (t : ℕ) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) :
    ∫ ω, (rawError N m t η b ω)^4 ∂seedLaw m ≤ fourthBound m t := by
  let p := momentDegree t
  have pp : 0 < p := by dsimp [p,momentDegree]; positivity
  let K := (5*(m:ℝ))^4*4^p
  have h (ω : Seed m) : (rawError N m t η b ω)^4 ≤ K*(radius ω)^p := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (raw_envelope hη hc hN hm hb hb' t ω) 4
    rw [(by decide : Even 4).pow_abs,mul_pow,← pow_mul,mul_pow] at h
    have e : (2*3^t)*4 = p := by dsimp [p,momentDegree]; omega
    simpa only [e,K,mul_pow,mul_assoc] using h
  have hm4 : MemLp (rawError N m t η b) (4:ℕ) (seedLaw m) := raw_mem4 _ _ _ _ _
  have hi : Integrable (fun ω => rawError N m t η b ω^4) (seedLaw m) := by
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hm4.integrable_norm_pow'
  have ri := (CircleSeedIntegrability.radius_power_mem m p 1 (by norm_num)).integrable (by norm_num)
  have mono := integral_mono hi (ri.const_mul K) h
  rw [integral_const_mul] at mono
  apply (mono.trans (mul_le_mul_of_nonneg_left (radius_moment m p hm pp) (by dsimp [K]; positivity))).trans_eq
  dsimp [fourthBound,K,p]
  simp only [mul_pow]
  ring


end CircleWidthMoment
