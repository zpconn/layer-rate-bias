module

public import CircleCapMoments
public import CircleGaussianTracking
import all CircleGaussianTracking
import all CircleSeedIntegrability
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationCheck
import all CircleCapMoments
import all CircleFlowMoments
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Exposure of the unrestricted GD iteration on rare Gaussian seeds.
All finite iteration bounds refer to the simultaneous two-layer step with
the strict positive training gates. -/
@[expose] public section
noncomputable section
namespace CircleShortGDTails
open Real MeasureTheory ProbabilityTheory Set Filter
open CircleEscape CircleEscapeBridge CircleInitializationCheck CircleSeedIntegrability
abbrev Coord (m : ℕ) := Fin m × Fin 3
variable {N m : ℕ}

private theorem radius_coord (ω : Seed m) (i : Coord m) : |ω i| ≤ radius ω := by
  have h := Finset.single_le_sum (fun i _ => abs_nonneg (ω i)) (Finset.mem_univ i)
  unfold radius
  linarith

private theorem radius_moment (m p : ℕ) (hm : 0 < m) (hp : 0 < p) :
    ∫ ω : Seed m, (radius ω)^p ∂seedLaw m ≤
      ((1+3*(m:ℝ))*(p:ℝ))^p * exp 9 * (6*(m:ℝ)) := by
  let vs := fun (i : Coord m) (ω : Seed m) => exp ((ω i)^2/32)
  have hi (i : Coord m) : Integrable (vs i) (seedLaw m) := by
    have h : Integrable (fun x : ℝ => exp (x^2/32)) (gaussianReal 0 1) :=
      Integrable.of_integral_ne_zero (by rw [CircleCapMoments.gaussian_exp_sq]; positivity)
    exact (measurePreserving_eval (fun _ : Coord m => gaussianReal 0 1) i).integrable_comp_of_integrable h
  have mi (i : Coord m) : ∫ ω, vs i ω ∂seedLaw m = sqrt (16/15) := by
    exact ((measurePreserving_eval (fun _ : Coord m => gaussianReal 0 1) i).hasLaw.integral_comp
      (show AEStronglyMeasurable (fun x : ℝ => exp (x^2/32)) (gaussianReal 0 1) by fun_prop)).trans CircleCapMoments.gaussian_exp_sq
  let K := ((1+3*(m:ℝ))*(p:ℝ))^p * exp 9
  have bound (ω : Seed m) : (radius ω)^p ≤ K * ∑ i, vs i ω := by
    have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    obtain ⟨i,_,maximal⟩ := Finset.exists_max_image Finset.univ (fun i : Coord m => |ω i|) Finset.univ_nonempty
    have rs : radius ω ≤ (1+3*(m:ℝ))*(1+|ω i|) := by
      have hh := Finset.sum_le_sum (s:=Finset.univ) maximal
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hh
      unfold radius
      nlinarith [abs_nonneg (ω i),(Nat.cast_nonneg m : 0 ≤ (m:ℝ))]
    have pp : 0 < (p:ℝ) := by exact_mod_cast hp
    have xpow : (1+|ω i|)^p ≤ (p:ℝ)^p * exp (1+|ω i|) := by
      have h : 1+|ω i| ≤ (p:ℝ)*exp ((1+|ω i|)/p) := by
        have hh := Real.add_one_le_exp ((1+|ω i|)/p)
        have h' := (div_le_iff₀ pp).mp (show (1+|ω i|)/p ≤ exp ((1+|ω i|)/p) by linarith)
        linarith
      have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|ω i|) h p
      rwa [mul_pow,← exp_nat_mul,show (p:ℝ)*((1+|ω i|)/p)=1+|ω i| by field_simp] at ht
    have he : exp (1+|ω i|) ≤ exp 9 * vs i ω := by
      rw [← Real.exp_add]
      apply exp_le_exp.mpr
      nlinarith [sq_nonneg (|ω i|-16),sq_abs (ω i)]
    have add := Finset.single_le_sum (fun k _ => exp_nonneg ((ω k)^2/32)) (Finset.mem_univ i)
    have h := pow_le_pow_left₀ (zero_le_one.trans (CircleSeedIntegrability.radius_one ω)) rs p
    rw [mul_pow] at h
    dsimp only [K]
    calc
      _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left xpow (by positivity))
      _ ≤ (1+3*(m:ℝ))^p*((p:ℝ)^p*(exp 9*vs i ω)) := by gcongr
      _ = ((1+3*(m:ℝ))*(p:ℝ))^p*exp 9*vs i ω := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left add (by positivity)
  have hi' := (CircleSeedIntegrability.radius_power_mem m p 1 (by norm_num)).integrable (by norm_num)
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have h := integral_mono hi' (hs.const_mul K) bound
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)] at h
  simp only [mi,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at h
  have hu : sqrt (16/15:ℝ) ≤ 2 := by apply sqrt_le_iff.mpr; norm_num
  apply h.trans
  change K*_ ≤ K*_
  apply mul_le_mul_of_nonneg_left _ (by dsimp [K]; positivity)
  nlinarith [mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg m)]

private def B (m t : ℕ) (ω : Seed m) := (4*radius ω)^(3^t)/2

private theorem B_one (t : ℕ) (ω : Seed m) : 1 ≤ B m t ω := by
  have r := CircleSeedIntegrability.radius_one ω
  have h := le_self_pow₀ (show 1 ≤ 4*radius ω by linarith) (show 3^t ≠ 0 by positivity)
  unfold B
  linarith

private theorem actual_bound (hN : 0 < N) (hm : 0 < m) (t : ℕ) (ω : Seed m) :
    CircleSeedIntegrability.Bounded (path N m 1 ω t) (B m t ω) := by
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
    let k := 1/((N:ℝ)*√(m:ℝ))
    have h := CircleSeedIntegrability.bound_step c k (B m t ω) (path N m 1 ω t) (B_one t ω) ih
      (gridPoint N) (fun i => 1+(gridPoint N i).re) (fun i => (grid_norm N i).le) (by
        intro i; exact CircleFlowMoments.circle_label_abs N i)
    have d : 1+|k| *N*(|c| *m+2) ≤ 4 := by
      rw [abs_of_nonneg (by dsimp [k];positivity),abs_of_nonneg (by dsimp [c];positivity)]
      dsimp [k,c]
      field_simp
      nlinarith [mul_nonneg ns.le (sub_nonneg.mpr sr),Real.sq_sqrt (show 0 ≤ (m:ℝ) by positivity)]
    have ub : (1+|k| *N*(|c| *m+2))*(B m t ω)^3 ≤ B m (t+1) ω := by
      apply (mul_le_mul_of_nonneg_right d (pow_nonneg (zero_le_one.trans (B_one t ω)) _)).trans_eq
      simp [B,pow_succ 3,pow_mul]
      ring
    intro j
    exact ⟨(h j).1.trans ub,(h j).2.trans ub⟩

def rawError (N m t : ℕ) (b : ℝ) (ω : Seed m) :=
  trainedMean (path N m 1) t ω - reference N m b ω

theorem raw_envelope (hN : 0 < N) (hm : 0 < m) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) (t : ℕ) (ω : Seed m) :
    |rawError N m t b ω| ≤ (5*m:ℝ)*(4*radius ω)^(2*3^t) := by
  have ms : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have sr : 1 ≤ √(m:ℝ) := one_le_sqrt.mpr ms
  have cr : 1/√(m:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr sr
  have cp : |(1/√(m:ℝ))/π| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_self (by positivity) (by linarith [pi_gt_three])).trans cr
  have y := CircleSeedIntegrability.mean_cap (1/√(m:ℝ)) _ (zero_le_one.trans (B_one t ω)) _ (actual_bound hN hm t ω)
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
  exact (abs_sub _ _).trans (by change |populationMean (1/√(m:ℝ)) (path N m 1 ω t)| + |reference N m b ω| ≤ _; nlinarith only [y,tr,bb,hroot,zr,z1])


def momentDegree (t : ℕ) := 8*3^t

def fourthBound (m t : ℕ) : ℝ := (5*m:ℝ)^4 *
    (4*(1+3*(m:ℝ))*(momentDegree t:ℝ))^(momentDegree t)*exp 9*(6*m)

theorem raw_mem4 (N m t : ℕ) (b : ℝ) : MemLp (rawError N m t b) 4 (seedLaw m) :=
  (trained_memLp N m t 1 4 (by norm_num)).sub (reference_memLp N m b 4 (by norm_num))

/-- The fourth moment of the true unconstrained iteration grows at most like
exp(O(3^t (log(m+1)+t))). No screen or trajectory tube is assumed. -/
theorem raw_fourth (hN : 0 < N) (hm : 0 < m) (t : ℕ) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) :
    ∫ ω, (rawError N m t b ω)^4 ∂seedLaw m ≤ fourthBound m t := by
  let p := momentDegree t
  have pp : 0 < p := by dsimp [p,momentDegree]; positivity
  let K := (5*(m:ℝ))^4*4^p
  have h (ω : Seed m) : (rawError N m t b ω)^4 ≤ K*(radius ω)^p := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (raw_envelope hN hm hb hb' t ω) 4
    rw [(by decide : Even 4).pow_abs,mul_pow,← pow_mul,mul_pow] at h
    have e : (2*3^t)*4 = p := by dsimp [p,momentDegree]; omega
    simpa only [e,K,mul_pow,mul_assoc] using h
  have hm4 : MemLp (rawError N m t b) (4:ℕ) (seedLaw m) := raw_mem4 _ _ _ _
  have hi : Integrable (fun ω => rawError N m t b ω^4) (seedLaw m) := by
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hm4.integrable_norm_pow'
  have ri := (CircleSeedIntegrability.radius_power_mem m p 1 (by norm_num)).integrable (by norm_num)
  have mono := integral_mono hi (ri.const_mul K) h
  rw [integral_const_mul] at mono
  apply (mono.trans (mul_le_mul_of_nonneg_left (radius_moment m p hm pp) (by dsimp [K]; positivity))).trans_eq
  dsimp [fourthBound,K,p]
  simp only [mul_pow]
  ring

/-- A finite decomposition isolates cap control on accepted bad seeds and
charges the unrestricted iteration on the exponentially rarer rejected part. -/
theorem exceptional_mse (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) (E : Set (Seed m)) (me : MeasurableSet E) :
    ∫ ω in E, (rawError N m t b ω)^2 ∂seedLaw m ≤
      1044*m*sqrt ((seedLaw m).real E)+sqrt (fourthBound m t)*exp (-(m:ℝ)/480) := by
  let μ := seedLaw m
  let A := CircleCapMoments.screen N m
  let X := rawError N m t b
  have ma : MeasurableSet A := CircleCapMoments.screen_measurable N m (by omega) odd hm
  have f := raw_mem4 N m t b
  have hi := (f.mono_exponent (by norm_num : (2:ENNReal) ≤ 4)).integrable_sq
  have split : (∫ ω in E, X ω^2 ∂μ) = (∫ ω in E∩A, X ω^2 ∂μ) + ∫ ω in E\A, X ω^2 ∂μ := by
    have union : (E∩A) ∪ (E\A) = E := by ext; simp
    nth_rw 1 [← union]
    exact setIntegral_union (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁.2) (me.diff ma) hi.integrableOn hi.integrableOn
  have ac : (∫ ω in E∩A, X ω^2 ∂μ) ≤ 1044*m*sqrt (μ.real E) := by
    have eq : (∫ ω in E∩A, X ω^2 ∂μ) = ∫ ω in E∩A, CircleCapMoments.cappedSq N m t b ω ∂μ := by
      apply setIntegral_congr_fun (me.inter ma)
      intro ω hω
      have pass := trajectory_on_check N m _ hω.2 (initial ω)
      change (_-_)^2 = (populationMean _ (train _ _ _ _ _)-_)^2
      rw [CircleCapMoments.rate,pass]
      rfl
    rw [eq]
    apply (CircleCapMoments.exceptional_mse N m t hN odd hm ht b hb hb' (E∩A)).trans
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (measureReal_mono Set.inter_subset_left)) (by positivity)
  have rej : μ.real Aᶜ ≤ exp (-(m:ℝ)/240) := by
    convert CircleCapMoments.reject_probability N m hN odd hm using 2
    ext ω
    simp [A,CircleCapMoments.screen]
  have rb := CircleMoment.exceptional_second_moment (F:=X) (CircleGaussianTracking.square_mem f) (E\A)
  have small : sqrt (μ.real (E\A)) ≤ exp (-(m:ℝ)/480) := by
    apply (sqrt_le_sqrt ((measureReal_mono (fun _ h => h.2 : E\A ⊆ Aᶜ)).trans rej)).trans_eq
    rw [show exp (-(m:ℝ)/240) = (exp (-(m:ℝ)/480))^2 by rw [← Real.exp_nat_mul]; congr 1; ring,
      sqrt_sq (exp_pos _).le]
  change (∫ ω in E, X ω^2 ∂μ) ≤ _
  rw [split]
  exact add_le_add ac (rb.trans (mul_le_mul (sqrt_le_sqrt (raw_fourth (by omega) hm t hb hb')) small (sqrt_nonneg _) (sqrt_nonneg _)))


def earlyCap (N : ℕ) := ⌈π^2*log (N:ℝ)⌉₊

/-- Cubic iteration through the prescribed early cap has exponent at most
24 N²⁴; this loose exponent suffices against width N³². -/
theorem early_degree (N : ℕ) (hN : 1 ≤ N) : (momentDegree (earlyCap N):ℝ) ≤ 24*(N:ℝ)^24 := by
  have n1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have np : 0 < (N:ℝ) := by linarith
  have logN := log_nonneg n1
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg π) logN)).le
  change (earlyCap N:ℝ) ≤ π^2*log (N:ℝ)+1 at hceil
  have lp : 0 ≤ log (3:ℝ) := log_nonneg (by norm_num)
  have pp : π^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (show 0 ≤ 4+π by positivity)]
  have k : π^2*log (3:ℝ) ≤ 24 := by
    have ll : log (3:ℝ) ≤ 3/2 := by linarith [log_three_lt_d9]
    exact (mul_le_mul pp ll lp (by norm_num)).trans (by norm_num)
  have ee := mul_le_mul_of_nonneg_right hceil lp
  have e : (earlyCap N:ℝ)*log 3 ≤ log 3+24*log (N:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right k logN]
  have h := exp_le_exp.mpr e
  rw [exp_nat_mul,exp_log (by norm_num : 0 < (3:ℝ)),exp_add,exp_log (by norm_num : 0 < (3:ℝ)),
    show 24*log (N:ℝ) = log ((N:ℝ)^24) by rw [log_pow]; norm_num,exp_log (by positivity)] at h
  simp only [momentDegree,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith

private theorem log_fourthBound (N : ℕ) (hN : 1 ≤ N) :
    log (fourthBound (N^32) (earlyCap N)) ≤ 12000*(N:ℝ)^25 := by
  let n : ℝ := N
  let p : ℕ := momentDegree (earlyCap N)
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast hN
  have np : 0 < n := by linarith
  have pp : 0 < (p:ℝ) := by dsimp [p,momentDegree]; positivity
  have P : (p:ℝ) ≤ 24*n^24 := early_degree N hN
  have n32 : 1 ≤ n^32 := one_le_pow₀ hn
  have lu : log n ≤ n := by linarith [log_le_sub_one_of_pos np]
  have base : 4*(1+3*n^32)*(p:ℝ) ≤ 384*n^56 := by
    have hp := mul_le_mul (show 4*(1+3*n^32) ≤ 16*n^32 by linarith) P pp.le (by positivity)
    nlinarith only [hp]
  have lb := log_le_log (by positivity : 0 < 4*(1+3*n^32)*(p:ℝ)) base
  rw [log_mul (by norm_num : (384:ℝ) ≠ 0) (by positivity),log_pow] at lb
  norm_num only [Nat.cast_ofNat] at lb
  have lbase : log (4*(1+3*n^32)*(p:ℝ)) ≤ 440*n := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 384)]
  have powb := mul_le_mul lbase P pp.le (show 0 ≤ 440*n by positivity)
  change log (((5*((N^32:ℕ):ℝ))^4*(4*(1+3*((N^32:ℕ):ℝ))*(p:ℝ))^p*exp 9)*(6*((N^32:ℕ):ℝ))) ≤ _
  rw [Nat.cast_pow]
  change log (((5*n^32)^4*(4*(1+3*n^32)*(p:ℝ))^p*exp 9)*(6*n^32)) ≤ 12000*n^25
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),log_exp,
    log_mul (by positivity) (by positivity),log_pow,log_pow,
    log_mul (by norm_num : (5:ℝ) ≠ 0) (by positivity),log_mul (by norm_num : (6:ℝ) ≠ 0) (by positivity),log_pow]
  norm_num only [Nat.cast_ofNat]
  have n25 : n ≤ n^25 := le_self_pow₀ hn (by norm_num)
  nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5),
    log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)]

/-- The exponentially rare cap rejection absorbs the global moment growth
throughout the prescribed logarithmic training window. -/
theorem rejected_early (N : ℕ) (hN : 12000000 ≤ N) :
    sqrt (fourthBound (N^32) (earlyCap N))*exp (-((N^32:ℕ):ℝ)/480) ≤ 1/(N:ℝ)^10 := by
  have h1 : 1 ≤ N := le_trans (by decide) hN
  have n1 : (1:ℝ) ≤ N := by exact_mod_cast h1
  have np : 0 < (N:ℝ) := by linarith
  have nl : (12000000:ℝ) ≤ N := by exact_mod_cast hN
  have f := fourthBound (N^32) (earlyCap N)
  have hb := log_fourthBound N h1
  have hp : 0 < fourthBound (N^32) (earlyCap N) := by unfold fourthBound momentDegree; positivity
  have g : (N:ℝ)^7 ≥ 11520000 := by linarith [le_self_pow₀ n1 (by norm_num : 7 ≠ 0)]
  have bound : 12000*(N:ℝ)^25 ≤ (N:ℝ)^32/960 := by
    nlinarith [mul_le_mul_of_nonneg_right g (by positivity : 0 ≤ (N:ℝ)^25)]
  have root : sqrt (fourthBound (N^32) (earlyCap N)) ≤ exp ((N:ℝ)^32/960) := by
    apply sqrt_le_iff.mpr
    refine ⟨(exp_pos _).le,?_⟩
    rw [← exp_log hp,← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
    nlinarith only [hb,bound,pow_nonneg np.le 32]
  rw [Nat.cast_pow]
  apply (mul_le_mul_of_nonneg_right root (exp_pos _).le).trans
  rw [← exp_add,show (N:ℝ)^32/960 + -((N:ℝ)^32)/480 = -((N:ℝ)^32/960) by ring,exp_neg,one_div]
  apply inv_anti₀ (by positivity : (0:ℝ) < (N:ℝ)^10)
  rw [← exp_log (by positivity : (0:ℝ) < (N:ℝ)^10)]
  apply exp_le_exp.mpr
  rw [log_pow]
  norm_num
  have g2 : (N:ℝ)^2 ≤ (N:ℝ)^32 := pow_le_pow_right₀ n1 (by norm_num)
  nlinarith [log_le_sub_one_of_pos np,mul_le_mul_of_nonneg_right nl np.le]

theorem earlyCap_width (N : ℕ) (hN : 3400 ≤ N) : 200*earlyCap N ≤ N^32 := by
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : 0 < (N:ℝ) := by linarith
  have hn : (3400:ℝ) ≤ N := by exact_mod_cast hN
  have hl : log (N:ℝ) ≤ N := by linarith [log_le_sub_one_of_pos hp]
  have pp : π^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (show 0 ≤ 4+π by positivity)]
  have hc := (Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg π) (log_nonneg h1))).le
  change (earlyCap N:ℝ) ≤ π^2*log (N:ℝ)+1 at hc
  have h : 200*(earlyCap N:ℝ) ≤ (N:ℝ)^32 := by
    have n2 : (N:ℝ)^2 ≤ (N:ℝ)^32 := pow_le_pow_right₀ h1 (by norm_num)
    nlinarith [mul_le_mul pp hl (log_nonneg h1) (by norm_num : (0:ℝ) ≤ 16),
      mul_le_mul_of_nonneg_right hn hp.le]
  exact_mod_cast h

/-- At the logarithmic cap and width N^32, any measurable bad set of mass
C/N¹⁵⁸ contributes at most a constant times N⁻¹⁰ to the actual paired MSE. -/
theorem early_bad_mse (N : ℕ) (hN : 12000000 ≤ N) (odd : Odd N) {b C : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) (hC : 0 ≤ C)
    (E : Set (Seed (N^32))) (me : MeasurableSet E)
    (miss : (seedLaw (N^32)).real E ≤ C/(N:ℝ)^158) :
    ∫ ω in E, (rawError N (N^32) (earlyCap N) b ω)^2 ∂seedLaw (N^32) ≤
      (1044*sqrt C+1)/(N:ℝ)^10 := by
  have np : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have n1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := exceptional_mse N (N^32) (earlyCap N) (by omega) odd (pow_pos (by omega) _) (earlyCap_width N (by omega)) hb hb' E me
  apply h.trans
  have prob := sqrt_le_sqrt miss
  rw [sqrt_div hC,show (N:ℝ)^158=((N:ℝ)^79)^2 by ring,sqrt_sq (by positivity)] at prob
  have a := mul_le_mul_of_nonneg_left prob (show 0 ≤ 1044*((N^32:ℕ):ℝ) by positivity)
  apply (add_le_add a (rejected_early N hN)).trans
  rw [Nat.cast_pow,add_div]
  apply add_le_add_left
  have simpler : 1044*(N:ℝ)^32*(sqrt C/(N:ℝ)^79) = 1044*sqrt C/(N:ℝ)^47 := by field_simp
  rw [simpler]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ n1 (by norm_num))

end CircleShortGDTails
