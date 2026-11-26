module

public import CircleSynchronizedEscape
public import CircleFlowMoments
import all CircleFlowMoments
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Gaussian box probabilities and raw moment consequences for
synchronized discrete escape at growing widths and horizons. -/
@[expose] public section
noncomputable section
namespace CircleSynchronizedWidth
open Set Real MeasureTheory ProbabilityTheory Filter Topology CircleSynchronizedEscape
  CircleEscapeBridge CircleSeedIntegrability

def cost (N m T : ℕ) (L : ℝ) : ℝ :=
  3*m*((2*L+1)^2/2+log (8*sqrt (2*π)*N)+T*log 512)

private theorem side_le (N T : ℕ) (hN : 0<N) : 0<side N T ∧ side N T≤1 := by
  have npos : (1:ℝ)≤N := by exact_mod_cast hN
  unfold side
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤512) (n:=T),
      mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ)≤512) (n:=T)) (show 0≤8*(N:ℝ) by positivity)]

private theorem coord_lower (ℓ c R : ℝ) (hℓ : 0≤ℓ) (hR : |c|+ℓ≤R) :
    ℓ*gaussianPDFReal 0 1 R ≤ (gaussianReal 0 1).real (Icc c (c+ℓ)) := by
  have lower (x : ℝ) (hx : x∈Icc c (c+ℓ)) : gaussianPDFReal 0 1 R≤gaussianPDFReal 0 1 x := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    have h : |x| ≤ R := abs_le.mpr ⟨by linarith [hx.1,neg_le_abs c],by linarith [hx.2,le_abs_self c]⟩
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hsq
    linarith
  have bound := setIntegral_ge_of_const_le (μ:=volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) lower (integrable_gaussianPDFReal 0 1).integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith),smul_eq_mul] at bound
  rw [measureReal_def,gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  simpa [add_sub_cancel_left] using bound

theorem mass_formula (N m T : ℕ) (hN : 0<N) (L : ℝ) :
    exp (-cost N m T L) = (side N T*gaussianPDFReal 0 1 (2*L+1))^(3*m) := by
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have hden : 0 < 8*sqrt (2*π)*(N:ℝ) := by positivity
  rw [cost, neg_mul_eq_mul_neg, show (3:ℝ)*(m:ℝ) = ((3*m:ℕ):ℝ) by push_cast; rfl, exp_nat_mul]
  congr 1
  rw [show -((2*L+1)^2/2+log (8*sqrt (2*π)*N)+T*log 512) =
      -((2*L+1)^2/2) - log (8*sqrt (2*π)*N) - T*log 512 by ring,
    exp_sub, exp_sub,exp_log hden,exp_nat_mul,exp_log (by norm_num)]
  simp only [side,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [neg_div]
  ring

theorem gaussian_box_probability (N m T : ℕ) (hN : 0<N) (L σ : ℝ) (hL : 0≤L) (sign : |σ|=1) :
    exp (-cost N m T L) ≤ (seedLaw m).real (syncBox N m T σ L) := by
  have loc (j : Fin 3) : |location σ L j|≤2*L := by
    fin_cases j <;> (simp [location,abs_mul,sign,abs_of_nonneg hL]; try positivity)
  have one (j : Fin 3) := coord_lower (side N T) (location σ L j) (2*L+1) (side_le N T hN).1.le
    (add_le_add (loc j) (side_le N T hN).2)
  rw [mass_formula N m T hN L]
  simp only [seedLaw,syncBox,measureReal_def,Measure.pi_pi,ENNReal.toReal_prod]
  rw [show 3*m=Fintype.card (Fin m × Fin 3) by simp [mul_comm],←Finset.card_univ,←Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => mul_nonneg (side_le N T hN).1.le (gaussianPDFReal_nonneg ..))
    (fun i _ => one i.2)

private theorem ref_cap (N m T : ℕ) (hN : 0<N) (hm : 0<m) (L b : ℝ) (hL : 1≤L)
    (hb : 0≤b) (hb' : b≤1) (ω : Seed m) (box : ω∈syncBox N m T 1 L) :
    |reference N m b ω| ≤ 1+32*sqrt m*L^2 := by
  have cap (i : Fin m × Fin 3) : ω i^2 ≤ (3*L)^2 := by
    have hi := box i (mem_univ _)
    have loc : 0≤location 1 L i.2 ∧ location 1 L i.2≤2*L := by
      unfold location; split_ifs <;> constructor <;> linarith
    change location 1 L i.2≤ω i ∧ ω i≤location 1 L i.2+side N T at hi
    exact pow_le_pow_left₀ (loc.1.trans hi.1) (by linarith [hi.2,loc.2,(side_le N T hN).2]) _
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => cap i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,
    Nat.cast_ofNat] at h
  apply (CircleFlowMoments.reference_cap ω hN hb hb').trans
  unfold CircleFlowMoments.squared
  apply add_le_add_right
  apply le_trans (mul_le_mul_of_nonneg_left h (show 0≤1/sqrt m by positivity))
  have root : (1/sqrt m)*(m:ℝ)=sqrt m := by
    have p : (0:ℝ)<m := by exact_mod_cast hm
    field_simp; nlinarith [sq_sqrt p.le]
  nlinarith [show 1/sqrt m*((m:ℝ)*3*(3*L)^2)=27*sqrt m*L^2 by
    linear_combination (27*L^2)*root,mul_nonneg (sqrt_nonneg (m:ℝ)) (sq_nonneg L)]

/-- Finite variance and paired-MSE lower bounds under the actual unrestricted
product Gaussian law, with a synchronization cost linear in the width. -/
theorem actual_lower (N m T : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) {η L : ℝ}
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (b : ℝ) (hb : 0≤b) (hb' : b≤1) :
    let A := amplitude m T L/2
    let p := exp (-cost N m T L)
    p*A^2 ≤ variance (trainedMean (path N m η) T) (seedLaw m) ∧
      p*(max (A-(1+32*sqrt m*L^2)) 0)^2 ≤ ∫ ω,
        (trainedMean (path N m η) T ω-reference N m b ω)^2 ∂seedLaw m := by
  let F := trainedMean (path N m η) T
  let A := amplitude m T L/2
  have hA : 0≤A := by dsimp [A,amplitude]; positivity
  have hf := trained_memLp N m T η 2 (by norm_num)
  have mass (σ : ℝ) (sign : |σ|=1) := gaussian_box_probability N m T (by omega) L σ hL.le sign
  have pp (ω : Seed m) (hω : ω∈syncBox N m T 1 L) : A≤(-1)^T*F ω := by
    simpa [A,F] using box_escape N m T hN odd hm hη hc hL scale (σ:=1) (by norm_num) ω hω
  have pm (ω : Seed m) (hω : ω∈syncBox N m T (-1) L) : A≤ -((-1)^T*F ω) := by
    simpa [A,F] using box_escape N m T hN odd hm hη hc hL scale (σ:= -1) (by norm_num) ω hω
  constructor
  · rcases Nat.even_or_odd T with he|ho
    · apply CircleTails.variance_of_opposite_tails hf (measurable_syncBox ..) (measurable_syncBox ..)
        hA (mass 1 (by norm_num)) (mass (-1) (by norm_num))
      · simpa [he.neg_one_pow] using pp
      · intro ω hω; have h := pm ω hω; rw [he.neg_one_pow,one_mul] at h; linarith
    · apply CircleTails.variance_of_opposite_tails hf (measurable_syncBox ..) (measurable_syncBox ..)
        hA (mass (-1) (by norm_num)) (mass 1 (by norm_num))
      · simpa [ho.neg_one_pow] using pm
      · intro ω hω; have h := pp ω hω; rw [ho.neg_one_pow,neg_one_mul] at h; linarith
  · apply CircleEscapeMoment.paired_second_moment_of_escape hf (reference_memLp N m b 2 (by norm_num))
      (measurable_syncBox ..) (mass 1 (by norm_num))
    · intro ω hω
      simpa [F,abs_mul,abs_pow] using (pp ω hω).trans (le_abs_self _)
    · have h := (eq_div_iff hη.ne').mp scale
      exact ref_cap N m T (by omega) hm L b (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg L)]) hb hb'

private theorem exponential_lower (N m T : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (hT : 2≤T)
    {η L : ℝ} (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (b : ℝ) (hb : 0≤b) (hb' : b≤1) :
    let B := exp (4*log 2*(3:ℝ)^T-cost N m T L)
    B ≤ variance (trainedMean (path N m η) T) (seedLaw m) ∧
      B ≤ ∫ ω,(trainedMean (path N m η) T ω-reference N m b ω)^2 ∂seedLaw m := by
  let a := (2:ℝ)^(3^T:ℕ)
  let l := sqrt m*L^2
  have mh : 1≤sqrt m := one_le_sqrt.mpr (by exact_mod_cast hm)
  have l40 : 40≤L^2 := by rw [scale]; exact le_div_self (by norm_num) hη hc
  have size : 40≤l := by dsimp [l]; nlinarith [mul_le_mul_of_nonneg_right mh (sq_nonneg L)]
  have alpha : 256≤a := by
    apply (show (256:ℝ) = 2^8 by norm_num).le.trans
    exact pow_le_pow_right₀ (by norm_num) ((by decide : 8≤3^2).trans (Nat.pow_le_pow_right (by decide) hT))
  have floor : a^2+(1+32*sqrt m*L^2) ≤ amplitude m T L/2 := by
    rw [amplitude,show sqrt m/π*(L*2^(3^T:ℕ))^2/2=l*a^2/(2*π) by dsimp [l,a]; ring]
    apply (le_div_iff₀ (by positivity)).mpr
    change _ ≤ l*a^2
    have p : 0≤a^2+(1+32*sqrt m*L^2) := by positivity
    have t := mul_le_mul_of_nonneg_left (show 2*π≤8 by linarith [pi_lt_four]) p
    have aux : 65536≤a^2 := by nlinarith [sq_nonneg (a-256)]
    dsimp only [l] at size ⊢
    nlinarith only [t, mul_nonneg (sub_nonneg.mpr size) (sub_nonneg.mpr aux),size,aux]
  have hA := actual_lower N m T hN odd hm hη hc hL scale b hb hb'
  have pos : 0 ≤ 1+32*sqrt m*L^2 := by positivity
  have hpow : exp (4*log 2*(3:ℝ)^T) = (a^2)^2 := by
    have e : exp ((3:ℝ)^T*log 2)=a := by
      simpa [a,exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_nat_mul (log 2) (3^T)
    rw [show 4*log 2*(3:ℝ)^T = (2:ℕ)*((2:ℕ)*((3:ℝ)^T*log 2)) by push_cast; ring,
      exp_nat_mul,exp_nat_mul,e]
  rw [sub_eq_add_neg,exp_add,hpow,mul_comm]
  constructor
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg a) (by linarith only [floor,pos]) 2)
      (exp_pos _).le).trans hA.1
  · have bound : a^2 ≤ max (amplitude m T L/2-(1+32*sqrt m*L^2)) 0 :=
      (show _≤amplitude m T L/2-(1+32*sqrt m*L^2) by linarith only [floor]).trans (le_max_left ..)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg a) bound 2) (exp_pos _).le).trans hA.2

/-- Both unconditional moments diverge whenever the synchronization cost is
eventually below the leading cubic amplification exponent by a fixed factor. -/
theorem divergence_of_cost (N m T : ℕ → ℕ) (b : ℕ → ℝ) (η L : ℝ)
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j ∧ 0≤b j ∧ b j≤1)
    {c : ℝ} (less : c<4*log 2) (cost_cap : ∀ᶠ j in atTop, cost (N j) (m j) (T j) L ≤ c*3^(T j)) :
    Tendsto (fun j => variance (trainedMean (path (N j) (m j) η) (T j)) (seedLaw (m j))) atTop atTop ∧
    Tendsto (fun j => ∫ ω,(trainedMean (path (N j) (m j) η) (T j) ω-reference (N j) (m j) (b j) ω)^2
      ∂seedLaw (m j)) atTop atTop := by
  have div := (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (sub_pos.mpr less)
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3)).comp grow)))
  have bound := Filter.Eventually.and valid (cost_cap.and (grow.eventually_ge_atTop 2))
  constructor <;> apply tendsto_atTop_mono' atTop _ div <;>
    filter_upwards [bound] with j hj
  all_goals obtain ⟨⟨n,o,m',bp,bc⟩,h,hT⟩ := hj
  all_goals have base := exponential_lower _ _ _ n o m' hT hη hc hL scale (b j) bp bc
  all_goals have le : exp ((4*log 2-c)*(3:ℝ)^(T j)) ≤ exp (4*log 2*(3:ℝ)^(T j)-cost (N j) (m j) (T j) L) :=
    exp_le_exp.mpr (by linarith only [h])
  · exact le.trans base.1
  · exact le.trans base.2

/-- For every fixed admissible step, grids of at most exponential growth
in T and widths of any exponential rate strictly below log 3 have divergent
actual Euler variance and same-seed interpolation-reference MSE. -/
theorem divergence_below_log_three (N m T : ℕ → ℕ) (b : ℕ → ℝ) (η : ℝ)
    (hη : 0<η) (hc : η≤1) (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j ∧ 0≤b j ∧ b j≤1)
    {c K : ℝ} (less : c<log 3)
    (grid : ∀ᶠ j in atTop, log (N j)≤K*(T j:ℝ))
    (width : ∀ᶠ j in atTop, log (m j)≤c*(T j:ℝ)) :
    Tendsto (fun j => variance (trainedMean (path (N j) (m j) η) (T j)) (seedLaw (m j))) atTop atTop ∧
    Tendsto (fun j => ∫ ω,(trainedMean (path (N j) (m j) η) (T j) ω-reference (N j) (m j) (b j) ω)^2
      ∂seedLaw (m j)) atTop atTop := by
  let L := sqrt (40/η)
  have hL : 0<L := sqrt_pos.mpr (by positivity)
  have sc : L^2=40/η := sq_sqrt (by positivity)
  let C := (2*L+1)^2/2+log (8*sqrt (2*π))
  let D := 3*(|C|+|K|+|log 512|+1)
  have gd := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have elim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (log 3-c) (sub_pos.mpr less)).comp gd).const_mul D
  have small : ∀ᶠ j in atTop, D*((T j:ℝ)*exp (-(log 3-c)*(T j:ℝ))) ≤ log 2 := by
    simpa [Function.comp_def] using elim.eventually_le_const (show D*0<log 2 by simp [log_pos (by norm_num : (1:ℝ)<2)])
  apply divergence_of_cost N m T b η L hη hc hL sc grow valid (c:=log 2)
    (by linarith [log_pos (by norm_num : (1:ℝ)<2)])
  filter_upwards [valid,grid,width,small,grow.eventually_ge_atTop 1] with j v g w little ht
  have np : (0:ℝ)<N j := by exact_mod_cast (show 0<N j by omega)
  have mp : (0:ℝ)<m j := by exact_mod_cast v.2.2.1
  have tp : (1:ℝ)≤T j := by exact_mod_cast ht
  have nlog := log_mul (show 8*sqrt (2*π)≠0 by positivity) np.ne'
  have bnd : cost (N j) (m j) (T j) L ≤ D*((T j:ℝ)*(m j:ℝ)) := by
    unfold cost D
    rw [nlog]
    have cb : C ≤ |C| * (T j:ℝ) := (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg _) tp)
    have gb := mul_le_mul_of_nonneg_right (le_abs_self K) (zero_le_one.trans tp)
    have lb := mul_le_mul_of_nonneg_right (le_abs_self (log 512)) (zero_le_one.trans tp)
    apply le_trans (mul_le_mul_of_nonneg_left (show _ ≤ (|C|+|K|+|log 512|+1)*(T j:ℝ) by
      dsimp only [C] at cb; linarith only [cb,g,gb,lb,tp]) (by positivity : 0≤3*(m j:ℝ))) _
    ring_nf
    exact le_rfl
  have mw := (Real.log_le_iff_le_exp mp).mp w
  have dpos : 0≤D := by dsimp [D]; positivity
  have gain : exp (c*(T j:ℝ)) = exp (-(log 3-c)*(T j:ℝ))*(3:ℝ)^(T j) := by
    rw [show (3:ℝ)^(T j) = exp ((T j:ℝ)*log 3) by rw [exp_nat_mul,exp_log (by norm_num)],←exp_add]
    congr 1
    ring
  apply bnd.trans
  calc
    _ ≤ D*((T j:ℝ)*exp (c*(T j:ℝ))) := by gcongr
    _ = (D*((T j:ℝ)*exp (-(log 3-c)*(T j:ℝ))))*(3:ℝ)^(T j) := by rw [gain]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right little (by positivity)

/-- For m=N³² and T bounded below by c log N, the synchronized boxes already
force divergence as soon as c log 3>32, on every growing odd grid. -/
theorem polynomial_schedule (N T : ℕ → ℕ) (b : ℕ → ℝ) (η : ℝ) (hη : 0<η) (hc : η≤1)
    (grow : Tendsto N atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0≤b j ∧ b j≤1)
    {c : ℝ} (crit : 32<c*log 3) (sched : ∀ᶠ j in atTop, c*log (N j) ≤ (T j:ℝ)) :
    Tendsto (fun j => variance (trainedMean (path (N j) (N j^32) η) (T j)) (seedLaw (N j^32))) atTop atTop ∧
    Tendsto (fun j => ∫ ω,(trainedMean (path (N j) (N j^32) η) (T j) ω-
      reference (N j) (N j^32) (b j) ω)^2 ∂seedLaw (N j^32)) atTop atTop := by
  have lp : 0<log 3 := log_pos (by norm_num)
  have cp : 0<c := by by_contra! h; linarith [mul_nonpos_of_nonpos_of_nonneg h lp.le]
  have hg := tendsto_atTop_mono' atTop sched (Tendsto.const_mul_atTop cp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)))
  have ht : Tendsto T atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [hg.eventually_ge_atTop (n:ℝ)] with j hj
    exact_mod_cast hj
  refine divergence_below_log_three N (fun j => N j^32) T b η hη hc ht ?_ (c:=32/c) (K:=1/c)
    ((div_lt_iff₀ cp).mpr (by linarith only [crit])) ?_ ?_
  · filter_upwards [valid] with j h
    exact ⟨h.1,h.2.1,pow_pos (by omega) _,h.2.2⟩
  · filter_upwards [sched] with j h
    rw [show 1/c*(T j:ℝ)=(T j:ℝ)/c by ring]
    exact (le_div_iff₀ cp).mpr (by linarith only [h])
  · filter_upwards [sched] with j h
    rw [Nat.cast_pow,log_pow]
    have w := mul_le_mul_of_nonneg_left h (show (0:ℝ)≤32/c by positivity)
    convert w using 1
    push_cast
    field_simp

/-- If log N=o(T), the same mechanism permits m as large as c·3ᵀ/T
for any positive c<4/27, including on the long fitting horizon. -/
theorem divergence_at_critical_scale (N m T : ℕ → ℕ) (b : ℕ → ℝ) (η : ℝ) (hη : 0<η) (hc : η≤1)
    (grow : Tendsto T atTop atTop) (smallGrid : Tendsto (fun j => log (N j)/(T j:ℝ)) atTop (nhds 0))
    (valid : ∀ᶠ j in atTop, 3≤N j ∧ Odd (N j) ∧ 0<m j ∧ 0≤b j ∧ b j≤1)
    {c : ℝ} (pos : 0<c) (crit : c<4/27)
    (width : ∀ᶠ j in atTop, (m j:ℝ)*(T j:ℝ) ≤ c*3^(T j)) :
    Tendsto (fun j => variance (trainedMean (path (N j) (m j) η) (T j)) (seedLaw (m j))) atTop atTop ∧
    Tendsto (fun j => ∫ ω,(trainedMean (path (N j) (m j) η) (T j) ω-reference (N j) (m j) (b j) ω)^2
      ∂seedLaw (m j)) atTop atTop := by
  let L := sqrt (40/η)
  let C := (2*L+1)^2/2+log (8*sqrt (2*π))
  have l2 : 0<log 2 := log_pos (by norm_num)
  have l512 : log 512=9*log 2 := by rw [show (512:ℝ)=2^9 by norm_num,log_pow]; norm_num
  have gap : 3*c*log 512<4*log 2 := by
    rw [l512]
    nlinarith [mul_lt_mul_of_pos_right crit l2]
  let ε := (4*log 2-3*c*log 512)/(6*c)
  have ep : 0<ε := div_pos (sub_pos.mpr gap) (by positivity)
  have hs : 3*c*(log 512+ε)<4*log 2 := by
    have eq := (div_mul_cancel₀ (4*log 2-3*c*log 512) (show 6*c≠0 by positivity))
    dsimp [ε]
    linarith only [eq,gap]
  have g := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have raw : Tendsto (fun j => (C+log (N j))/(T j:ℝ)) atTop (nhds 0) := by
    simpa [add_div,div_eq_mul_inv,add_mul,Function.comp_def] using (g.inv_tendsto_atTop.const_mul C).add smallGrid
  apply divergence_of_cost N m T b η L hη hc (sqrt_pos.mpr (by positivity)) (sq_sqrt (by positivity))
    grow valid hs
  filter_upwards [valid, width, raw.eventually_le_const ep,grow.eventually_gt_atTop 0] with j v w a t
  have npos : (0:ℝ)<N j := by exact_mod_cast (show 0<N j by omega)
  have tp : (0:ℝ)<T j := by exact_mod_cast t
  have q := (div_le_iff₀ tp).mp a
  have g0 := Real.log_nonneg (by norm_num : (1:ℝ)≤512)
  apply le_trans _ (show (3*(log 512+ε))*((m j:ℝ)*(T j:ℝ)) ≤
      (3*c*(log 512+ε))*3^(T j) by
    convert mul_le_mul_of_nonneg_left w (show 0≤3*(log 512+ε) by positivity) using 1; ring)
  unfold cost
  rw [log_mul (show 8*sqrt (2*π)≠0 by positivity) npos.ne']
  have a' := mul_le_mul_of_nonneg_left q (show 0≤3*(m j:ℝ) by positivity)
  dsimp [C] at a'
  linarith only [a']
end CircleSynchronizedWidth
