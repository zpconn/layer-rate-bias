module

public import CirclePairedGDClock
public import CirclePositiveWidth
public import CirclePairedOrdering
import all CircleWeightedDynamics
import all CirclePositiveConfidence
import all CircleFiniteConfidence
import all CircleGaussianTracking
import all CircleRateTrajectory
import all CirclePairedCoefficient
import all CirclePairedOrdering
import Mathlib.Tactic

/-! The paired discrete update at the manuscript's common deterministic horizon.
All events use the original joint Gaussian law on the same network seed. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDTypical
open Real MeasureTheory Filter Topology CircleEscapeBridge CircleFlowPath CircleActualTracking
  CircleWeightedDynamics CircleFiniteConfidence CirclePositiveConfidence CircleSpectrum
  CircleFlowTracking CirclePairedGDClock

private theorem preparation {N : ℕ} (hx : 1000000≤(N:ℝ)) {τ b : ℝ}
    (lo : 1/2≤τ) (hi : τ≤2) (b0 : 0≤b) (b1 : b≤1) :
    let x : ℝ := N
    let δ := 1/sqrt x
    let A := x^4
    let ρ := 1/x^12
    let err := 160/x^12
    let R := sqrt (12/δ)
    (36/δ≤x^32 ∧ 10*(x+1)/(δ*A)≤x^16) ∧
    (mult τ*gridScale N δ/x^16≤err ∧ mult τ*signedScale N b δ/x^16≤err) ∧
    (2*scale τ/x^16*R≤ρ*CirclePairedGDClock.rate x ∧ scale τ*(36*ρ)+err≤τ/(π*x)^2-CirclePairedGDClock.rate x) ∧
    (err+(1+b)*(scale τ*(36*ρ)))*(R/CirclePairedGDClock.rate x)≤1/x^4 := by
  intro x δ A ρ err R
  change 1000000≤x at hx
  have x1 : 1≤x := by linarith
  have xp : 0<x := by linarith
  have sp := Real.sqrt_pos.mpr xp
  have sx : sqrt x≤x := by nlinarith [Real.sq_sqrt xp.le,Real.sqrt_nonneg x]
  have s1 : 1≤sqrt x := by simpa using Real.sqrt_le_sqrt x1
  have dp : 0<δ := by dsimp [δ]; positivity
  have cp : 0≤mult τ := (by norm_num : (0:ℝ)≤1).trans (le_max_left ..)
  have c2 : mult τ≤2 := max_le (by norm_num) hi
  have rate2 : scale τ≤2 := c2
  obtain ⟨kp,_,kr⟩ := rate_bounds x1
  have ax (i j : ℕ) (h : i+1≤j) := absorb hx (a:=i) (b:=j) h
  have cmp (i j : ℕ) (h : i≤j) : x^i ≤ x^j := pow_le_pow_right₀ x1 h
  have sqr : x≤x^2 := by simpa using cmp 1 2 (by decide)
  have rle : R≤4*x := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    dsimp only [δ];field_simp
    nlinarith only [sx,sqr,xp]
  have dle : R/CirclePairedGDClock.rate x≤160*x^3 := by
    apply (div_le_iff₀ kp).mpr
    calc
      R ≤ 4*x := rle
      _ ≤ 4*x*(CirclePairedGDClock.rate x*(40*x^2)) := by
        conv_lhs => rw [←mul_one (4*x)]
        exact mul_le_mul_of_nonneg_left kr (by positivity)
      _ = _ := by ring
  have grids : gridScale N δ ≤ 10*x^2 := by
    change x*sqrt (90/(1/sqrt x))≤_
    have hb : sqrt (90/(1/sqrt x))≤10*x := by
      apply sqrt_le_iff.mpr; refine ⟨by positivity,?_⟩
      field_simp
      nlinarith only [sx,sqr,xp]
    nlinarith only [mul_le_mul_of_nonneg_left hb xp.le]
  have rows : rowScale N δ ≤ 10*x := by
    change sqrt (90*x/(1/sqrt x))≤_
    apply sqrt_le_iff.mpr; refine ⟨by positivity,?_⟩
    field_simp
    nlinarith only [sx,xp]
  have srows : signedScale N b δ ≤ 70*x := by
    have coef : 6/x+1-b≤7 := by
      have h : 6/x≤6 := (div_le_iff₀ xp).mpr (by linarith)
      linarith
    have := mul_le_mul coef rows (sqrt_nonneg _) (by norm_num : (0:ℝ)≤7)
    dsimp [signedScale]; linarith
  have gbound := mul_le_mul c2 grids (by unfold gridScale;positivity) (by norm_num : (0:ℝ)≤2)
  have vb := mul_le_mul_of_nonneg_left srows cp
  have vbound : mult τ*signedScale N b δ ≤ 140*x := by
    exact vb.trans ((mul_le_mul_of_nonneg_right c2 (by positivity : 0≤70*x)).trans_eq (by ring))
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · dsimp [δ];field_simp
    nlinarith only [sx,ax 1 32 (by decide),xp]
  · apply (div_le_iff₀ (mul_pos dp (pow_pos xp 4))).mpr
    dsimp [δ,A];field_simp
    nlinarith only [mul_le_mul_of_nonneg_left sx (show 0≤10*(x+1) by positivity),ax 2 20 (by decide),sqr,xp]
  · dsimp [err]; rw [show x^16=x^12*x^4 by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    apply (mul_le_mul_of_nonneg_right gbound (pow_nonneg xp.le 12)).trans
    nlinarith only [mul_le_mul_of_nonneg_right (cmp 2 4 (by decide)) (pow_nonneg xp.le 12),pow_nonneg xp.le 16]
  · dsimp [err]; rw [show x^16=x^12*x^4 by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    apply (mul_le_mul_of_nonneg_right vbound (pow_nonneg xp.le 12)).trans
    nlinarith only [mul_le_mul_of_nonneg_right (show x≤x^4 by simpa using cmp 1 4 (by decide)) (pow_nonneg xp.le 12),pow_nonneg xp.le 16]
  · have z : 2*scale τ*R ≤ 16*x := by
      have z := mul_le_mul rate2 rle (sqrt_nonneg _) (by norm_num : (0:ℝ)≤2)
      linarith
    have B : 16*x*(40*x^2) ≤ x^4 := by
      nlinarith only [ax 3 4 (by decide),pow_nonneg xp.le 3]
    have B' := mul_le_mul_of_nonneg_right B kp.le
    have K := mul_le_mul_of_nonneg_left kr (by positivity : 0≤16*x)
    have key : 2*scale τ*R≤x^4*CirclePairedGDClock.rate x := by nlinarith only [z,B',K]
    dsimp [ρ];field_simp
    exact key
  · have gapLower : 1/(32*(π*x)^2) ≤ τ/(π*x)^2-CirclePairedGDClock.rate x := by
      unfold CirclePairedGDClock.rate;field_simp
      nlinarith only [lo]
    apply le_trans _ gapLower
    have p16 : π^2≤16 := by nlinarith [pi_lt_four,pi_pos]
    dsimp [ρ,err]
    field_simp
    have cpi := mul_le_mul rate2 p16 (sq_nonneg _) (by norm_num : (0:ℝ)≤2)
    nlinarith only [cpi,p16,ax 0 10 (by decide)]
  · have ub : err+(1+b)*(scale τ*(36*ρ)) ≤ 304/x^12 := by
      dsimp [err,ρ];field_simp
      have S := mul_le_mul_of_nonneg_right (by linarith : 1+b≤2) cp
      change (1+b)*scale τ≤2*scale τ at S
      nlinarith only [S,rate2]
    have ab := mul_le_mul ub dle (div_nonneg (sqrt_nonneg _) kp.le) (by positivity : 0≤304/x^12)
    apply ab.trans
    field_simp
    nlinarith only [ax 0 5 (by decide)]

private theorem one_rate (n : ℕ) (hn : 4^32≤n+1) (odd : Odd (n+1)) (τ : ℝ) (lo : 1/2≤τ) (hi : τ≤2) :
    let N := n+1
    let m := N^32
    let x : ℝ := N
    let T := horizon x
    let w := x^(1/32:ℝ)
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤1/sqrt x ∧ ∀ z∈E,
      rms τ 1 N z T≤1/x^3 ∧
      |learnerMean τ 1 N z T-reference N m (weight τ n) z| ≤ 5/w^97 := by
  intro N m x T w
  have hN : 3≤N := by change 3≤n+1; omega
  have hlarge : (4:ℝ)^32≤x := by
    dsimp [x,N]; exact_mod_cast hn
  have hx : 1000000≤x := (by norm_num : (1000000:ℝ)≤4^32).trans hlarge
  have xp : 0<x := by linarith
  have hp : 0<τ := by linarith
  have hm : 0<m := by dsimp [m];exact pow_pos (by omega) _
  obtain ⟨hw,ww⟩ := root_spec hlarge
  change 4≤w at hw; change w^32=x at ww
  have wp : 0<w := by linarith
  let b := weight τ n
  let δ := 1/sqrt x
  let A := x^4
  let ρ := 1/x^12
  let err := 160/x^12
  let R := sqrt (12/δ)
  let k := CirclePairedGDClock.rate x
  have bnds := CircleGaussianTracking.weight_bounds n hp.le
  change 0≤b ∧ b≤1 at bnds
  have sqrtm : sqrt (m:ℝ)=x^16 := by
    dsimp only [m,x];push_cast; rw [show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have eqm : (m:ℝ)=x^32 := by dsimp [m,x]; push_cast; rfl
  have ar : A/sqrt (m:ℝ)=ρ := by dsimp [A,ρ];rw [sqrtm]; field_simp
  have r0 : 0≤ρ := by dsimp [ρ];positivity
  have r1 : ρ≤1 := by
    dsimp [ρ]; exact (div_le_one (pow_pos xp _)).2 (one_le_pow₀ (by linarith))
  have posδ : 0<δ := by dsimp [δ];positivity
  have ltδ : δ<1 := by
    dsimp [δ]; apply (div_lt_one (sqrt_pos.mpr xp)).mpr
    exact (by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by linarith : 1<x))
  have opts := preparation (N:=N) hx lo hi bnds.1 bnds.2
  obtain ⟨⟨energy,margin⟩,⟨gg,vv⟩,⟨cash,drift⟩,proj⟩ := opts
  have Apos : 0<A := pow_pos xp _
  have en : 36/δ≤(m:ℝ) := by rw [eqm]; exact energy
  have mar : 10*(((n+1:ℕ)+1:ℕ):ℝ)/(δ*A)≤sqrt (m:ℝ) := by
    rw [sqrtm]; change 10*((N+1:ℕ):ℝ)/(δ*A)≤x^16
    rw [Nat.cast_add_one];exact margin
  obtain ⟨E,em,pe,he⟩ := CirclePositiveConfidence.six_tests τ hp.le n m hN odd hm δ A
    posδ ltδ Apos (ar ▸ r1) en mar
  refine ⟨E,em,pe,?_⟩
  intro z hz
  have I := he z hz
  have G : Bounds N τ b ρ R err err z := by
    refine ⟨I.residual,I.energy,?_,?_,?_,?_⟩
    · intro i;simpa only [ar] using I.gridMargin i
    · simpa only [ar] using I.angular
    · intro i j;exact (I.gram i j).trans (sqrtm ▸ gg)
    · intro i;exact (I.signed i).trans (sqrtm ▸ vv)
  obtain ⟨kp,k1,_⟩ := rate_bounds (by linarith : 1≤x)
  have ep : 0≤err := by dsimp [err]; positivity
  have C := CircleWeightedDynamics.unit_trajectory hN hm odd z hp hi bnds.1 r0 r1 ep ep kp
    (by simpa using k1) G (sqrtm ▸ cash) drift
  have rc : rms τ 1 N z T≤4/w^97 := by
    exact ((C.1 T).1.trans_eq (by rw [one_mul])).trans (residual_clock hw ww)
  have term : 1/x^4≤1/w^97 := by
    apply one_div_le_one_div_of_le (pow_pos wp _)
    rw [←ww,← pow_mul]
    exact pow_le_pow_right₀ (by linarith) (by decide)
  refine ⟨rc.trans ?_, ((C.1 T).2.2.trans ?_)⟩
  · rw [←ww,←pow_mul]
    apply (div_le_div_iff₀ (pow_pos wp _) (pow_pos wp _)).2
    change 4*w^96 ≤ 1*w^97
    nlinarith only [mul_le_mul_of_nonneg_right hw (pow_nonneg wp.le 96)]
  · have h := mul_le_of_le_one_left (show 0≤rms τ 1 N z T from norm_nonneg _) bnds.2
    refine (add_le_add (h.trans rc) (proj.trans term)).trans_eq ?_
    ring

/-- Simultaneous high-probability fit and population response for a readout
step of one and the two prescribed hidden steps, at the manuscript clock. -/
theorem common_event :
    ∀ᶠ n : ℕ in atTop, ∀ _ : Odd (n+1),
    let N := n+1
    let m := N^32
    let x : ℝ := N
    let H := horizon x
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤2/sqrt x ∧ ∀ z∈E,
      rms (1/2) 1 N z H≤1/x^3 ∧ rms 2 1 N z H≤1/x^3 ∧
      |x^2*(learnerMean (1/2) 1 N z H-learnerMean 2 1 N z H)-
        CirclePairedOrdering.coefficient n*CirclePairedCoefficient.score N m z| ≤ 10/x^(33/32:ℝ) := by
  filter_upwards [eventually_ge_atTop (4^32 : ℕ)] with n h odd
  intro N m x H
  have hn : 4^32≤n+1 := by omega
  have hlarge : (4:ℝ)^32≤x := by dsimp [x,N];exact_mod_cast hn
  let w := x^(1/32:ℝ)
  obtain ⟨hw,ww⟩ := root_spec hlarge
  change 4≤w at hw; change w^32=x at ww
  have xp : 0<x := by norm_num at hlarge;linarith
  obtain ⟨E,em,eb,e⟩ := one_rate n hn odd (1/2) (by norm_num) (by norm_num)
  obtain ⟨F,fm,fb,f⟩ := one_rate n hn odd 2 (by norm_num) (by norm_num)
  refine ⟨E∩F,em.inter fm,?_,?_⟩
  · rw [Set.compl_inter]
    exact (measureReal_union_le _ _).trans ((add_le_add eb fb).trans_eq (by ring))
  intro z hz
  obtain ⟨ea,ey⟩ := e z hz.1
  obtain ⟨fa,fy⟩ := f z hz.2
  refine ⟨ea,fa,?_⟩
  let Es := learnerMean (1/2) 1 N z H - reference N m (weight (1/2) n) z
  let Ef := learnerMean 2 1 N z H - reference N m (weight 2 n) z
  have eq : x^2*(learnerMean (1/2) 1 N z H-learnerMean 2 1 N z H)-
      CirclePairedOrdering.coefficient n*CirclePairedCoefficient.score N m z=x^2*(Es-Ef) := by
    simp only [Es,Ef,CirclePairedOrdering.coefficient,CirclePairedCoefficient.score,reference]
    dsimp only [x,N];push_cast;ring
  rw [eq,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have ee : |Es-Ef|≤5/w^97+5/w^97 := (abs_sub _ _).trans (add_le_add ey fy)
  apply (mul_le_mul_of_nonneg_left ee (sq_nonneg x)).trans_eq
  have hr : w^33=x^(33/32:ℝ) := by simpa [w] using root_pow xp 33
  rw [←hr]
  change x^2*(5/w^97+5/w^97)=10/w^33
  rw [←ww]
  field_simp
  ring

end CirclePairedGDTypical
