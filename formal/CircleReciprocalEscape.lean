module

public import CircleEulerLimits
public import CircleFlowTracking
public import CircleReciprocal
public import CircleGridMargin
import all CircleReciprocal
import all CircleFlowTracking
import Mathlib.Analysis.Complex.ExponentialBounds
import all CircleEscape
import all CircleCapMoments
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleCapInduction
import all CircleInitializationCheck
import all CircleGridMargin
import Mathlib.Tactic

/-! On shrinking positive boxes, curvature vanishes quadratically while the
first simultaneous increment grows inversely with the box radius. -/
public section
noncomputable section
namespace CircleReciprocalEscape
open Real Set Filter Finset CircleEscape CircleEscapeBridge CircleCapInduction CircleCapMoments
open CircleSeedIntegrability CircleInitializationCheck
open scoped Topology NNReal
variable {N m : ℕ}

private theorem step_cone {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x : Fin N → V) (y : Fin N → ℝ) (c k L σ s : ℝ) (n : Net V m)
    (hc : 0 < c) (hk : 0 < k) (hL : 0 < L) (hu : ∀ i, ‖x i‖ ≤ 1)
    (cover : ∀ w, ∃ i, ‖w‖/2 ≤ feature w (x i)) (hy : ∀ i, σ*y i ≤ 2)
    (unitSign : σ^2 = 1) (large : 2*L ≤ s) (state : Cone n σ s)
    (scale : 16 ≤ k*c*L^2) (noise : 16*N ≤ c*s^2) :
    Cone (step x y c k n) (-σ) (s^3/L^2) := by
  intro j
  let W := ‖n.w j‖
  let A := σ*n.a j
  let D := k*∑ i, σ*(output c n (x i)-y i)*feature (n.w j) (x i)
  let grad := ∑ i, (output c n (x i)-y i)*feature (n.w j) (x i)
  have hA : s ≤ A := (state j).1
  have hW : s ≤ W := (state j).2
  have hW0 : 0 ≤ W := norm_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have key := signed_gradient x y n c σ hc.le hu hy
    (fun i => hs0.trans (state i).1) cover j
  have dk : k*(c*A*W^2/4 - 2*N*W) ≤ D := mul_le_mul_of_nonneg_left key hk.le
  have hsize : 16*(N:ℝ) ≤ c*(A*W) := by
    apply noise.trans
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [sq]
    exact mul_le_mul hA hW hs0 (hs0.trans hA)
  have prod := mul_le_mul_of_nonneg_right hsize hW0
  have hlow : k*(c*A*W^2/8) ≤ D := by
    apply le_trans _ dk
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  have hD : 2*A*W^2 ≤ D*L^2 := by
    have hg := mul_le_mul_of_nonneg_right hlow (sq_nonneg L)
    calc
      _ ≤ (k*c*L^2) * A*W^2/8 := by
        have ap := hs0.trans hA
        have := mul_le_mul_of_nonneg_right scale (show 0≤A*W^2/8 by positivity)
        linarith only [this]
      _ ≤ _ := by linarith
  have hsplit : D = k*σ*grad := by
    dsimp [D,grad]
    simp only [mul_assoc, ← Finset.mul_sum]
  have hiden := hidden_projection x y c k n j
  have hproject : A*D-W^2 ≤ W*‖(step x y c k n).w j‖ := by
    calc
      _ = -inner ℝ (n.w j) ((step x y c k n).w j) := by
        rw [hiden, hsplit]
        dsimp [A,grad,W]
        linear_combination (n.a j*k*(∑ i, (output c n (x i)-y i)*feature (n.w j) (x i))) * unitSign
      _ ≤ _ := by simpa using real_inner_le_norm (-(n.w j)) ((step x y c k n).w j)
  obtain ⟨ha, hw⟩ := CircleGrowth.cone_step A W L s D _ hL large hA hW hD hproject
  refine ⟨ha.trans_eq ?_, hw⟩
  rw [hsplit]
  dsimp [A,grad,step]
  ring

private theorem box_coords {r : ℝ} {z : Seed m} (hz : z∈box m r false) (i : Fin m × Fin 3) :
    2*r≤z i ∧ z i≤3*r := hz i (Set.mem_univ _)

private theorem box_net {r : ℝ} (hr : 0<r) {z : Seed m} (hz : z∈box m r false) :
    Bounded (initial z) (6*r) := by
  intro j
  have a := box_coords hz (j,0)
  have b := box_coords hz (j,1)
  have c := box_coords hz (j,2)
  change |z (j,0)|≤_ ∧ ‖(initial z).w j‖≤_
  constructor
  · rw [abs_of_nonneg (by linarith)];linarith
  · apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |z (j,1)|+|z (j,2)|≤_
    rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
    linarith

/-- The actual reciprocal step divided by N√m is bounded below by K/r² on
the entire shrinking box, with K independent of its radius and seed. -/
theorem large_step (N m : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c) :
    ∃ K : ℝ, 0<K ∧ ∀ r>0, ∀ z∈box m r false,
      K/r^2 ≤ CircleReciprocal.rate N m c z/(N*sqrt m) := by
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have Cpos : 0<C N := by unfold C;positivity
  refine ⟨c/(27*C N*(N*sqrt m)),by positivity,?_⟩
  intro r hr z hz
  have bound (i : Fin m × Fin 3) := box_coords hz i
  have nz (j : Fin m) : (initial z).w j≠0 := by
    intro h
    have zero : z (j,1)=0 := congrArg Complex.re h
    linarith [(bound (j,1)).1]
  have ee : (2*r)^2*3 ≤ energy (initial z) ∧ energy (initial z) ≤ 27*r^2 := by
    have s₁ := sum_le_sum (s:=univ) (fun (i : Fin m × Fin 3) _ =>
      pow_le_pow_left₀ (by positivity : 0≤2*r) (bound i).1 2)
    have s₂ := sum_le_sum (s:=univ) (fun (i : Fin m × Fin 3) _ =>
      pow_le_pow_left₀ ((by positivity : 0≤2*r).trans (bound i).1) (bound i).2 2)
    simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at s₁ s₂
    rw [energy,initial_energy_coordinates]
    constructor
    · exact (le_div_iff₀ mp).mpr (by linarith only [s₁])
    · exact (div_le_iff₀ mp).mpr (by linarith only [s₂])
  obtain ⟨top,upp⟩ := initial_top N m hn odd hm (initial z)
  have lower := gram_lower (gridPoint N) (initial z) (by omega) hm (1/4) _ (by norm_num) nz (fun w =>
    (by ring : (N:ℝ)*(1/4)*‖w‖=(N:ℝ)*‖w‖/4) ▸ (CircleGridMargin.grid_relu_sum_bounds N hn w).1) top.1
  have lp : 0<curvature (gridPoint N) (initial z) := by
    have ep := (show 0<(2*r)^2*3 by positivity).trans_le ee.1
    exact lt_of_lt_of_le (mul_pos (by norm_num) ep) lower
  have ub := upp.trans (mul_le_mul_of_nonneg_left ee.2 Cpos.le)
  dsimp [CircleReciprocal.rate]
  apply (le_div_iff₀ (mul_pos np (sqrt_pos.mpr mp))).2
  apply (le_div_iff₀ lp).2
  apply (mul_le_mul_of_nonneg_left ub (show 0≤c/(27*C N*(N*sqrt m))/r^2*(N*sqrt m) by positivity)).trans_eq
  field_simp

private theorem first_step (N m : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ A : ℝ in atTop, ∀ z∈box m (1/A) false,
      K*A^2 ≤ CircleReciprocal.rate N m c z/(N*sqrt m) ∧
      Cone (path N m (CircleReciprocal.rate N m c z) z 1) 1 (K*A/2) := by
  obtain ⟨K,kp,dk⟩ := large_step N m hn odd hm c hc
  let g := 1/sqrt (m:ℝ)
  have gp : 0<g := by dsimp [g]; positivity
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  let M := (N:ℝ)*(g*m)*216
  have event : ∀ᶠ A : ℝ in atTop, M≤A^2 := ((tendsto_pow_atTop (α:=ℝ) (by decide : 2≠0))).eventually_ge_atTop M
  refine ⟨K,kp,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),event] with A a1 aM
  have ap : 0<A := by linarith
  let r := 1/A
  have rp : 0<r := by dsimp [r];positivity
  intro z hz
  let net := initial z
  let η := CircleReciprocal.rate N m c z
  let k := η/(N*sqrt m)
  have kl : K*A^2≤k := (by unfold r;field_simp : K*A^2=K/r^2) ▸ dk r rp z hz
  have kn := (show 0<K*A^2 by positivity).trans_le kl
  have bs := box_net rp hz
  have eb (i : Fin N) : output g net (gridPoint N i) ≤ (g*m)*(6*r)^2 := by
    have h := output_cap g _ (by positivity) net bs (gridPoint N i) (grid_norm N i).le
    rw [abs_of_nonneg gp.le] at h
    exact (le_abs_self _).trans h
  let i₀ : Fin N := ⟨0,by omega⟩
  have origin : gridPoint N i₀=1 := by apply Complex.ext <;> simp [gridPoint,i₀]
  have label (i : Fin N) : 0≤1+(gridPoint N i).re := by
    linarith [(Complex.abs_re_le_norm (gridPoint N i)).trans_eq (grid_norm N i),neg_abs_le (gridPoint N i).re]
  refine ⟨kl,?_⟩
  intro j
  let h (i : Fin N) := feature (net.w j) (gridPoint N i)
  let y (i : Fin N) := 1+(gridPoint N i).re
  let v (i : Fin N) := output g net (gridPoint N i)
  let grad := ∑ i, (y i-v i)*h i
  have hp (i : Fin N) : 0≤h i := le_max_right _ _
  have h0 : 2*r≤h i₀ := by
    dsimp only [h];rw [origin]
    have eq : inner ℝ (net.w j) (1:ℂ) = z (j,1) := by simp [Complex.inner,net,initial]
    unfold feature;rw [eq];exact (box_coords hz (j,1)).1.trans (le_max_left ..)
  have normW : ‖net.w j‖≤6*r := (bs j).2
  have hb (i : Fin N) : h i≤6*r := (le_abs_self _).trans ((feature_cap _ _ (grid_norm N i).le).trans normW)
  have signal : 4*r≤∑ i, y i*h i := by
    apply LE.le.trans _ (single_le_sum (f:=fun i => y i*h i) (fun i _ => mul_nonneg (label i) (hp i)) (mem_univ i₀))
    change 4*r≤(1+(gridPoint N i₀).re)*h i₀
    rw [origin,Complex.one_re];linarith only [h0]
  have noise : (∑ i, v i*h i)≤r := by
    have pt (i : Fin N) : v i*h i ≤ ((g*m)*(6*r)^2)*(6*r) :=
      mul_le_mul (eb i) (hb i) (hp i) (by positivity)
    have hsum := sum_le_sum (s:=univ) (fun i _ => pt i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    apply hsum.trans
    dsimp only [r,M] at aM ⊢
    field_simp
    linarith only [aM]
  have gradient : 3*r≤grad := by
    dsimp only [grad];simp only [sub_mul,sum_sub_distrib];linarith only [signal,noise]
  have a0 : 2*r≤net.a j := (box_coords hz (j,0)).1
  have G' : (∑ i, (v i-y i)*h i) = -grad := by
    dsimp only [grad];rw [←sum_neg_distrib];apply sum_congr rfl;intro i _;ring
  have ka : K*A≤k*r := by
    apply (le_of_eq (by dsimp [r];field_simp : K*A=(K*A^2)*r)).trans (mul_le_mul_of_nonneg_right kl rp.le)
  have sα : K*A/2≤net.a j+k*grad := by
    have scale := mul_le_mul_of_nonneg_left gradient kn.le
    nlinarith only [a0,ka,scale,rp,kp,ap,mul_pos kp ap]
  let out := step (gridPoint N) y g k net
  change K*A/2≤1*out.a j ∧ K*A/2≤‖out.w j‖
  constructor
  · change _≤1*(net.a j-k*∑ i,(v i-y i)*h i)
    rw [G'];linarith only [sα]
  · have proj := hidden_projection (gridPoint N) y g k net j
    change inner ℝ (net.w j) (out.w j)=‖net.w j‖^2-(k*net.a j)*∑ i,(v i-y i)*h i at proj
    rw [G'] at proj
    have w := (real_inner_le_norm (net.w j) (out.w j)).trans (mul_le_mul_of_nonneg_right normW (norm_nonneg _))
    have ag := mul_le_mul a0 gradient (by positivity : 0≤3*r) (by linarith)
    have kg := mul_le_mul_of_nonneg_left ag kn.le
    have kgr := mul_le_mul_of_nonneg_right ka rp.le
    apply le_of_mul_le_mul_right (a:=6*r) _ (by positivity)
    nlinarith only [proj,w,kg,kgr,sq_nonneg ‖net.w j‖,mul_nonneg (mul_nonneg kp.le ap.le) rp.le]

/-- The exact small-seed exponent on each hidden length/readout after the
first update and t additional simultaneous updates. -/
def powerIndex : ℕ → ℕ
  | 0 => 1
  | t+1 => 2+3*powerIndex t

theorem powerIndex_eq (t : ℕ) : powerIndex t+1=2*3^t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [powerIndex,pow_succ];omega

private theorem power_pos (t : ℕ) : 0<powerIndex t := by cases t <;> simp [powerIndex]

/-- Every point of the positive shrinking box yields at least a constant
times A^(2·3^t−1) in every readout and hidden length after t+1 updates.
The signed readouts follow the same alternating parity on the entire box. -/
theorem cone_boxes (N m : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    (c : ℝ) (hc : 0<c) (t : ℕ) :
    ∃ d : ℝ, 0<d ∧ ∀ᶠ A : ℝ in atTop, ∀ z∈box m (1/A) false,
      Cone (path N m (CircleReciprocal.rate N m c z) z (t+1)) ((-1)^t) (d*A^(powerIndex t)) := by
  obtain ⟨K,kp,base⟩ := first_step N m hn odd hm c hc
  let g := 1/sqrt (m:ℝ)
  have gp : 0<g := by unfold g;positivity
  let L := sqrt (16/(K*g))
  have lp : 0<L := sqrt_pos.mpr (by positivity)
  have ls : K*g*L^2 = 16 := by unfold L;rw [sq_sqrt (by positivity)]; field_simp
  induction t with
  | zero =>
    refine ⟨K/2,by positivity,?_⟩
    filter_upwards [base] with A ha z hz
    simpa [powerIndex,mul_div_assoc,div_mul_eq_mul_div] using (ha z hz).2
  | succ t ih =>
    obtain ⟨d,dp,ind⟩ := ih
    refine ⟨d^3/L^2,by positivity,?_⟩
    let P := powerIndex t
    have tend : Tendsto (fun A : ℝ => d*A^P) atTop atTop := (tendsto_pow_atTop (power_pos t).ne').const_mul_atTop dp
    have floor := tend.eventually_ge_atTop (2*L)
    have noise := tend.eventually_ge_atTop (sqrt (16*N/g))
    filter_upwards [base,ind,eventually_ge_atTop (1:ℝ),floor,noise] with A first later a1 amin an z hz
    have ap : 0<A := by linarith
    let η := CircleReciprocal.rate N m c z
    let k := η/(N*sqrt m)
    have kbound : K*A^2≤k := (first z hz).1
    have kn := (show 0<K*A^2 by positivity).trans_le kbound
    have Λ : 0<L/A := div_pos lp ap
    have lb : 2*(L/A)≤d*A^P := by
      apply LE.le.trans _ amin
      exact mul_le_mul_of_nonneg_left (div_le_self lp.le a1) (by norm_num)
    have n0 : 0≤16*(N:ℝ)/g := by positivity
    have nr : 16*(N:ℝ)≤g*(d*A^P)^2 := by
      have h := pow_le_pow_left₀ (sqrt_nonneg _) an 2
      rw [sq_sqrt n0] at h
      simpa [mul_comm] using (div_le_iff₀ gp).mp h
    have kscale : 16≤k*g*(L/A)^2 := by
      calc
        _ = K*A^2*g*(L/A)^2 := by rw [←ls];field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right kbound gp.le) (sq_nonneg _)
    have ny (i : Fin N) : (-1:ℝ)^t*(1+(gridPoint N i).re) ≤2 := by
      apply (le_abs_self _).trans
      simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      exact (abs_add_le _ _).trans ((add_le_add (le_of_eq abs_one) ((Complex.abs_re_le_norm _).trans_eq (grid_norm N i))).trans_eq (by norm_num))
    let net := path N m η z (t+1)
    have next := step_cone (gridPoint N) (fun i => 1+(gridPoint N i).re) g k (L/A) ((-1)^t) (d*A^P) net
      gp kn Λ (fun i => (grid_norm N i).le) (grid_coverage N hn) ny
      (by rw [←sq_abs,abs_pow,abs_neg,abs_one,one_pow];norm_num) lb (later z hz) kscale nr
    have mag : (d*A^P)^3/(L/A)^2 = (d^3/L^2)*A^(powerIndex (t+1)) := by
      rw [powerIndex,pow_add,mul_comm 3 (powerIndex t),pow_mul]
      dsimp [P];field_simp
    rw [mag] at next
    rw [pow_succ (-1:ℝ),mul_neg_one]
    change Cone (step (gridPoint N) (fun i => 1+(gridPoint N i).re) g k net) _ _
    exact next

/-- Actual population output on shrinking boxes. -/
theorem mean_boxes (N m : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c) (t : ℕ) :
    ∃ d : ℝ, 0<d ∧ ∀ᶠ A : ℝ in atTop, ∀ z∈box m (1/A) false,
      d*A^(2*powerIndex t)≤|CircleReciprocal.Y N m (t+1) c z| := by
  obtain ⟨b,bp,ev⟩ := cone_boxes N m hn odd hm c hc t
  let d := ((1/sqrt (m:ℝ))/π)*m*b^2
  refine ⟨d,by unfold d;positivity,?_⟩
  filter_upwards [ev,eventually_ge_atTop (1:ℝ)] with A h a1 z hz
  have ap : 0<A := by linarith
  have lb := signed_mean (1/sqrt (m:ℝ)) ((-1)^t) (b*A^powerIndex t)
    _ (by positivity) (by positivity) (h z hz)
  have ub := (le_abs_self _).trans_eq (by rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] :
    |(-1:ℝ)^t*CircleReciprocal.Y N m (t+1) c z| = |CircleReciprocal.Y N m (t+1) c z|)
  exact (by unfold d;rw [mul_comm 2 (powerIndex t),pow_mul,mul_pow];ring :
    d*A^(2*powerIndex t)=((1/sqrt (m:ℝ))/π)*m*(b*A^powerIndex t)^2) ▸ lb.trans ub

open MeasureTheory ProbabilityTheory

private theorem shrinking_boxes {m : ℕ} (hm : 0<m) (F : Seed m→ℝ) (hi : Integrable F (seedLaw m)) :
    Tendsto (fun A : ℝ => ∫ z in box m (1/A) false, F z ∂seedLaw m) atTop (𝓝 0) := by
  let E := fun A : ℝ => box m (1/A) false
  have me (A : ℝ) : MeasurableSet (E A) := measurable_box m (1/A) false
  have erase (z : Seed m) : ∀ᶠ A : ℝ in atTop, z∉E A := by
    let i : Fin m × Fin 3 := (⟨0,hm⟩,0)
    by_cases pos : 0<z i
    · filter_upwards [eventually_ge_atTop (4/z i),eventually_gt_atTop (0:ℝ)] with A ha ap hz
      have hi := (box_coords hz i).2
      have large := (div_le_iff₀ pos).mp ha
      change z i≤3*(1/A) at hi
      have small : z i*A≤3 := (le_div_iff₀ ap).mp (hi.trans_eq (by ring))
      linarith only [large,small]
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with A ap hz
      exact pos ((show 0<2*(1/A) by positivity).trans_le (box_coords hz i).1)
  let FF := fun A => (E A).indicator F
  have hm' (A : ℝ) : AEStronglyMeasurable (FF A) (seedLaw m) := hi.aestronglyMeasurable.indicator (me A)
  have hb (A : ℝ) (z : Seed m) : ‖FF A z‖≤‖F z‖ := by
    by_cases h : z∈E A <;> simp [FF,h]
  have conv (z : Seed m) : Tendsto (fun A => FF A z) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((erase z).mono fun A h => (Set.indicator_of_notMem h F).symm)
  have lim := tendsto_integral_filter_of_dominated_convergence (F:=FF) (f:=fun _ => (0:ℝ)) (fun z => ‖F z‖)
    (Eventually.of_forall hm') (Eventually.of_forall fun A => ae_of_all _ (hb A)) hi.norm (ae_of_all _ conv)
  simpa only [FF,integral_indicator (me _),integral_zero] using lim

private theorem small_mass {m : ℕ} {A : ℝ} (hA : 1≤A) :
    (gaussianPDFReal 0 1 3/A)^(3*m) ≤ (seedLaw m).real (box m (1/A) false) := by
  have ap : 0<A := by linarith
  have range : 3*(1/A)≤3 := by rw [←div_eq_mul_one_div];exact div_le_self (by norm_num) hA
  have pdf : gaussianPDFReal 0 1 3 ≤ gaussianPDFReal 0 1 (3*(1/A)) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    linarith only [pow_le_pow_left₀ (show 0≤3*(1/A) by positivity) range 2]
  have h := (signed_gaussian_mass m (1/A) (by positivity) false)
  exact (pow_le_pow_left₀ (div_nonneg (gaussianPDFReal_nonneg ..) ap.le)
    (by simpa only [div_eq_inv_mul,one_div,mul_one] using mul_le_mul_of_nonneg_left pdf (by positivity : 0≤A⁻¹)) (3*m)).trans h

/-- The actual reciprocal learner has no p-th absolute moment whenever its
box amplification exponent times p reaches the full Gaussian dimension.
This statement includes the boundary exponent itself. -/
theorem no_moment (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c p : ℝ) (hc : 0<c) (hp : 0<p)
    (high : ((3*m:ℕ):ℝ) ≤ ((2*powerIndex t:ℕ):ℝ)*p) :
    ¬Integrable (fun z => |CircleReciprocal.Y N m (t+1) c z|^p) (seedLaw m) := by
  obtain ⟨d,dp,ev⟩ := mean_boxes N m hn odd hm c hc t
  let e := 2*powerIndex t
  let D := 3*m
  let a := gaussianPDFReal 0 1 3
  have a0 : 0<a := gaussianPDFReal_pos 0 1 3 (by norm_num)
  let f := fun z => |CircleReciprocal.Y N m (t+1) c z|^p
  let floor := a^D*d^p
  have fp : 0<floor := mul_pos (pow_pos a0 _) (rpow_pos_of_pos dp p)
  intro hf
  have lim := shrinking_boxes hm f hf
  have cost : ∀ᶠ A : ℝ in atTop, floor≤∫ z in box m (1/A) false, f z ∂seedLaw m := by
    filter_upwards [ev,eventually_ge_atTop (1:ℝ)] with A hh hA
    have ap := zero_lt_one.trans_le hA
    have hpow : A^D≤(A^e)^p := by
      rw [←rpow_natCast A D,←rpow_natCast A e,←rpow_mul ap.le]
      exact rpow_le_rpow_of_exponent_le hA high
    have pay : floor ≤ (a/A)^D*(d*A^e)^p := by
      rw [div_pow,mul_rpow dp.le (pow_nonneg ap.le e)]
      have b := mul_le_mul_of_nonneg_left hpow (show 0≤(a^D/(A^D))*d^p by positivity)
      calc
        _ = ((a^D/A^D)*d^p)*A^D := by unfold floor;field_simp
        _ ≤ _ := b.trans_eq (by ring)
    let B := box m (1/A) false
    have cb := (small_mass (m:=m) hA)
    have cost' := mul_le_mul_of_nonneg_right cb (show 0≤(d*A^e)^p by positivity)
    have mono := setIntegral_mono_on (integrable_const ((d*A^e)^p)).integrableOn hf.integrableOn
      (measurable_box m (1/A) false) (fun z hz => rpow_le_rpow (show 0≤d*A^e by positivity) (hh z hz) hp.le)
    exact (pay.trans cost').trans ((by rw [setIntegral_const,smul_eq_mul] :
      (seedLaw m).real B*(d*A^e)^p = ∫ _ : Seed m in B, (d*A^e)^p ∂seedLaw m) ▸ mono)
  exact (not_le_of_gt fp) (le_of_tendsto_of_tendsto tendsto_const_nhds lim cost)

/-- Subtracting the same-seed reference preserves the singularity at every
positive real order, including orders below one. -/
theorem no_paired_moment (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    (c p : ℝ) (hc : 0<c) (hp : 0<p) (high : (3*m:ℕ)≤(2*powerIndex t:ℕ)*p) (b : ℝ) :
    ¬Integrable (fun z => |CircleReciprocal.Y N m (t+1) c z-reference N m b z|^p) (seedLaw m) := by
  let F := CircleReciprocal.Y N m (t+1) c
  let Z := reference N m b
  let q := ENNReal.ofReal p
  have hq : q ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have qt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have rq : q.toReal = p := ENNReal.toReal_ofReal hp.le
  have mf : Measurable F := CircleReciprocal.Y_measurable N m (t+1) c hn odd hm
  have mz : Measurable Z := reference_measurable N m b
  intro good
  have r : MemLp (F-Z) q (seedLaw m) := (integrable_norm_rpow_iff (mf.sub mz).aestronglyMeasurable hq qt).mp (by
    simpa [rq,Real.norm_eq_abs,F,Z] using good)
  have zmem : MemLp Z q (seedLaw m) := reference_memLp N m b q qt
  have f : MemLp F q (seedLaw m) := by simpa only [sub_add_cancel] using r.add zmem
  apply no_moment N m t hn odd hm c p hc hp high
  simpa [rq,Real.norm_eq_abs,F] using f.integrable_norm_rpow hq qt

/-- Unconditional divergence against the same-seed reference and every fixed
real target, under the actual Gaussian measure. -/
theorem no_second_moment (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c)
    (high : 3*m≤4*powerIndex t) (b h : ℝ) :
    ¬MemLp (fun z => CircleReciprocal.Y N m (t+1) c z-reference N m b z) 2 (seedLaw m) ∧
      ¬MemLp (fun z => CircleReciprocal.Y N m (t+1) c z-h) 2 (seedLaw m) := by
  have neg := no_moment N m t hn odd hm c 2 hc (by norm_num) (by exact_mod_cast (by omega : 3*m ≤ 2*powerIndex t*2))
  have fail : ¬MemLp (CircleReciprocal.Y N m (t+1) c) 2 (seedLaw m) := by
    intro yes
    apply neg
    simpa [sq_abs] using yes.integrable_sq
  constructor
  · intro H
    exact fail (by simpa only [Pi.add_def,sub_add_cancel] using H.add (reference_memLp N m b 2 (by norm_num)))
  · intro H
    exact fail (by simpa only [Pi.add_def,sub_add_cancel] using H.add (memLp_const (μ:=seedLaw m) (p:=2) h))

private theorem infinite_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω→ℝ)
    (M : Measurable F) (fail : ¬MemLp F 2 μ) :
    (∫⁻ z, ENNReal.ofReal (F z^2) ∂μ)=⊤ := by
  by_contra h
  apply fail
  apply (memLp_two_iff_integrable_sq M.aestronglyMeasurable).2
  exact ⟨(M.pow_const 2).aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg (F z))).2 (lt_top_iff_ne_top.mpr h)⟩

/-- Infinite (extended nonnegative) MSE against both kinds of targets. -/
theorem infinite_mse (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c)
    (high : 3*m≤4*powerIndex t) (b h : ℝ) :
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N m (t+1) c z-reference N m b z)^2) ∂seedLaw m)=⊤ ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N m (t+1) c z-h)^2) ∂seedLaw m)=⊤ := by
  obtain ⟨r,s⟩ := no_second_moment N m t hn odd hm c hc high b h
  have M := CircleReciprocal.Y_measurable N m (t+1) c hn odd hm
  exact ⟨infinite_sq _ _ (M.sub (CircleCapMoments.reference_measurable N m b)) r,
    infinite_sq _ _ (M.sub measurable_const) s⟩

private theorem schedule (T : ℕ→ℕ) (time : ∀ᶠ N : ℕ in atTop, 60*log N≤(T N:ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ t : ℕ, T N=t+1 ∧ 3*N^32≤2*powerIndex t := by
  have lim := CircleEulerLimits.cost_ratio_of_log_schedule T 60 (by linarith [Real.log_three_gt_d9]) time
  filter_upwards [eventually_ge_atTop 3,lim.eventually_le_const (show (0:ℝ)<1 by norm_num)] with N hN h
  have q : N^64≤3^(T N) := by
    have p : (0:ℝ)<3^(T N) := by positivity
    have b := (div_le_iff₀ p).mp h
    simp only [one_mul] at b
    exact_mod_cast b
  have n32 : 3≤N^32 := hN.trans (Nat.le_self_pow (by decide : 32≠0) N)
  have count : 3*N^32≤3^(T N) := (Nat.mul_le_mul_right (N^32) n32).trans
    ((by rw [←pow_add] : N^32*N^32=N^64).le.trans q)
  cases ht : T N with
  | zero => simp [ht] at count;omega
  | succ t =>
    refine ⟨t,rfl,?_⟩
    rw [ht,pow_succ (3:ℕ) t] at count
    have d := powerIndex_eq t
    have nt := power_pos t
    omega

/-- At the growing schedule, the first absolute moment and the two actual
second moments are infinite at every sufficiently large odd grid size. -/
theorem schedule_infinite (T : ℕ→ℕ) (time : ∀ᶠ N : ℕ in atTop, 60*log N≤(T N:ℝ)) :
    ∀ᶠ N : ℕ in atTop, Odd N → ∀ c>0, ∀ b h : ℝ,
      ¬Integrable (fun z => |CircleReciprocal.Y N (N^32) (T N) c z|) (seedLaw (N^32)) ∧
      (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) (T N) c z-reference N (N^32) b z)^2) ∂seedLaw (N^32))=⊤ ∧
      (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) (T N) c z-h)^2) ∂seedLaw (N^32))=⊤ := by
  filter_upwards [eventually_ge_atTop 3,schedule T time] with N hn htime odd c hc b h
  obtain ⟨t,et,hi⟩ := htime
  have hm : 0<N^32 := pow_pos (by omega) _
  rw [et]
  refine ⟨?_,infinite_mse N (N^32) t hn odd hm c hc (by omega) b h⟩
  simpa using no_moment N (N^32) t hn odd hm c 1 hc (by norm_num) (by simpa only [mul_one] using (Nat.cast_le (α:=ℝ)).mpr hi)

theorem medium_infinite : ∀ᶠ N : ℕ in atTop, Odd N → ∀ c>0, ∀ b h : ℝ,
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) ⌈60*log N⌉₊ c z-reference N (N^32) b z)^2) ∂seedLaw (N^32))=⊤ ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) ⌈60*log N⌉₊ c z-h)^2) ∂seedLaw (N^32))=⊤ := by
  exact (schedule_infinite (fun N => ⌈60*log N⌉₊) (.of_forall fun _ => Nat.le_ceil _)).mono
    (fun _ H o c hc b h => (H o c hc b h).2)

theorem horizon_infinite : ∀ᶠ N : ℕ in atTop, Odd N → ∀ c>0, ∀ b h : ℝ,
    ¬Integrable (fun z => |CircleReciprocal.Y N (N^32) (CircleFlowTracking.horizon N) c z|) (seedLaw (N^32)) ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) (CircleFlowTracking.horizon N) c z-reference N (N^32) b z)^2) ∂seedLaw (N^32))=⊤ ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N (N^32) (CircleFlowTracking.horizon N) c z-h)^2) ∂seedLaw (N^32))=⊤ := by
  apply schedule_infinite (fun N : ℕ => CircleFlowTracking.horizon N)
  filter_upwards [eventually_ge_atTop 3] with N hn
  have n3 : (3:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have n1 : (1:ℝ)≤N := by linarith
  have p3 : (N:ℝ)≤(N:ℝ)^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤3)
  have r := Real.one_le_sqrt.mpr (by linarith : (1:ℝ)≤12*N)
  have big := p3.trans (le_mul_of_one_le_left (by positivity : 0≤(N:ℝ)^3)
    (by linarith : 1≤2*Real.sqrt (12*N)))
  have factor : (60:ℝ) ≤ 2*Real.pi^2*(N:ℝ)^2 := by
    calc _ ≤ 2*(3:ℝ)^2*(3:ℝ)^2 := by norm_num
         _ ≤ _ := by gcongr; exact Real.pi_gt_three.le
  apply (mul_le_mul factor (Real.log_le_log np big) (Real.log_nonneg n1) (by positivity)).trans
  exact Nat.le_ceil (2*π^2*(N:ℝ)^2 * log (2*sqrt (12*N)*(N:ℝ)^3))

end CircleReciprocalEscape
