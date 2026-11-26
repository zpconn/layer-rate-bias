module

public import CircleFlowBlockMovement
public import CircleVariableFlow
import all CircleVariableFlow
import all CircleSharpTracking
import all CircleTangentDrift
import all CircleFlowPath
import all CircleActualTracking
import all CircleMeanDynamics
import all CircleGridSpectrum
import all CircleKernelGD
import all CircleSpectralPathLength
import all CircleGaussianTracking
import Mathlib.Tactic

/-! The deterministic equal-rate continuous-time certificate, with its
original uniform radius and one copy of the Gram/row perturbation. -/
@[expose] public section
noncomputable section
namespace CircleUniformRadius
open Real MeasureTheory Set Filter CircleFlowPath CircleFlowMoments CircleTangentDrift CircleActualTracking
  CircleGridSpectrum CircleSpectrum CircleEscapeBridge CircleFlowTracking
variable {N m : ℕ}

private theorem local_budget {ρ u E x y d d₀ p : ℝ} (hp : 0≤ρ) (hs : ρ≤1) (en : E≤4)
    (hx : x≤3*ρ+u) (hy : y≤3*ρ+u) (motion : |d-d₀|≤1*((4*ρ+2*ρ^2)*E+x+y))
    (init : |d₀-p|≤u) : |d-p|≤30*ρ+3*u := by
  apply (abs_sub_le d d₀ p).trans
  nlinarith only [motion,init,mul_le_mul_of_nonneg_left en (by positivity : 0≤4*ρ+2*ρ^2),
    hx,hy,mul_nonneg hp (sub_nonneg.mpr hs)]

private theorem operators {ρ u : ℝ} {x₀ x : State m} {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N→ℝ}
    (hn : 0<N) (hm : 0<m) (hp : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (G : GoodInit 1 ρ u K kQ x₀)
    (initK : ∀ i j, |gridGram 1 x₀ (startGates x₀) i j-K i j|≤u)
    (initQ : ∀ j, |populationRow 1 x₀ (startGates x₀) j-kQ j|≤u)
    (tube : Tube ρ x₀ x) (g : Fin N→Fin m→ℝ) (ad : gridGates x g) :
    ‖gramOp (gridGram 1 x g)-gramOp K‖≤30*ρ+3*u ∧
    ‖rowOp (populationRow 1 x g)-rowOp kQ‖≤30*ρ+3*u := by
  rw [←gramOp_sub,←rowOp_sub]
  constructor
  · apply gramOp_norm hn (by positivity)
    intro i j
    exact local_budget hp hr G.energy (G.gridMargin i) (G.gridMargin j)
      (entry_drift hm (by norm_num) (by norm_num) hp (grid_unit i) (grid_unit j) tube tube (ad i) (ad j)
        (startGates_admissible x₀ i) (startGates_admissible x₀ j)) (initK i j)
  · apply rowOp_norm hn (by positivity)
    intro j
    exact local_budget hp hr G.energy G.angular (G.gridMargin j)
      (angular_entry_drift hm (by norm_num) (by norm_num) hp (grid_unit j) tube tube (ad j)
        (startGates_admissible x₀ j)) (initQ j)

private theorem prefix_bounds {T ρ k e R : ℝ} {z : ℝ→State m} {K : Matrix (Fin N) (Fin N) ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T z) (hk : 0<k)
    (spec : ∀ v, (k+e)*‖v‖^2≤ inner ℝ v (gramOp K v))
    (close : ∀ s, Tube ρ (z 0) (z s) → ∀ g, gridGates (z s) g → ‖gramOp K-gramOp (gridGram 1 (z s) g)‖≤e)
    (init : ‖gridR N (z 0)‖≤R) {t : ℝ} (ht : t∈Icc 0 T)
    (prev : ∀ s∈Ico 0 t, Tube ρ (z 0) (z s)) :
    ‖gridR N (z t)‖≤R*exp (-(k*t)) ∧ (∫ s in (0:ℝ)..t, ‖gridR N (z s)‖)≤R/k := by
  let r (s : ℝ) := gridR N (z s)
  have T0 := ht.1.trans ht.2
  have sub : uIcc 0 t ⊆ uIcc 0 T := by rw [uIcc_of_le ht.1,uIcc_of_le T0];exact Icc_subset_Icc_right ht.2
  have ac := (energy_ac F).mono sub
  have regular : ∀ᵐ s : ℝ, s∈Icc 0 t → ∃ v, HasDerivAt r v s ∧ inner ℝ (r s) v ≤ -k*‖r s‖^2 := by
    filter_upwards [ae_grid_hilbert_ode F,volume.ae_ne t] with s h ne hs
    obtain ⟨g,ad,der⟩ := h (by rw [uIcc_of_le T0];exact ⟨hs.1,hs.2.trans ht.2⟩)
    refine ⟨_,der,?_⟩
    have ray := shifted_rayleigh _ _ spec (close s (prev s ⟨hs.1,lt_of_le_of_ne hs.2 ne⟩) g ad) (r s)
    rw [inner_neg_right]
    change -inner ℝ (r s) (gramOp (gridGram 1 (z s) g) (r s)) ≤ -k*‖r s‖^2
    linarith only [ray]
  have decay := damped_comparison (k:=2*k) (M:=0) ht.1 ac (by
    filter_upwards [regular] with s hh hs
    obtain ⟨v,der,p⟩ := hh hs
    rw [show deriv (fun t => ‖gridR N (z t)‖^2) s=2*inner ℝ (r s) v from der.norm_sq.deriv]
    change 2*inner ℝ (r s) v+2*k*‖r s‖^2≤_
    linarith only [p])
  have ex : exp (-(2*k*t))=exp (-(k*t))^2 := by rw [sq,←exp_add];congr 1;ring
  simp only [ex,sub_zero,add_zero] at decay
  have dec := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (exp_nonneg _) (norm_nonneg _))).mp (by rwa [mul_pow])
  have ar := (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (CircleSharpTracking.actual_grid_ac F)).mono sub
  have area := CircleSharpTracking.integrated_response r (fun _ => 0) (k:=k) ht.1 ar intervalIntegrable_const (by
    filter_upwards [regular] with s h hs
    obtain ⟨v,d,sp⟩ := h hs
    exact ⟨le_rfl,v,d,by simpa only [mul_zero,add_zero] using sp⟩)
  simp only [intervalIntegral.integral_zero,add_zero] at area
  refine ⟨dec.trans ((mul_le_mul_of_nonneg_left init (exp_nonneg _)).trans_eq (mul_comm _ _)),(le_div_iff₀ hk).mpr ?_⟩
  change ‖r 0‖≤R at init
  linarith only [area,init,norm_nonneg (r t)]

private theorem confined {T ρ k e R : ℝ} {z : ℝ→State m} {K : Matrix (Fin N) (Fin N) ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T z)
    (hT : 0≤T) (hp : 0<ρ) (hr : ρ<1) (hk : 0<k)
    (spec : ∀ v, (k+e)*‖v‖^2≤ inner ℝ v (gramOp K v))
    (close : ∀ s, Tube ρ (z 0) (z s) → ∀ g, gridGates (z s) g → ‖gramOp K-gramOp (gridGram 1 (z s) g)‖≤e)
    (init : ‖gridR N (z 0)‖≤R) (budget : (R/k)/sqrt m≤ρ/2)
    (movement : ∀ t∈Icc 0 T, ∀ j, length (z t-z 0) j≤∫ s in (0:ℝ)..t, (‖gridR N (z s)‖/sqrt m)*length (z s) j)
    (zero : ∀ t∈Icc 0 T, ∀ j, length (z 0) j=0 → length (z t-z 0) j=0) :
    ∀ t∈Icc 0 T, Tube ρ (z 0) (z t) ∧ ‖gridR N (z t)‖≤R*exp (-(k*t)) ∧
        (∫ s in (0:ℝ)..t, ‖gridR N (z s)‖)≤R/k := by
  let L (j : Fin m) := length (z 0) j
  let d (j : Fin m) (s : ℝ) := length (z s-z 0) j
  let S (j : Fin m) := if L j=0 then ∅ else Icc 0 T ∩ {s | ρ*L j≤d j s}
  have cont (j : Fin m) : ContinuousOn (d j) (Icc 0 T) := by
    have cz (p : Coord m) : ContinuousOn (fun t => z t p) (Icc 0 T) := by simpa only [uIcc_of_le hT] using (F.ac p).continuousOn
    dsimp only [d,length,Pi.sub_apply]
    fun_prop (disch := assumption)
  have compact (j : Fin m) : IsCompact (S j) := by
    dsimp only [S]
    split
    · exact isCompact_empty
    · exact isCompact_Icc.of_isClosed_subset ((cont j).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  have empty : ¬(⋃j,S j).Nonempty := by
    intro nonempty
    obtain ⟨t,ht,first⟩ := (isCompact_iUnion compact).exists_isMinOn nonempty continuous_id.continuousOn
    obtain ⟨j,hj⟩ := mem_iUnion.mp ht
    by_cases lz : L j=0
    · simp [S,lz] at hj
    have lj := lt_of_le_of_ne (show 0≤L j from sqrt_nonneg _) (Ne.symm lz)
    obtain ⟨time,hit⟩ : t∈Icc 0 T ∧ ρ*L j≤d j t := by simpa [S,lz] using hj
    have pr (s : ℝ) (hs : s∈Ico 0 t) : Tube ρ (z 0) (z s) := by
      intro l
      have window : s∈Icc 0 T := ⟨hs.1,hs.2.le.trans time.2⟩
      by_cases zl : L l=0
      · rw [zero _ window l zl];change 0≤ρ*L l;rw [zl,mul_zero]
      · by_contra! bad
        exact hs.2.not_ge (isMinOn_iff.mp first s (mem_iUnion.mpr ⟨l,by simpa [S,zl] using And.intro window bad.le⟩))
    have area := (prefix_bounds F hk spec close init time pr).2
    have subset : uIcc 0 t ⊆ uIcc 0 T := by rw [uIcc_of_le time.1,uIcc_of_le hT];exact Icc_subset_Icc_right time.2
    have cr := ((CircleSharpTracking.actual_grid_ac F).mono subset).continuousOn.norm
    have coords (p : Coord m) := ((F.ac p).mono subset).continuousOn
    have cl : ContinuousOn (fun s => length (z s) j) (uIcc 0 t) := by unfold length;fun_prop (disch := assumption)
    let C := ((1+ρ)*L j)/sqrt m
    have cp : 0≤C := by dsimp [C];positivity
    have mono := intervalIntegral.integral_mono_ae_restrict time.1 ((cr.div_const _).mul cl).intervalIntegrable
      (cr.intervalIntegrable.const_mul C) ((ae_restrict_iff' measurableSet_Icc).mpr (by
        filter_upwards [volume.ae_ne t] with s ne hs
        have len := current_length (pr s ⟨hs.1,lt_of_le_of_ne hs.2 ne⟩) j
        exact (mul_le_mul_of_nonneg_left len (show 0≤‖gridR N (z s)‖/sqrt m by positivity)).trans_eq (by dsimp only [C,L];ring)))
    rw [intervalIntegral.integral_const_mul] at mono
    have paid := (movement t time j).trans (mono.trans (mul_le_mul_of_nonneg_left area cp))
    have strict : C*(R/k)<ρ*L j := by
      have p := mul_le_mul_of_nonneg_right budget (mul_nonneg (by linarith only [hp] : 0≤1+ρ) lj.le)
      have n := mul_pos (mul_pos hp lj) (sub_pos.mpr hr)
      calc
        _ = (R/k)/sqrt m*((1+ρ)*L j) := by dsimp only [C];ring
        _ ≤ _ := p
        _ < _ := by nlinarith only [n]
    exact (paid.trans_lt strict).not_ge hit
  intro t ht
  have path (s : ℝ) (hs : s∈Icc 0 T) : Tube ρ (z 0) (z s) := by
    intro j
    by_cases hz : L j=0
    · rw [zero _ hs j hz];change 0≤ρ*L j;rw [hz,mul_zero]
    · by_contra! bad
      exact empty ⟨s,mem_iUnion.mpr ⟨j,by simpa [S,hz] using And.intro hs bad.le⟩⟩
  exact ⟨path t ht,prefix_bounds F hk spec close init ht (fun s hs => path s ⟨hs.1,hs.2.le.trans ht.2⟩)⟩



/-- Uniform relative confinement, including every zero-length neuron, plus
the decaying RMS and accumulated residual for every physical prefix. -/
theorem confinement {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) {T R ρ u : ℝ}
    (ht : 0≤T) (hp : 0<ρ) (hr : ρ≤1) (hu : 0≤u)
    (small : 30*ρ+3*u≤(1/(π*(n+1:ℕ))^2)/2)
    (radius : 4*R/((1/(π*(n+1:ℕ))^2)*sqrt m)≤ρ)
    (z : ℝ→State m) (F : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T z)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) (z 0))
    (initK : ∀ i j : Fin (n+1), |gridGram 1 (z 0) (startGates (z 0)) i j-sampledMatrix 1 i j|≤u)
    (initQ : ∀ j : Fin (n+1), |populationRow 1 (z 0) (startGates (z 0)) j-k0 1|≤u)
    (init : ‖gridR (n+1) (z 0)‖≤R) :
    let N := n+1
    let lam := 1/(π*(N:ℝ))^2
    ∀ t∈Icc 0 T, Tube ρ (z 0) (z t) ∧ ‖gridR N (z t)‖≤R*exp (-((lam/2)*t)) ∧
      (∫ s in (0:ℝ)..t, ‖gridR N (z s)‖)≤R/(lam/2) := by
  intro N lam
  let e := 30*ρ+3*u
  have gram := gramOp_gap hn ho 1 (by norm_num) (by norm_num)
  have lp : 0<lam := by dsimp [lam,N];positivity
  have l1 : lam≤1 := CircleKernelGD.gap_le_one hn
  have spec (v : EuclideanSpace ℝ (Fin N)) : (lam/2+e)*‖v‖^2 ≤ inner ℝ v (gramOp (sampledMatrix 1) v) :=
    (mul_le_mul_of_nonneg_right (by change lam/2+e≤lam;change e≤lam/2 at small;linarith only [small]) (sq_nonneg _)).trans (gram v)
  have ts : ρ<1 := by change 30*ρ+3*u≤lam/2 at small; linarith only [small,hu,l1]
  have cash : R/(lam/2)/sqrt m≤ρ/2 := by
    have w : R/(lam/2)/sqrt m=(4*R/(lam*sqrt m))/2 := by ring
    rw [w];exact div_le_div_of_nonneg_right radius (by norm_num)
  exact confined F ht hp ts (by positivity) spec
    (fun s tube g ad => (norm_sub_rev _ _).le.trans (operators (by omega) hm hp.le hr hu G initK initQ tube g ad).1)
    init cash (fun _ h j => CircleFlowBlockMovement.movement_prefix (by omega) F h j)
    (fun _ h j h₀ => CircleFlowBlockMovement.zero_fixed_prefix (by omega) F h j h₀)

set_option maxHeartbeats 800000 in
/-- The exact printed deterministic comparison against the same-seed
constant-mode-stopped reference. The time and width are arbitrary. -/
theorem good_path {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) {T R ρ u : ℝ}
    (ht : 0≤T) (hp : 0<ρ) (hr : ρ≤1) (hu : 0≤u)
    (small : 30*ρ+3*u≤(1/(π*(n+1:ℕ))^2)/2)
    (radius : 4*R/((1/(π*(n+1:ℕ))^2)*sqrt m)≤ρ)
    (z : ℝ→State m) (F : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T z)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) (z 0))
    (initK : ∀ i j : Fin (n+1), |gridGram 1 (z 0) (startGates (z 0)) i j-sampledMatrix 1 i j|≤u)
    (initQ : ∀ j : Fin (n+1), |populationRow 1 (z 0) (startGates (z 0)) j-k0 1|≤u)
    (init : ‖gridR (n+1) (z 0)‖≤R) :
    let N := n+1
    let b := weight 1 n
    |mean (z T)-reference N m (b*(1-exp (-(CircleKernelGD.gamma N*T)))) (z 0)|≤
      (30*ρ+3*u)*R*(b/CircleKernelGD.gamma N + 2*(1+b)/(1/(π*(N:ℝ))^2)) := by
  intro N b
  let r (s : ℝ) := gridR N (z s)
  let Y (s : ℝ) := mean (z s)
  let p := rowOp (fun _ : Fin N => b)
  let K := gramOp (sampledMatrix (N:=N) 1)
  let lam := 1/(π*(N:ℝ))^2
  let γ := CircleKernelGD.gamma N
  let e := 30*ρ+3*u
  have lp : 0<lam := by dsimp [lam,N];positivity
  have gp : 0<γ := (show 0<(3:ℝ)/π^2 by positivity).trans_le (CircleKernelGD.gamma_bounds (N:=N)).1
  have bp := (CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)).1
  change 0≤b at bp
  have pc : ‖p‖≤b := rowOp_norm (by omega : 0<N) bp (fun _ => (abs_of_nonneg bp).le)
  have er : 0≤e := by dsimp only [e];positivity
  have rp := (norm_nonneg _).trans init
  have conf := confinement hn ho hm ht hp hr hu small radius z F G initK initQ init
  let ok (s : ℝ) (g : Fin N→Fin m→ℝ) := gridGates (z s) g ∧
    HasDerivAt r (-(gramOp (gridGram 1 (z s) g) (r s))) s ∧
    HasDerivAt Y (-(rowOp (populationRow 1 (z s) g) (r s))) s
  classical
  let gate (s : ℝ) := if h : ∃ g,ok s g then Classical.choose h else startGates (z s)
  let J (s : ℝ) := gramOp (gridGram 1 (z s) (gate s))
  let q (s : ℝ) := rowOp (populationRow 1 (z s) (gate s))
  have ode : ∀ᵐ s : ℝ, s∈Icc 0 T →
      HasDerivAt r (-J s (r s)) s ∧ HasDerivAt Y (-q s (r s)) s ∧
      ‖K-J s‖≤e ∧ ‖q s-p.comp K‖≤e := by
    filter_upwards [CircleMeanDynamics.ae_joint_ode hm F] with s hs loc
    have valid : ∃g,ok s g := hs (by rw [uIcc_of_le ht];exact loc)
    have chosen : ok s (gate s) := by dsimp only [gate];rw [dite_eq_left valid];exact Classical.choose_spec valid
    have near := operators (by omega) hm hp.le hr hu G initK initQ (conf s loc).1 _ chosen.1
    rw [population_row_factorization n hn ho 1 (by norm_num) (by norm_num)] at near
    exact ⟨chosen.2.1,chosen.2.2,(norm_sub_rev _ _).le.trans near.1,near.2⟩
  have pop (v : EuclideanSpace ℝ (Fin N)) : (2*(lam/2))*‖v‖^2 ≤ inner ℝ v (K v) := by
    rw [show 2*(lam/2)=lam by ring]
    exact gramOp_gap hn ho 1 (by norm_num) (by norm_num) v
  have a := row_ac F (fun _ : Fin N => b)
  have out := nonlinear_tracking (r:=r) (Y:=Y) (A:=J) (g:=q) (k:=lam/2) (γ:=γ) (e:=e) (R:=R) p K ht (half_pos lp) gp er rp init
    (gramOp_eigenrow 1 b (by norm_num) (by norm_num)) pop small (energy_ac F) a
    ((CircleMeanDynamics.mean_ac F).fun_sub a) ode
  rw [show b*(1-exp (-(CircleKernelGD.gamma N*T)))=CircleVariableFlow.stopped n T from rfl,CircleVariableFlow.stopped_ref n m hn,←actual_reference hn]
  change |Y T-(Y 0-p (r 0)+exp (-(γ*T))*p (r 0))|≤_
  have first := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show 1+‖p‖≤1+b by linarith only [pc]) er) rp
  have second := mul_le_mul_of_nonneg_right pc (mul_nonneg er rp)
  apply out.trans
  calc
    _ ≤ (1+b)*e*R/(lam/2)+b*(e*R)/γ := add_le_add (div_le_div_of_nonneg_right first (half_pos lp).le)
      (div_le_div_of_nonneg_right second gp.le)
    _ = e*R*(b/γ+2*(1+b)/lam) := by ring

end CircleUniformRadius
