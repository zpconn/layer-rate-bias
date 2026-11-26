module

public import CircleFiniteDynamics
public import CircleFiniteConfidence
import all CircleFiniteDynamics
import all CircleRateTrajectory
import all CircleKernelGD
import all CircleGaussianTracking
import all CircleFiniteConfidence
import all CircleActualTracking
import Mathlib.Tactic

/-! The finite-width, finite-confidence positive theorem for the odd-grid
circle regression problem. The width is a free integer and both layers use
the fixed physical learning rate η. -/
@[expose] public section
noncomputable section
namespace CircleFiniteWidth
open Real MeasureTheory Filter Topology CircleEscapeBridge CircleActualTracking CircleFlowPath
  CircleWidthTracking CircleRateTrajectory CircleFiniteConfidence CircleSpectrum

def gap (N : ℕ) : ℝ := 1/(π*(N:ℝ))^2

def R (δ : ℝ) := sqrt (12/δ)

def D (N : ℕ) (δ : ℝ) := 2*R δ/gap N

def A (N : ℕ) (δ : ℝ) := 2*D N δ

def tol (N : ℕ) (ε : ℝ) := min (1/(N:ℝ)^3) (ε/(2*(N:ℝ)^2))

def cap (N : ℕ) (η δ ε : ℝ) := ⌈2/(η*gap N)*log (R δ/tol N ε)⌉₊

/-- The five lower bounds in (1) apply to √m. The fifth uses the
concentration of the *signed* population-minus-grid row. -/
def width (n : ℕ) (δ ε : ℝ) : ℝ :=
  let N := n+1
  let b := weight 1 n
  max (A N δ) (max (sqrt (36/δ)) (max (10*((N:ℝ)+1)/(δ*A N δ))
    (max (2*(gridScale N δ+36*A N δ)/gap N)
      ((2*(N:ℝ)^2*D N δ/ε)*(signedScale N b δ+(1+b)*36*A N δ)))))

private theorem time_bound {N : ℕ} {η δ ε : ℝ} (hn : 0<N) (he : 0<ε) (hδ : 0<δ)
    (hη : 0<η) (hc : η≤1) (small : gap N/2≤1) :
    (1-η*(gap N/2))^(cap N η δ ε)*R δ≤tol N ε := by
  let k := gap N/2
  let T := cap N η δ ε
  have ng : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have gp : 0<gap N := by unfold gap;positivity
  have kp : 0<k := by dsimp [k];positivity
  have s : 0<tol N ε := lt_min (by positivity) (by positivity)
  have r : 0<R δ := by unfold R;positivity
  have ceil : 2/(η*gap N)*log (R δ/tol N ε)≤(T:ℝ) := Nat.le_ceil _
  have clk : log (R δ/tol N ε)≤η*k*(T:ℝ) := by
    have h := mul_le_mul_of_nonneg_left ceil (mul_pos hη kp).le
    calc
      log (R δ/tol N ε) = η*k*(2/(η*gap N)*log (R δ/tol N ε)) := by dsimp [k];field_simp
      _ ≤ _ := h
  have exp_est := exp_le_exp.mpr (neg_le_neg clk)
  rw [exp_neg (log _),exp_log (div_pos r s)] at exp_est
  exact (mul_le_mul_of_nonneg_right (CircleKernelGD.disc_exp ((mul_le_of_le_one_left kp.le hc).trans small) T) r.le).trans
    ((mul_le_mul_of_nonneg_right exp_est r.le).trans_eq (by field_simp))

/-- For every width satisfying (1), one measurable set controls the
training RMS and the paired population error at the stated cap. On the
same set the residual decays geometrically at every iterate and the
original parameter sequence converges to an interpolating network. -/
theorem finite_width (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1))
    {η δ ε : ℝ} (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hδ1 : δ<1) (hε : 0<ε)
    (hw : width n δ ε≤sqrt m) :
    let N := n+1
    let T := cap N η δ ε
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E,
      rms η N z T≤1/(N:ℝ)^3 ∧
      |learnerMean η N z T-reference N m (weight 1 n) z|≤ε/(N:ℝ)^2 ∧
      (∀ t, rms η N z t≤(1-η*(gap N/2))^t*R δ ∧ budget η N z t≤D N δ) ∧
      ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  intro N T
  let b := weight 1 n
  let k := gap N/2
  let L := sqrt (m:ℝ)
  let ρ := A N δ/L
  have nn : 0<N := Nat.succ_pos _
  have np : (0:ℝ)<N := Nat.cast_pos.mpr nn
  have gp : 0<gap N := by unfold gap;positivity
  have rp : 0<R δ := by unfold R;positivity
  have dp : 0<D N δ := by unfold D;positivity
  have ap : 0<A N δ := by unfold A;positivity
  have kp : 0<k := by dsimp [k];positivity
  have k1 : k≤1 := (half_le_self gp.le).trans (CircleKernelGD.gap_le_one hn)
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
  change 0≤b ∧ b≤1 at wb
  change max _ (max _ (max _ (max _ _)))≤L at hw
  simp only [max_le_iff] at hw
  obtain ⟨wA,wE,wM,wG,wS⟩ := hw
  have lp : 0<L := ap.trans_le wA
  have hm : 0<m := by exact_mod_cast Real.sqrt_pos.mp lp
  have small : ρ≤1 := (div_le_one lp).mpr wA
  have en : 36/δ≤(m:ℝ) := by
    calc
      36/δ = sqrt (36/δ)^2 := (sq_sqrt (by positivity)).symm
      _ ≤ L^2 := pow_le_pow_left₀ (sqrt_nonneg _) wE 2
      _ = m := sq_sqrt (Nat.cast_nonneg m)
  have margin : 10*((N+1:ℕ):ℝ)/(δ*A N δ)≤sqrt m := by simpa only [Nat.cast_add,Nat.cast_one,N] using wM
  obtain ⟨E,meas,bad,init⟩ := six_tests n m hn odd hm δ (A N δ) hδ hδ1 ap small en margin
  refine ⟨E,meas,bad,?_⟩
  intro z hz
  have I := init z hz
  have G : CircleFiniteDynamics.Bounds N b ρ (R δ) (gridScale N δ/L) (signedScale N b δ/L) z :=
    ⟨I.residual,I.energy,I.gridMargin,I.angular,I.gram,I.signed⟩
  have gpos : 0≤gridScale N δ := by unfold gridScale;positivity
  have spos : 0≤signedScale N b δ := by
    unfold signedScale
    exact mul_nonneg (by linarith only [div_nonneg (by norm_num : (0:ℝ)≤6) np.le,wb.2]) (sqrt_nonneg _)
  have D_eq : R δ/k=D N δ := by dsimp [k,D];ring
  have cash : 2/sqrt (m:ℝ)*R δ≤ρ*k := by
    dsimp only [ρ,L,A,D,k]; field_simp; linarith
  have drift : 36*ρ+gridScale N δ/L≤gap N-k := by
    have g : 2*(gridScale N δ+36*A N δ)≤L*gap N := (div_le_iff₀ gp).mp wG
    dsimp only [ρ,k]
    field_simp
    linarith only [g]
  have C := CircleFiniteDynamics.trajectory hn hm odd z hη hc wb.1
    (div_nonneg ap.le lp.le) small (div_nonneg gpos lp.le) (div_nonneg spos lp.le)
    kp k1 G cash drift
  have rt := (C.1 T).1.trans (time_bound nn hε hδ hη hc k1)
  have fit := rt.trans (min_le_left _ _)
  have opt := rt.trans (min_le_right _ _)
  have coeff : (signedScale N b δ/L+(1+b)*36*ρ)*(R δ/k) ≤ ε/(2*(N:ℝ)^2) := by
    rw [D_eq]
    have w : (2*(N:ℝ)^2*D N δ)*(signedScale N b δ+(1+b)*36*A N δ)≤L*ε := by
      convert (div_le_iff₀ hε).mp (show
        (2*(N:ℝ)^2*D N δ)*(signedScale N b δ+(1+b)*36*A N δ)/ε≤L from (by convert wS using 1;ring)) using 1
    dsimp only [ρ]
    field_simp
    linarith only [w]
  refine ⟨fit,((C.1 T).2.2.trans ?_),fun t => ⟨(C.1 t).1,(C.1 t).2.1.trans_eq D_eq⟩,C.2⟩
  have mulb := (mul_le_of_le_one_left (show 0≤rms η N z T from norm_nonneg _) wb.2).trans opt
  exact (add_le_add mulb coeff).trans_eq (by ring)

end CircleFiniteWidth
