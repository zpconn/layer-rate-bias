module

public import CircleSeedIntegrability
public import CircleEulerLimits
import all CircleEscape
import all CircleSeedIntegrability
import all CircleInitializationCheck
import all CircleEscapeBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Synchronized Gaussian lower boxes for simultaneous discrete circle GD. -/
@[expose] public section
noncomputable section
namespace CircleSynchronizedEscape
open Set Real CircleEscape CircleEscapeBridge CircleSeedIntegrability
open scoped InnerProductSpace

def label (N : ℕ) (i : Fin N) := 1+(gridPoint N i).re

def advance (N m : ℕ) (η : ℝ) : Net ℂ m → Net ℂ m :=
  step (gridPoint N) (label N) (1/sqrt m) (η/(N*sqrt m))

def center (m : ℕ) (σ s : ℝ) : Net ℂ m := ⟨fun _ => σ*s, fun _ => (s:ℂ)⟩

def mask (N : ℕ) (s : ℝ) (i : Fin N) := gate (s:ℂ) (gridPoint N i)

def drive (N m : ℕ) (s : ℝ) (n : Net ℂ m) : ℂ :=
  (1/(N*sqrt m)) • ∑ i, ((output (1/sqrt m) n (gridPoint N i)-label N i)*mask N s i) • gridPoint N i

private theorem same_gate_update (N m : ℕ) (η s : ℝ) (n : Net ℂ m)
    (g : ∀ j i, gate (n.w j) (gridPoint N i)=mask N s i) (j : Fin m) :
    (advance N m η n).a j=n.a j-η*inner ℝ (n.w j) (drive N m s n) ∧
    (advance N m η n).w j=n.w j-(η*n.a j) • drive N m s n := by
  have f (i : Fin N) : feature (n.w j) (gridPoint N i)=mask N s i*inner ℝ (n.w j) (gridPoint N i) := by
    rw [←g j i,gate_projection]
  simp only [advance,step,drive, inner_smul_right,inner_sum,f,g]
  constructor
  · congr 1
    simp_rw [←mul_assoc]
    ring
  · rw [smul_smul]
    congr 2
    ring

private theorem real_inner (s : ℝ) (x : ℂ) : inner ℝ (s:ℂ) x = s*x.re := by
  rw [Complex.inner]; simp [mul_comm]

private theorem center_output (N m : ℕ) (hm : 0<m) (σ s : ℝ) (i : Fin N) :
    output (1/sqrt m) (center m σ s) (gridPoint N i) = sqrt m*(σ*s)*max (s*(gridPoint N i).re) 0 := by
  have h : 0<(m:ℝ) := by exact_mod_cast hm
  have r := Real.sqrt_pos.mpr h
  simp [output,center,feature,mul_comm]
  field_simp
  linear_combination -(σ*s*max (s*(gridPoint N i).re) 0)*Real.sq_sqrt h.le

private theorem gate_scalar (N : ℕ) (s : ℝ) (i : Fin N) :
    mask N s i = if 0<s*(gridPoint N i).re then 1 else 0 := by simp [mask,gate,mul_comm]

private theorem grid_reflect (N : ℕ) [NeZero N] (i : Fin N) :
    (gridPoint N (-i)).re=(gridPoint N i).re ∧ (gridPoint N (-i)).im= -(gridPoint N i).im := by
  by_cases h : i=0
  · subst i; simp [gridPoint]
  have nz : i.val ≠ 0 := fun hz => h (Fin.ext hz)
  have npos : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have val : ((-i).val:ℝ)=(N:ℝ)-(i.val:ℝ) := by
    have v : (-i).val=N-i.val := by
      rw [Fin.val_neg']
      exact Nat.mod_eq_of_lt (by omega)
    rw [v,Nat.cast_sub i.isLt.le]
  have angle : 2*π/N*((-i).val:ℝ)=2*π-(2*π/N*(i.val:ℝ)) := by rw [val]; field_simp
  simp [gridPoint,angle]

private theorem sum_imag_zero (N : ℕ) [NeZero N] (f : Fin N → ℝ)
    (even : ∀ i, f (-i)=f i) : ∑ i, f i*(gridPoint N i).im=0 := by
  let a := fun i => f i*(gridPoint N i).im
  have perm : ∑ i, a (-i) = ∑ i, a i := Equiv.sum_comp (Equiv.neg (Fin N)) a
  have row (i : Fin N) : a (-i)= -a i := by simp [a,even,(grid_reflect N i).2]
  simp_rw [row,Finset.sum_neg_distrib] at perm
  linarith

def mu (N : ℕ) (s : ℝ) := (∑ i, mask N s i*(gridPoint N i).re^2)/N

def psi (N : ℕ) (s : ℝ) := (∑ i, mask N s i*label N i*(gridPoint N i).re)/N

private theorem mask_abs (N : ℕ) (s : ℝ) (i : Fin N) : |mask N s i| ≤ 1 := by
  rw [gate_scalar]; split <;> norm_num

private theorem coord_cap (N : ℕ) (i : Fin N) : |(gridPoint N i).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (grid_norm N i).le

private theorem psi_abs (N : ℕ) (hN : 0<N) (s : ℝ) : |psi N s| ≤ 2 := by
  have p : (0:ℝ)<N := by exact_mod_cast hN
  rw [psi,abs_div,abs_of_pos p,div_le_iff₀ p]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin N, (2:ℝ) := by
      apply Finset.sum_le_sum; intro i _
      have y : |label N i| ≤ 2 := (abs_add_le _ _).trans (by linarith [coord_cap N i,abs_one (α:=ℝ)])
      rw [abs_mul,abs_mul]
      simpa using mul_le_mul (mul_le_mul (mask_abs N s i) y (abs_nonneg _) zero_le_one)
        (coord_cap N i) (abs_nonneg _) (by norm_num : 0≤(1:ℝ)*2)
    _ = _ := by simp; ring

private theorem mu_lower (N : ℕ) (hN : 3≤N) {s : ℝ} (hs : s≠0) : 1/16 ≤ mu N s := by
  have p : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have g := (CircleGridMargin.grid_relu_sum_bounds N hN (s:ℂ)).2
  have row (i : Fin N) : feature (s:ℂ) (gridPoint N i)^2 = s^2*(mask N s i*(gridPoint N i).re^2) := by
    rw [gate_scalar,feature,real_inner]
    split_ifs with h
    · rw [max_eq_left h.le]; ring
    · rw [max_eq_right (le_of_not_gt h)]; ring
  simp_rw [row] at g
  rw [←Finset.mul_sum,Complex.norm_real, Real.norm_eq_abs,sq_abs] at g
  rw [mu,le_div_iff₀ p]
  apply le_of_mul_le_mul_left (a:=s^2) _ (sq_pos_of_ne_zero hs)
  linarith

private theorem center_drive (N m : ℕ) (hN : 0<N) (hm : 0<m) (σ s : ℝ) :
    drive N m s (center m σ s) = ((σ*s^2*mu N s-psi N s/sqrt m : ℝ):ℂ) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  let a := fun i => (sqrt m*(σ*s)*max (s*(gridPoint N i).re) 0-label N i)*mask N s i
  have row (i : Fin N) : a i*(gridPoint N i).re =
      sqrt m*(σ*s^2)*(mask N s i*(gridPoint N i).re^2) - mask N s i*label N i*(gridPoint N i).re := by
    dsimp [a]; rw [gate_scalar]
    split_ifs with h
    · rw [max_eq_left h.le]; ring
    · ring
  have even (i : Fin N) : a (-i)=a i := by simp [a,label,gate_scalar,(grid_reflect N i).1]
  rw [drive]
  simp_rw [center_output N m hm]
  apply Complex.ext
  · rw [Complex.smul_re,smul_eq_mul]
    change (1/(N*sqrt m))*(∑ i, (a i) • gridPoint N i).re = _
    rw [Complex.re_sum]
    simp only [Complex.smul_re, smul_eq_mul,row, Finset.sum_sub_distrib,←Finset.mul_sum,mu,psi,Complex.ofReal_re]
    field_simp
  · rw [Complex.smul_im,smul_eq_mul]
    change (1/(N*sqrt m))*(∑ i, (a i) • gridPoint N i).im = _
    simp only [Complex.im_sum, Complex.smul_im, smul_eq_mul,sum_imag_zero N a even,mul_zero,Complex.ofReal_im]

def scalarStep (N m : ℕ) (η σ s : ℝ) := s*(1-η*(mu N s*s^2-σ*psi N s/sqrt m))

theorem center_advance (N m : ℕ) (hN : 0<N) (hm : 0<m) (η σ s : ℝ) (sgn : σ^2=1) :
    advance N m η (center m σ s) = center m σ (scalarStep N m η σ s) := by
  have h (j : Fin m) := same_gate_update N m η s (center m σ s) (fun _ _ => rfl) j
  have g := center_drive N m hN hm σ s
  have extN {u v : Net ℂ m} (a : ∀ j,u.a j=v.a j) (w : ∀ j,u.w j=v.w j) : u=v := by
    cases u; cases v; congr <;> exact funext ‹_›
  apply extN <;> intro j
  · rw [(h j).1,g]; change σ*s-η*inner ℝ (s:ℂ) _=σ*scalarStep N m η σ s
    rw [real_inner,Complex.ofReal_re,scalarStep]
    linear_combination -(η*s*psi N s/(sqrt m))*sgn
  · rw [(h j).2,g]
    change (s:ℂ)-(η*(σ*s)) • ((σ*s^2*mu N s-psi N s/sqrt m:ℝ):ℂ) = _
    apply Complex.ext
    · simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re,center,scalarStep]
      linear_combination -(η*s^3*mu N s)*sgn
    · simp only [Complex.sub_im,Complex.smul_im,smul_eq_mul,Complex.ofReal_im,center,mul_zero,sub_zero]

/-- At every signed center past the threshold the exact step reverses its
sign and increases its absolute value by at least a cubic divided by L². -/
theorem center_cubic (N m : ℕ) (hN : 3≤N) (hm : 0<m) {η L σ s : ℝ}
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η)
    (sign : |σ|=1) (large : 2*L≤|s|) :
    (η*|s|^3/40 ≤ |scalarStep N m η σ s|) ∧ scalarStep N m η σ s * s < 0 := by
  have ab : 0 < |s| := lt_of_lt_of_le (by linarith) large
  have sn := abs_pos.mp ab
  have muB := mu_lower N hN sn
  have h1 : (1:ℝ)≤sqrt m := one_le_sqrt.mpr (by exact_mod_cast hm)
  have yb : σ*psi N s/sqrt m ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    have b := (le_abs_self (σ*psi N s)).trans_eq (by rw [abs_mul,sign,one_mul])
    linarith [psi_abs N (by omega) s]
  have l := (eq_div_iff hη.ne').mp scale
  have g : 160≤η*s^2 := by
    have b := sq_le_sq₀ (by positivity : 0 ≤ 2*L) ab.le |>.mpr large
    rw [sq_abs] at b
    nlinarith [mul_le_mul_of_nonneg_left b hη.le]
  let k := η*(mu N s*s^2-σ*psi N s/sqrt m)-1
  have gain : η*s^2/40≤k := by
    dsimp [k]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right muB (sq_nonneg s)) hη.le,
      mul_le_mul_of_nonneg_left yb hη.le]
  have kp : 0<k := (by nlinarith : 0<η*s^2/40).trans_le gain
  have rhs : scalarStep N m η σ s = -(s*k) := by unfold scalarStep k; ring
  rw [rhs,abs_neg,abs_mul,abs_of_pos kp]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left gain ab.le,show |s|^3=|s| * s^2 by rw [pow_succ,sq_abs,mul_comm]]
  · nlinarith [mul_pos (sq_pos_of_ne_zero sn) kp]

/-- No training direction lies too close to the two vertical gate
boundaries on an odd regular grid. The odd numerator gives the 1/N margin. -/
theorem grid_gate_margin (N : ℕ) (hN : 0<N) (odd : Odd N) (i : Fin N) :
    1/(N:ℝ) ≤ |(gridPoint N i).re| := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  let t := 2*π/N*(i.val:ℝ)
  have a : t*(N:ℝ)=2*π*i.val := by dsimp [t]; field_simp
  have tr : 0≤t := by dsimp [t]; positivity
  have upper : t≤2*π := by
    apply (mul_le_mul_iff_of_pos_right hn).mp
    rw [a]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr i.isLt.le) (by positivity)
  have sep (k : ℕ) (hk : Odd k) : 1≤|(4:ℝ)*i.val-k*N| := by
    have evenodd : 4*i.val ≠ k*N := by
      have he : Even (4*i.val) := Even.mul_right (by decide : Even 4) _
      exact fun h => Nat.not_even_iff_odd.mpr (hk.mul odd) (h ▸ he)
    rcases lt_or_gt_of_ne evenodd with h|h
    · have z : 4*i.val+1≤k*N := by omega
      have z' : (4:ℝ)*i.val+1≤k*N := by exact_mod_cast z
      exact (by linarith : 1 ≤ -((4:ℝ)*i.val-k*N)).trans (neg_le_abs _)
    · have z : k*N+1≤4*i.val := by omega
      have z' : (k:ℝ)*N+1≤4*i.val := by exact_mod_cast z
      exact (by linarith : 1 ≤ (4:ℝ)*i.val-k*N).trans (le_abs_self _)
  have calc_sep (k : ℕ) (hk : Odd k) : 1/(N:ℝ) ≤ (2/π)*|t-k*π/2| := by
    have id : (t-k*π/2)=(π/(2*N))*(4*i.val-k*N) := by dsimp [t]; field_simp; ring
    rw [id,abs_mul,abs_of_pos (by positivity)]
    have h' := mul_le_mul_of_nonneg_left (sep k hk) (show 0 ≤ (2/π)*(π/(2*N)) by positivity)
    convert h' using 1 <;> field_simp
  change 1/(N:ℝ) ≤ |cos t|
  by_cases b : t≤π
  · have cap : |t-((1:ℕ):ℝ)*π/2|≤π/2 := abs_le.mpr ⟨by linarith,by linarith⟩
    have h := (calc_sep 1 (by decide)).trans (mul_abs_le_abs_sin cap)
    simpa [sin_sub_pi_div_two] using h
  · have cap : |t-((3:ℕ):ℝ)*π/2|≤π/2 := abs_le.mpr ⟨by linarith,by linarith⟩
    have h := (calc_sep 3 (by decide)).trans (mul_abs_le_abs_sin cap)
    simpa only [Nat.cast_ofNat,show t-3*π/2=(t-π/2)-π by ring,sin_sub_pi,sin_sub_pi_div_two,neg_neg] using h
/-- Maximum readout and hidden-vector relative deviations from the
synchronized center. This rectangular norm also bounds every gate score. -/
def Tube {m : ℕ} (n : Net ℂ m) (σ s d : ℝ) :=
  ∀ j, |n.a j-σ*s| ≤ d*|s| ∧ ‖n.w j-(s:ℂ)‖ ≤ d*|s|

private theorem feature_distance (u v x : ℂ) (hx : ‖x‖=1) :
    |feature u x - feature v x| ≤ ‖u-v‖ := by
  have h := ((LipschitzWith.id (α:=ℝ)).max_const 0).dist_le_mul (inner ℝ u x) (inner ℝ v x)
  simp only [id_eq,NNReal.coe_one,one_mul,Real.dist_eq,←inner_sub_left] at h
  exact h.trans (by simpa [hx] using abs_real_inner_le_norm (u-v) x)

private theorem feature_norm (u x : ℂ) (hx : ‖x‖=1) : |feature u x| ≤ ‖u‖ := by
  simpa [feature] using feature_distance u 0 x hx

private theorem tube_gate {N m : ℕ} (hN : 0<N) (odd : Odd N) {n : Net ℂ m} {σ s d : ℝ}
    (sn : s≠0) (tube : Tube n σ s d) (small : d≤1/(4*N)) :
    ∀ j i, gate (n.w j) (gridPoint N i)=mask N s i := by
  have p : (0:ℝ)<N := by exact_mod_cast hN
  have ds : d < 1/(N:ℝ) := small.trans_lt (one_div_lt_one_div_of_lt p (by linarith))
  intro j i
  let v := inner ℝ (n.w j) (gridPoint N i)
  let w := inner ℝ (s:ℂ) (gridPoint N i)
  have move : |v-w| ≤ d*|s| := by
    change |inner ℝ (n.w j) _ - inner ℝ (s:ℂ) _| ≤ _
    rw [←inner_sub_left]
    exact (by simpa [grid_norm] using abs_real_inner_le_norm (n.w j-(s:ℂ)) (gridPoint N i) :
      |inner ℝ (n.w j-(s:ℂ)) (gridPoint N i)| ≤ _).trans (tube j).2
  have size : d*|s| < |w| := by
    change _ < |inner ℝ (s:ℂ) _|
    rw [real_inner,abs_mul,mul_comm d]
    exact mul_lt_mul_of_pos_left (ds.trans_le (grid_gate_margin N hN odd i)) (abs_pos.mpr sn)
  change (if 0<v then 1 else 0) = if 0<w then 1 else 0
  by_cases pos : 0<w
  · have : 0<v := by linarith [(abs_le.mp move).1,abs_of_pos pos]
    simp [this,pos]
  · have : ¬0<v := by rw [abs_of_nonpos (le_of_not_gt pos)] at size; linarith [(abs_le.mp move).2]
    simp [this,pos]

private theorem response_distance {N m : ℕ} (hm : 0<m) {n : Net ℂ m} {σ s d : ℝ} (sgn : |σ|=1)
    (tube : Tube n σ s d) (hd : 0≤d) (small : d≤1) (i : Fin N) :
    |output (1/sqrt m) n (gridPoint N i)-output (1/sqrt m) (center m σ s) (gridPoint N i)| ≤
      sqrt m*(3*d*s^2) := by
  have hr : 0<sqrt m := sqrt_pos.mpr (by exact_mod_cast hm)
  let x := gridPoint N i
  have hx : ‖x‖=1 := grid_norm _ _
  have nrm : ‖(s:ℂ)‖=|s| := by simp
  have read : |σ*s|=|s| := by simp [abs_mul,sgn]
  have cap (j : Fin m) : ‖n.w j‖ ≤ 2*|s| := by
    have h := norm_sub_norm_le (n.w j) (s:ℂ)
    rw [nrm] at h
    linarith [(tube j).2,mul_le_mul_of_nonneg_right small (abs_nonneg s)]
  have atom (j : Fin m) : |n.a j*feature (n.w j) x-(σ*s)*feature (s:ℂ) x| ≤ 3*d*s^2 := by
    rw [show n.a j*feature (n.w j) x-(σ*s)*feature (s:ℂ) x =
      (n.a j-σ*s)*feature (n.w j) x+(σ*s)*(feature (n.w j) x-feature (s:ℂ) x) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,read]
    have h := mul_le_mul (tube j).1 ((feature_norm _ _ hx).trans (cap j)) (abs_nonneg _) (by positivity)
    have g := mul_le_mul_of_nonneg_left ((feature_distance _ _ _ hx).trans (tube j).2) (abs_nonneg s)
    nlinarith [show |s| * |s|=s^2 by rw [←sq,sq_abs]]
  change |(1/sqrt m)*(∑ j,n.a j*feature (n.w j) x)-
      (1/sqrt m)*(∑ _j:Fin m,(σ*s)*feature (s:ℂ) x)| ≤ _
  rw [←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_of_pos (one_div_pos.mpr hr)]
  have h := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun j _ => atom j))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0≤1/sqrt m)).trans_eq
  field_simp
  linear_combination -(d*s^2)*Real.sq_sqrt (Nat.cast_nonneg m)

private theorem drive_distance {N m : ℕ} (hN : 0<N) (hm : 0<m) {n : Net ℂ m} {σ s d : ℝ}
    (sgn : |σ|=1) (tube : Tube n σ s d) (hd : 0≤d) (small : d≤1) :
    ‖drive N m s n-drive N m s (center m σ s)‖ ≤ 3*d*s^2 := by
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  unfold drive
  rw [← smul_sub,←Finset.sum_sub_distrib,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity : 0≤1/(N*sqrt m))).trans
  let f := fun i => output (1/sqrt m) n (gridPoint N i)
  let g := fun i => output (1/sqrt m) (center m σ s) (gridPoint N i)
  have row (i : Fin N) : ‖((f i-label N i)*mask N s i) • gridPoint N i -
      ((g i-label N i)*mask N s i) • gridPoint N i‖ ≤ sqrt m*(3*d*s^2) := by
    rw [← sub_smul,←sub_mul,sub_sub_sub_cancel_right,norm_smul,grid_norm,mul_one,Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (mask_abs N s i)).trans (response_distance hm sgn tube hd small i)
  have b := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => row i)
  apply (mul_le_mul_of_nonneg_left b (by positivity : 0≤1/(N*sqrt m))).trans_eq
  simp
  field_simp

private theorem mu_upper (N : ℕ) (hN : 0<N) (s : ℝ) : |mu N s| ≤ 1 := by
  have p : (0:ℝ)<N := by exact_mod_cast hN
  rw [mu,abs_div,abs_of_pos p,div_le_iff₀ p,one_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i:Fin N, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_pow]
      exact (mul_le_of_le_one_left (by positivity) (mask_abs N s i)).trans (pow_le_one₀ (abs_nonneg _) (coord_cap N i))
    _ = _ := by simp

private theorem inner_difference (w w' G G' : ℂ) :
    |inner ℝ w G - inner ℝ w' G'| ≤ ‖w-w'‖*‖G‖+‖w'‖*‖G-G'‖ := by
  rw [show inner ℝ w G-inner ℝ w' G'=inner ℝ (w-w') G+inner ℝ w' (G-G') by
    rw [inner_sub_left,inner_sub_right]; ring]
  exact (abs_add_le ..).trans (add_le_add (abs_real_inner_le_norm ..) (abs_real_inner_le_norm ..))

private theorem smul_difference (a b : ℝ) (G G' : ℂ) :
    ‖a • G-b • G'‖ ≤ |a-b| * ‖G‖+|b| * ‖G-G'‖ := by
  rw [show a • G-b • G'=(a-b) • G+b • (G-G') by rw [sub_smul,smul_sub]; abel]
  simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le ((a-b) • G) (b • (G-G'))

theorem tube_advance (N m : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) {η L σ s d : ℝ}
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (sign : |σ|=1) (large : 2*L≤|s|)
    (hd : 0≤d) (small : d≤1/(4*N)) (n : Net ℂ m) (tube : Tube n σ s d) :
    Tube (advance N m η n) σ (scalarStep N m η σ s) (512*d) := by
  have np : (3:ℝ)≤N := by exact_mod_cast hN
  have d1 : d≤1 := small.trans (by apply (div_le_one (by positivity : 0<4*(N:ℝ))).mpr; linarith)
  have hrs : 1≤sqrt m := one_le_sqrt.mpr (by exact_mod_cast hm)
  have ab : 0 < |s| := lt_of_lt_of_le (by linarith) large
  have sql := (eq_div_iff hη.ne').mp scale
  have b := (sq_le_sq₀ (by positivity) ab.le).mpr large
  rw [sq_abs] at b
  have gfloor : 160≤η*s^2 := by nlinarith [mul_le_mul_of_nonneg_left b hη.le]
  have ss : 2≤s^2 := by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg s)]
  let G := drive N m s n
  let G' := drive N m s (center m σ s)
  have diff : ‖G-G'‖ ≤ 3*d*s^2 := drive_distance (by omega) hm sign tube hd d1
  have star : ‖G'‖ ≤ s^2+2 := by
    change ‖drive N m s (center m σ s)‖ ≤ _
    rw [center_drive N m (by omega) hm,Complex.norm_real,Real.norm_eq_abs]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_mul,sign,one_mul,abs_of_nonneg (sq_nonneg _),abs_div,
      abs_of_nonneg (sqrt_nonneg _)]
    exact add_le_add (mul_le_of_le_one_right (sq_nonneg _) (mu_upper N (by omega) s))
      ((div_le_iff₀ (by linarith)).mpr (by linarith [psi_abs N (by omega) s]))
  have gnorm : ‖G‖ ≤ 5*s^2 := by
    have h := norm_sub_norm_le G G'
    nlinarith [mul_le_mul_of_nonneg_right d1 (sq_nonneg s)]
  have cub := (center_cubic N m hN hm hη hc hL scale sign large).1
  have total : d*|s|+η*(d*|s| * (5*s^2)+|s| * (3*d*s^2)) ≤ 512*d*|scalarStep N m η σ s| := by
    have c := mul_le_mul_of_nonneg_left cub (mul_nonneg (by norm_num : 0≤(512:ℝ)) hd)
    have orig := mul_le_mul_of_nonneg_right gfloor (mul_nonneg hd (abs_nonneg s))
    rw [show |s|^3=s^2*|s| by rw [pow_succ,sq_abs]] at c
    nlinarith only [c,orig,show 0≤η*s^2*(d*|s|) by positivity]
  have csq : σ^2=1 := by rw [←sq_abs,sign]; norm_num
  have ident := center_advance N m (by omega) hm η σ s csq
  have hk := tube_gate (by omega : 0<N) odd (abs_pos.mp ab) tube small
  have rr (j : Fin m) := same_gate_update N m η s n hk j
  have rc (j : Fin m) := same_gate_update N m η s (center m σ s) (fun _ _ => rfl) j
  intro j
  have sc (v : ℝ) (h : |v|≤d*|s|) : |v| * ‖G‖ ≤ d*|s| * (5*s^2) :=
    mul_le_mul h gnorm (norm_nonneg _) (by positivity)
  have vc : ‖n.w j-(s:ℂ)‖*‖G‖ ≤ d*|s| * (5*s^2) :=
    mul_le_mul (tube j).2 gnorm (norm_nonneg _) (by positivity)
  have rad : ‖(s:ℂ)‖=|s| := by simp
  have asg : |σ*s|=|s| := by simp [abs_mul,sign]
  have ih : |inner ℝ (n.w j) G - inner ℝ (s:ℂ) G'| ≤ d*|s| * (5*s^2)+|s| * (3*d*s^2) :=
    (inner_difference ..).trans (add_le_add vc (by rw [rad]; exact mul_le_mul_of_nonneg_left diff (abs_nonneg s)))
  have wh : ‖(n.a j) • G-(σ*s) • G'‖ ≤ d*|s| * (5*s^2)+|s| * (3*d*s^2) :=
    (smul_difference ..).trans (add_le_add (sc _ (tube j).1) (by rw [asg]; exact mul_le_mul_of_nonneg_left diff (abs_nonneg s)))
  constructor
  · change |(advance N m η n).a j-(center m σ (scalarStep N m η σ s)).a j| ≤ _
    rw [←ident,(rr j).1,(rc j).1]
    change |n.a j-η*inner ℝ (n.w j) G-(σ*s-η*inner ℝ (s:ℂ) G')| ≤ _
    rw [show n.a j-η*inner ℝ (n.w j) G-(σ*s-η*inner ℝ (s:ℂ) G') =
      (n.a j-σ*s)-η*(inner ℝ (n.w j) G-inner ℝ (s:ℂ) G') by ring]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_of_pos hη]
    exact (add_le_add (tube j).1 (mul_le_mul_of_nonneg_left ih hη.le)).trans total
  · change ‖(advance N m η n).w j-(center m σ (scalarStep N m η σ s)).w j‖ ≤ _
    rw [←ident,(rr j).2,(rc j).2]
    change ‖(n.w j-(η*n.a j) • G)-((s:ℂ)-(η*(σ*s)) • G')‖ ≤ _
    rw [show (n.w j-(η*n.a j) • G)-((s:ℂ)-(η*(σ*s)) • G') =
      (n.w j-(s:ℂ))-η • (n.a j • G-(σ*s) • G') by rw [smul_sub,smul_smul,smul_smul]; abel]
    apply (norm_sub_le ..).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hη]
    exact (add_le_add (tube j).2 (mul_le_mul_of_nonneg_left wh hη.le)).trans total

def orbit (N m : ℕ) (η L σ : ℝ) : ℕ → ℝ
  | 0 => 2*L
  | t+1 => scalarStep N m η σ (orbit N m η L σ t)

private theorem orbit_growth (N m : ℕ) (hN : 3≤N) (hm : 0<m) {η L σ : ℝ}
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (sign : |σ|=1) (t : ℕ) :
    let s := orbit N m η L σ t
    radiusFloor L t ≤ |s| ∧ 0<(-1:ℝ)^t*s := by
  induction t with
  | zero => simp [orbit,radiusFloor,abs_of_pos hL]; constructor <;> linarith
  | succ t ih =>
    let s := orbit N m η L σ t
    have gr := center_cubic N m hN hm hη hc hL scale sign ((floor_large L hL.le t).trans ih.1)
    change radiusFloor L (t+1)≤|scalarStep N m η σ s| ∧ 0<(-1:ℝ)^(t+1)*scalarStep N m η σ s
    constructor
    · rw [←floor_step L hL t,scale]
      have b := pow_le_pow_left₀ (by dsimp [radiusFloor]; positivity) ih.1 3
      apply le_trans _ gr.1
      rw [div_div_eq_mul_div]; linarith [mul_le_mul_of_nonneg_left b hη.le]
    · have sq : ((-1:ℝ)^t)^2=1 := by rw [←sq_abs,abs_pow]; simp
      apply (mul_pos_iff_of_pos_right ih.2).mp
      rw [pow_succ]
      calc
        0 < -(scalarStep N m η σ s*s) := neg_pos.mpr gr.2
        _ = _ := by change _ = _ * (scalarStep N m η σ s) * (_*s); linear_combination (scalarStep N m η σ s*s)*sq

/-- Initial coordinate interval length of the synchronized Gaussian boxes. -/
def side (N T : ℕ) : ℝ := 1/(8*N*(512:ℝ)^T)

def location (σ L : ℝ) (k : Fin 3) := if k=0 then σ*(2*L) else if k=1 then 2*L else 0

def syncBox (N m T : ℕ) (σ L : ℝ) : Set (Seed m) :=
  univ.pi fun i => Icc (location σ L i.2) (location σ L i.2+side N T)

theorem measurable_syncBox (N m T : ℕ) (σ L : ℝ) : MeasurableSet (syncBox N m T σ L) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)

private theorem init_tube {N m T : ℕ} {σ L : ℝ} (hN : 0<N) (hs : 1≤2*L)
    (ω : Seed m) (inBox : ω ∈ syncBox N m T σ L) :
    Tube (initial ω) σ (2*L) (1/(4*N*512^T)) := by
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have ell : 0≤side N T := by unfold side; positivity
  have width : 2*side N T=1/(4*N*512^T) := by unfold side; field_simp; norm_num
  have cap (j : Fin m) (k : Fin 3) : |ω (j,k)-location σ L k|≤side N T := by
    have h := inBox (j,k) (mem_univ _)
    change location σ L k ≤ ω (j,k) ∧ ω (j,k) ≤ location σ L k+side N T at h
    exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  have bound : 2*side N T ≤ (1/(4*N*512^T))*|2*L| := by
    rw [←width,abs_of_nonneg (by linarith)]
    exact le_mul_of_one_le_right (by positivity) hs
  intro j
  constructor
  · exact (by simpa [initial,location] using cap j 0 : |(initial ω).a j-σ*(2*L)|≤side N T).trans
      ((by linarith : side N T≤2*side N T).trans bound)
  · apply le_trans _ bound
    apply Complex.norm_le_abs_re_add_abs_im _ |>.trans
    have h1 := cap j 1
    have h2 := cap j 2
    simp [location] at h1 h2
    simpa [initial] using add_le_add h1 h2 |>.trans_eq (by ring : side N T+side N T=2*side N T)

/-- Every simultaneous GD iterate in the narrow box shadows its synchronized
center. The last iterate has the published sign and escaping amplitude. -/
theorem box_escape (N m T : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) {η L σ : ℝ}
    (hη : 0<η) (hc : η≤1) (hL : 0<L) (scale : L^2=40/η) (sign : |σ|=1)
    (ω : Seed m) (inBox : ω∈syncBox N m T σ L) :
    amplitude m T L/2 ≤ ((-1)^T*σ)*trainedMean (path N m η) T ω := by
  let d (t : ℕ) := (512:ℝ)^t/(4*N*512^T)
  let s := orbit N m η L σ
  let n := path N m η ω
  have np : (3:ℝ)≤N := by exact_mod_cast hN
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have l : L^2*η=40 := (eq_div_iff hη.ne').mp scale
  have Llarge : 1≤2*L := by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg L)]
  have dpos (t : ℕ) : 0≤d t := by dsimp [d]; positivity
  have range (t : ℕ) (ht : t≤T) : d t≤1/(4*N) := by
    dsimp [d]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : 1≤(512:ℝ)) ht)
      (show 0≤4*(N:ℝ) by positivity)]
  have growth (t : ℕ) := orbit_growth N m hN hm hη hc hL scale sign t
  have tube (t : ℕ) (ht : t≤T) : Tube (n t) σ (s t) (d t) := by
    induction t with
    | zero => simpa [d,s,orbit,n,path,CircleInitializationCheck.train] using init_tube (by omega : 0<N) Llarge ω inBox
    | succ t ih =>
      have step := tube_advance N m hN odd hm hη hc hL scale sign
        ((floor_large L hL.le t).trans (growth t).1) (dpos t) (range t (by omega)) (n t) (ih (by omega))
      have eq : d (t+1)=512*d t := by dsimp [d]; rw [pow_succ]; ring
      rw [eq]
      exact step
  have clos := tube T le_rfl
  have r := (growth T).1
  have p : 0<(-1:ℝ)^T*s T := (growth T).2
  have unit : |(-1:ℝ)^T*σ|=1 := by simp [abs_mul,abs_pow,sign]
  have sg : (-1:ℝ)^T*s T=|s T| := by
    rw [← abs_of_pos p,abs_mul,abs_pow]; simp
  have s2 : σ^2=1 := by rw [←sq_abs,sign]; norm_num
  have close : d T≤1/4 := (range T le_rfl).trans (by apply one_div_le_one_div_of_le (by norm_num); linarith)
  have floor0 : 0 ≤ radiusFloor L T := by dsimp [radiusFloor]; positivity
  have cone : Cone (n T) ((-1)^T*σ) (3/4*radiusFloor L T) := by
    intro j
    have b := clos j
    have aa : |((-1:ℝ)^T*σ)*((n T).a j-σ*s T)|≤d T*|s T| := by simpa [abs_mul,unit] using b.1
    have dd := (abs_le.mp aa).1
    have id : ((-1:ℝ)^T*σ)*((n T).a j-σ*s T) = ((-1)^T*σ)*(n T).a j - |s T| := by
      rw [←sg]; linear_combination -((-1:ℝ)^T*s T)*s2
    rw [id] at dd
    have hh := norm_sub_norm_le ((s T:ℝ):ℂ) ((n T).w j)
    rw [norm_sub_rev,Complex.norm_real,Real.norm_eq_abs] at hh
    change radiusFloor L T ≤ |s T| at r
    constructor <;> linarith [b.2,mul_le_mul_of_nonneg_right close (abs_nonneg (s T))]
  have result := signed_mean (1/sqrt m) _ _ (n T) (by positivity) (by positivity) cone
  apply le_trans _ result
  unfold amplitude radiusFloor
  have scale' : (1/sqrt m)*(m:ℝ) = sqrt m := by field_simp; nlinarith [Real.sq_sqrt mp.le]
  rw [show (1/sqrt m/π)*(m:ℝ)=(1/sqrt m)*(m:ℝ)/π by ring,scale']
  nlinarith [sq_nonneg (L*2^(3^T:ℕ)),
    mul_nonneg (div_nonneg (sqrt_nonneg (m:ℝ)) pi_pos.le) (sq_nonneg (L*2^(3^T:ℕ)))]
