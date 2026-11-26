module

public import CircleWeightedStep
public import CircleSynchronizedEscape
public import CirclePairedOrdering
import all CircleWeightedStep
import all CircleFlowMoments
import all CircleTangentDrift
import all CircleFlowPath
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Relative perturbation bounds for two-layer, simultaneous gradient descent
near a state with identical readouts and horizontal hidden weights. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDTube
open Real CircleFlowPath CircleWeightedStep CircleTangentDrift
variable {m N : ℕ}

/-- Each of the three coordinate errors is compared with the magnitude of
its own layer in the synchronized network. -/
def Near (z : State m) (a w e : ℝ) : Prop :=
  ∀ j, |z (j,0)-a| ≤ e* |a| ∧ |z (j,1)-w| ≤ e* |w| ∧ |z (j,2)| ≤ e* |w|

def Axial (c : State m) (a w : ℝ) : Prop :=
  ∀ j, c (j,0)=a ∧ c (j,1)=w ∧ c (j,2)=0

private theorem product_diff (x u y v : ℝ) :
    |x*y-u*v|≤ |x-u| * |y| + |u| * |y-v| := by
  rw [show x*y-u*v=(x-u)*y+u*(y-v) by ring]
  simpa only [abs_mul] using abs_add_le ((x-u)*y) (u*(y-v))

private theorem sum_bound {n : ℕ} {v : Fin n → ℝ} {C : ℝ} (h : ∀ i, |v i| ≤ C) :
    |∑ i, v i| ≤ n*C := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)).trans_eq (by simp))

private theorem times_root {n : ℕ} (hn : 0<n) (B : ℝ) :
    (1/sqrt n)*(n*B)=sqrt n*B := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  have s := Real.sq_sqrt h.le
  field_simp
  nlinarith only [congrArg (· * B) s]

private theorem root_cap {n : ℕ} (hn : 0<n) : 1≤sqrt (n:ℝ) := by
  exact Real.one_le_sqrt.mpr (by exact_mod_cast hn)

private theorem axes (i : Fin N) :
    |(circleInput N i).1|≤1 ∧ |(circleInput N i).2|≤1 := by
  exact ⟨(Complex.abs_re_le_norm _).trans (CircleEscape.grid_norm N i).le,
    (Complex.abs_im_le_norm _).trans (CircleEscape.grid_norm N i).le⟩

private theorem center_pre {c : State m} {a w : ℝ} (hc : Axial c a w)
    (j : Fin m) (x : ℝ × ℝ) : pre c j x = x.1*w := by
  simp [pre,(hc j).2.1,(hc j).2.2]

private theorem pre_diff {z c : State m} {a w e : ℝ} (hc : Axial c a w) (hz : Near z a w e)
    (j : Fin m) (x : ℝ × ℝ) (hx : |x.1|≤1 ∧ |x.2|≤1) :
    |pre z j x - pre c j x| ≤ 2*e* |w| := by
  rw [center_pre hc]
  change |x.1*z (j,1)+x.2*z (j,2)-x.1*w|≤_
  rw [show x.1*z (j,1)+x.2*z (j,2)-x.1*w=x.1*(z (j,1)-w)+x.2*z (j,2) by ring]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul,abs_mul]
  have u := (mul_le_of_le_one_left (abs_nonneg _) hx.1).trans (hz j).2.1
  have v := (mul_le_of_le_one_left (abs_nonneg _) hx.2).trans (hz j).2.2
  linarith

private def feat (z : State m) (j : Fin m) (x : ℝ×ℝ) := max (pre z j x) 0

private theorem center_feat {c : State m} {a w : ℝ} (hc : Axial c a w) (j : Fin m)
    (x : ℝ × ℝ) (hx : |x.1|≤1) : |feat c j x|≤ |w| := by
  rw [feat,center_pre hc,abs_of_nonneg (le_max_right ..)]
  apply max_le _ (abs_nonneg _)
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hx)

private theorem feat_diff {z c : State m} {a w e : ℝ} (hc : Axial c a w) (hz : Near z a w e)
    (j : Fin m) (x : ℝ×ℝ) (hx : |x.1|≤1 ∧ |x.2|≤1) :
    |feat z j x-feat c j x|≤2*e* |w| :=
  (abs_max_sub_max_le_abs _ _ _).trans (pre_diff hc hz j x hx)

private theorem feat_cap {z c : State m} {a w e : ℝ} (hc : Axial c a w) (hz : Near z a w e)
    (h1 : e≤1) (j : Fin m) (x : ℝ×ℝ) (hx : |x.1|≤1 ∧ |x.2|≤1) :
    |feat z j x|≤3* |w| := by
  have h := abs_sub_abs_le_abs_sub (feat z j x) (feat c j x)
  linarith [feat_diff hc hz j x hx,center_feat hc j x hx.1,mul_le_of_le_one_left (abs_nonneg w) h1]

private theorem readout_cap {z : State m} {a w e : ℝ} (hz : Near z a w e)
    (h1 : e≤1) (j : Fin m) : |z (j,0)| ≤ 2* |a| := by
  linarith [abs_sub_abs_le_abs_sub (z (j,0)) a, (hz j).1, mul_le_of_le_one_left (abs_nonneg a) h1]

private theorem center_output {c : State m} {a w : ℝ} (hc : Axial c a w) (hm : 0<m)
    (x : ℝ×ℝ) (hx : |x.1|≤1) : |output (1/sqrt m) c x|≤sqrt m*(|a| * |w|) := by
  rw [output,abs_mul,abs_of_nonneg (by positivity : 0≤1/sqrt (m:ℝ))]
  refine (mul_le_mul_of_nonneg_left (sum_bound (fun j => ?_)) (by positivity)).trans_eq (times_root hm _)
  rw [abs_mul,(hc j).1]
  exact mul_le_mul_of_nonneg_left (center_feat hc j x hx) (abs_nonneg _)

private theorem output_diff {z c : State m} {a w e : ℝ} (hc : Axial c a w) (hz : Near z a w e)
    (hm : 0<m) (he : 0≤e) (h1 : e≤1) (x : ℝ×ℝ) (hx : |x.1|≤1 ∧ |x.2|≤1) :
    |output (1/sqrt m) z x-output (1/sqrt m) c x|≤sqrt m*(5*e* |a| * |w|) := by
  unfold output
  rw [←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (by positivity : 0≤1/sqrt (m:ℝ))]
  refine (mul_le_mul_of_nonneg_left (sum_bound (fun j => ?_)) (by positivity)).trans_eq (times_root hm _)
  rw [(hc j).1]
  apply (product_diff (z (j,0)) a (feat z j x) (feat c j x)).trans
  have h := mul_le_mul (hz j).1 (feat_cap hc hz h1 j x hx) (abs_nonneg _) (mul_nonneg he (abs_nonneg _))
  have h' := mul_le_mul_of_nonneg_left (feat_diff hc hz j x hx) (abs_nonneg a)
  linarith

private theorem gate_same {z c : State m} {a w e : ℝ} (hN : 0<N) (odd : Odd N)
    (hc : Axial c a w) (hz : Near z a w e) (hw : 0 < |w|) (small : e≤1/(8*(N:ℝ)))
    (i : Fin N) (j : Fin m) : startGates z i j=startGates c i j := by
  have np : 0 < (N:ℝ) := by exact_mod_cast hN
  let x := circleInput N i
  have cap := pre_diff hc hz j x (axes i)
  have margin : 1/(N:ℝ) ≤ |x.1| := CircleSynchronizedEscape.grid_gate_margin N hN odd i
  have strict : |pre z j x-pre c j x| < |pre c j x| := by
    rw [center_pre hc,abs_mul]
    rw [center_pre hc] at cap
    apply cap.trans_lt
    apply mul_lt_mul_of_pos_right _ hw
    have aux : 2*(1/(8*(N:ℝ))) < 1/(N:ℝ) := by field_simp; linarith
    linarith
  change (if 0<pre z j x then (1:ℝ) else 0)=(if 0<pre c j x then 1 else 0)
  split_ifs <;> try rfl
  all_goals simp_all only [not_lt,abs_of_nonpos]
  all_goals grind [abs_lt,abs_of_neg,abs_of_pos,abs_le]

theorem output_near {z c : State m} {a w e : ℝ} (hc : Axial c a w) (hz : Near z a w e)
    (hm : 0<m) (he : 0≤e) (h1 : e≤1) (i : Fin N) :
    |output (1/sqrt m) z (circleInput N i)| ≤ sqrt m*((1+5*e)* |a| * |w|) := by
  have d := output_diff hc hz hm he h1 (circleInput N i) (axes i)
  have b := center_output hc hm (circleInput N i) (axes i).1
  linarith [abs_sub_abs_le_abs_sub (output (1/sqrt m) z (circleInput N i))
    (output (1/sqrt m) c (circleInput N i))]

private def B (k : Fin 3) (a w : ℝ) : ℝ := if k=0 then |w| else |a|

private def basis (z : State m) (i : Fin N) (p : Coord m) :=
  row 1 z (circleInput N i) (startGates z i) p

private theorem hidden_bounds {z c : State m} {a w e x : ℝ} (hc : Axial c a w)
    (hz : Near z a w e) (he : 0≤e) (h1 : e≤1) (i : Fin N) (j : Fin m)
    (hx : |x|≤1) (eqg : startGates z i j=startGates c i j) :
    |z (j,0)*startGates z i j*x| ≤ 3* |a| ∧
    |z (j,0)*startGates z i j*x-c (j,0)*startGates c i j*x| ≤ 2*e* |a| := by
  have gate : |startGates z i j|≤1 := by
    unfold startGates actualGate
    split <;> norm_num
  have contract (v : ℝ) : |v*startGates z i j*x| ≤ |v| := by
    rw [abs_mul,abs_mul]
    exact (mul_le_of_le_one_right (by positivity) hx).trans
      (mul_le_of_le_one_right (abs_nonneg _) gate)
  constructor
  · exact (contract _).trans ((readout_cap hz h1 j).trans (by linarith [abs_nonneg a]))
  · rw [←eqg,(hc j).1, ←sub_mul, ←sub_mul]
    exact (contract _).trans ((hz j).1.trans (by nlinarith only [mul_nonneg he (abs_nonneg a)]))

private theorem basis_bounds {z c : State m} {a w e : ℝ} (hc : Axial c a w)
    (hz : Near z a w e) (he : 0≤e) (h1 : e≤1) (i : Fin N) (p : Coord m)
    (same : ∀ j, startGates z i j=startGates c i j) :
    |basis z i p| ≤ 3*B p.2 a w ∧
    |basis z i p-basis c i p| ≤ 2*e*B p.2 a w := by
  obtain ⟨j,k⟩ := p
  fin_cases k
  · simpa [basis,row,feat,B] using
      And.intro (feat_cap hc hz h1 j (circleInput N i) (axes i))
        (feat_diff hc hz j (circleInput N i) (axes i))
  · simpa [basis,row,B] using hidden_bounds hc hz he h1 i j (axes i).1 (same j)
  · simpa [basis,row,B] using hidden_bounds hc hz he h1 i j (axes i).2 (same j)

private def res (z : State m) (i : Fin N) :=
  output (1/sqrt m) z (circleInput N i) - circleLabel N i

private theorem term_diff {z c : State m} {a w e : ℝ} (hc : Axial c a w)
    (hz : Near z a w e) (hm : 0<m) (he : 0≤e) (h1 : e≤1)
    (big : 1≤sqrt m*(|a| * |w|)) (i : Fin N) (p : Coord m)
    (same : ∀ j, startGates z i j=startGates c i j) :
    |res z i*basis z i p-res c i*basis c i p| ≤
      sqrt m*(21*e* |a| * |w| * B p.2 a w) := by
  have b := basis_bounds hc hz he h1 i p same
  have rd : |res z i-res c i| ≤ sqrt m*(5*e* |a| * |w|) := by
    simpa [res] using output_diff hc hz hm he h1 (circleInput N i) (axes i)
  have rc : |res c i| ≤ 3*(sqrt m*(|a| * |w|)) := by
    have y : |circleLabel N i| ≤ 2 := by
      exact (abs_add_le ..).trans (by rw [abs_one]; linarith [(axes i).1])
    exact (abs_sub _ _).trans (by linarith [center_output hc hm (circleInput N i) (axes i).1])
  apply (product_diff ..).trans
  have d := mul_le_mul rd b.1 (abs_nonneg _) (by positivity)
  have c' := mul_le_mul rc b.2 (abs_nonneg _) (by positivity)
  linarith

private theorem dir_form (τ : ℝ) (z : State m) (p : Coord m) :
    direction τ N z p = -rate τ p*((1/(N:ℝ))*(1/sqrt m))*
      ∑ i : Fin N, res z i*basis z i p := by
  unfold direction velocity gradient
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [basis,row,res,CircleFlowPath.residual]
  ring

private theorem direction_diff {z c : State m} {τ a w e : ℝ} (hn : 0<N) (hm : 0<m)
    (odd : Odd N) (hc : Axial c a w) (hz : Near z a w e) (ht : 0≤τ) (he : 0≤e) (h1 : e≤1)
    (hw : 0 < |w|) (big : 1≤sqrt m*(|a| * |w|)) (small : e≤1/(8*(N:ℝ))) (p : Coord m) :
    |direction τ N z p-direction τ N c p| ≤ rate τ p*(21*e* |a| * |w| * B p.2 a w) := by
  let D := 21*e* |a| * |w| * B p.2 a w
  have hnp : 0<(N:ℝ) := by exact_mod_cast hn
  have hmp : 0<(m:ℝ) := by exact_mod_cast hm
  have rs : 0<sqrt (m:ℝ) := Real.sqrt_pos.mpr hmp
  have ratep : 0≤rate τ p := by unfold rate; split <;> positivity
  simp only [dir_form,←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_neg,
    abs_of_nonneg ratep,abs_of_nonneg (by positivity : 0≤1/(N:ℝ)),
    abs_of_nonneg (by positivity : 0≤1/sqrt (m:ℝ))]
  have bd := sum_bound (fun i : Fin N =>
    term_diff hc hz hm he h1 big i p (gate_same hn odd hc hz hw small i))
  calc
    _ ≤ (rate τ p * (1/(N:ℝ)*(1/sqrt m))) * ((N:ℝ)*(sqrt m*D)) :=
      mul_le_mul_of_nonneg_left bd (by positivity)
    _ = _ := by field_simp; ring

private theorem inflate {u v M e : ℝ} (he : 0≤e) (hv : 0≤v)
    (grown : u≤M) (next : M/32≤v) : e*u+21*e*M≤1024*e*v := by
  have h := mul_le_mul_of_nonneg_left grown he
  have h' := mul_le_mul_of_nonneg_left next he
  nlinarith only [h,h',mul_nonneg he hv]

/-- One simultaneous update tracks the exact axial update with a relative
error increase of at most 1024. Gate constancy is proved from odd-grid
geometry, including for the coordinates of the perturbed network. -/
theorem step_near {z c : State m} {τ η a w a' w' e : ℝ}
    (hn : 0<N) (hm : 0<m) (odd : Odd N) (hc : Axial c a w)
    (hc' : Axial (segment τ N c η) a' w') (hz : Near z a w e)
    (ht : 0≤τ) (heta : 0≤η) (he : 0≤e) (small : e≤1/(8*(N:ℝ)))
    (hw : 0 < |w|) (big : 1≤sqrt m*(|a| * |w|))
    (growA : 1≤η* |w|^2) (growW : 1≤η*τ* |a|^2)
    (nextA : η* |a| * |w|^2/32≤ |a'|) (nextW : η*τ* |a|^2* |w|/32≤ |w'|) :
    Near (segment τ N z η) a' w' (1024*e) := by
  have np : 1≤(N:ℝ) := by exact_mod_cast hn
  have h1 : e≤1 := small.trans ((div_le_one₀ (by positivity)).mpr (by linarith))
  have step (p : Coord m) :
      |segment τ N z η p-segment τ N c η p| ≤
      |z p-c p| + η*(rate τ p*(21*e* |a| * |w| * B p.2 a w)) := by
    change |z p+η*direction τ N z p-(c p+η*direction τ N c p)|≤_
    rw [show z p+η*direction τ N z p-(c p+η*direction τ N c p)=
      (z p-c p)+η*(direction τ N z p-direction τ N c p) by ring]
    exact (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg heta]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (direction_diff hn hm odd hc hz ht he h1 hw big small p) heta) _)
  have ga : |a| ≤ η* |a| * |w|^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left growA (abs_nonneg a)]
  have gw : |w| ≤ η*τ* |a|^2* |w| := by
    nlinarith only [mul_le_mul_of_nonneg_right growW (abs_nonneg w)]
  have ba := inflate he (abs_nonneg a') ga nextA
  have bw := inflate he (abs_nonneg w') gw nextW
  intro j
  have sa := step (j,0)
  have sx := step (j,1)
  have sy := step (j,2)
  simp [rate,B,(hc j).1,(hc' j).1] at sa
  simp [rate,B,(hc j).2.1,(hc' j).2.1] at sx
  simp [rate,B,(hc j).2.2,(hc' j).2.2] at sy
  exact ⟨by linarith [(hz j).1],by linarith [(hz j).2.1],by linarith [(hz j).2.2]⟩

end CirclePairedGDTube
