module

public import CircleSevenSpectrum
public import CircleSignedRow
public import CircleSevenIntervals
import all CircleMajorityFold
import all CircleSignedAngular
import all CircleSignedRow
import all CircleSevenSpectrum
import all CircleTeacherRKHS
import all CircleSpectrum
import all CircleSevenIntervals
import Mathlib.Tactic

/-! Rational certificates for the original, angular, and grouped seven-point designs. -/
@[expose] public section
noncomputable section
namespace CircleSevenDesign
open Real CircleSevenTrig CircleSevenSpectrum CircleSevenIntervals CircleSignedAngular
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private def piBox : Box π :=
  ⟨3.14159265358979323846,3.14159265358979323847,by exact_mod_cast pi_gt_d20.le,by exact_mod_cast pi_lt_d20.le⟩
private abbrev n := Box.nat
private def one : Box (1:ℝ) := (n 1).transport (by norm_num)
private def angleBox (j : ℕ) : Box (angle j) := (((n 2).mul piBox).mul (n j)).div (n 7)
private def cosBox0 : Box (cos (angle 0)) := one.transport (by simp [angle])
private def sinBox0 : Box (sin (angle 0)) := (n 0).transport (by simp [angle])
private def cosBox1 : Box (cos (angle 1)) :=
  ⟨0.62348980185873352,0.62348980185873354,by exact_mod_cast cos_one.1,by exact_mod_cast cos_one.2⟩
private def cosBox2 : Box (cos (angle 2)) :=
  ⟨-0.22252093395631442,-0.22252093395631439,by push_cast;exact_mod_cast cos_two.1,by push_cast;exact_mod_cast cos_two.2⟩
private def cosBox3 : Box (cos (angle 3)) :=
  ⟨-0.90096886790241914,-0.90096886790241911,by push_cast;exact_mod_cast cos_three.1,by push_cast;exact_mod_cast cos_three.2⟩
private theorem sin_eq_sqrt (j : ℕ) (hj : j≤3) : sin (angle j)=sqrt (1-cos (angle j)^2) := by
  have hj' : (j:ℝ)≤3 := by exact_mod_cast hj
  have h := sin_nonneg_of_nonneg_of_le_pi (show 0≤angle j by dsimp [angle];positivity)
    (show angle j≤π by dsimp [angle];nlinarith only [mul_le_mul_of_nonneg_left hj' pi_pos.le,pi_pos])
  rw [← sin_sq,Real.sqrt_sq h]
private def sinBox1 : Box (sin (angle 1)) :=
  ((one.sub cosBox1.sq).sqrt 0.781831482468027 0.781831482468032).transport (sin_eq_sqrt 1 (by decide))
private def sinBox2 : Box (sin (angle 2)) :=
  ((one.sub cosBox2.sq).sqrt 0.974927912181821 0.974927912181826).transport (sin_eq_sqrt 2 (by decide))
private def sinBox3 : Box (sin (angle 3)) :=
  ((one.sub cosBox3.sq).sqrt 0.433883739117556 0.433883739117561).transport (sin_eq_sqrt 3 (by decide))

private def sampleBox (t : ℝ) (tv : Box t) (j : ℕ) (sv : Box (sin (angle j))) (cv : Box (cos (angle j))) :
    Box (sample t j) :=
  (sv.add (((one.add tv).mul (piBox.sub (angleBox j))).mul cv)).div ((n 2).mul piBox)
private def sample00 : Box (sample (0:ℝ) 0) :=
  (sampleBox 0 ((n 0).transport (by norm_num)) 0 sinBox0 cosBox0).narrow 0.49999999999998 0.50000000000003
private def sample01 : Box (sample (0:ℝ) 1) :=
  (sampleBox 0 ((n 0).transport (by norm_num)) 1 sinBox1 cosBox1).narrow 0.34710727433489 0.34710727433494
private def sample02 : Box (sample (0:ℝ) 2) :=
  (sampleBox 0 ((n 0).transport (by norm_num)) 2 sinBox2 cosBox2).narrow 0.10748153910562 0.10748153910567
private def sample03 : Box (sample (0:ℝ) 3) :=
  (sampleBox 0 ((n 0).transport (by norm_num)) 3 sinBox3 cosBox3).narrow 0.00469982267184 0.00469982267189
private def sample10 : Box (sample (1:ℝ) 0) :=
  (sampleBox 1 one 0 sinBox0 cosBox0).narrow 0.99999999999998 1.00000000000003
private def sample11 : Box (sample (1:ℝ) 1) :=
  (sampleBox 1 one 1 sinBox1 cosBox1).narrow 0.56978220357015 0.56978220357020
private def sample12 : Box (sample (1:ℝ) 2) :=
  (sampleBox 1 one 2 sinBox2 cosBox2).narrow 0.05979848182927 0.05979848182932
private def sample13 : Box (sample (1:ℝ) 3) :=
  (sampleBox 1 one 3 sinBox3 cosBox3).narrow (-0.05965509646405) (-0.05965509646400)
private def modeBox (t : ℝ) (r : ℕ) (s₀ : Box (sample t 0)) (s₁ : Box (sample t 1))
    (s₂ : Box (sample t 2)) (s₃ : Box (sample t 3))
    (c₁ : Box (cos (angle (fold7 r)))) (c₂ : Box (cos (angle (fold7 (2*r)))))
    (c₃ : Box (cos (angle (fold7 (3*r))))) : Box (mode t r) :=
  (s₀.add ((n 2).mul (((s₁.mul c₁).add (s₂.mul c₂)).add (s₃.mul c₃)))).div (n 7)

private def c0 : Box (mode 0 0) :=
  (modeBox 0 0 sample00 sample01 sample02 sample03 cosBox0 cosBox0 cosBox0).narrow 0.20265389603208 0.20265389603217
private def c1 : Box (mode 0 1) :=
  (modeBox 0 1 sample00 sample01 sample02 sample03 cosBox1 cosBox2 cosBox3).narrow 0.125219016947 0.125219016952
private def c2 : Box (mode 0 2) :=
  (modeBox 0 2 sample00 sample01 sample02 sample03 cosBox2 cosBox3 cosBox1).narrow 0.022529753149 0.022529753154
private def c3 : Box (mode 0 3) :=
  (modeBox 0 3 sample00 sample01 sample02 sample03 cosBox3 cosBox1 cosBox2).narrow 0.000924281881 0.000924281886
private def d0 : Box (mode 1 0) :=
  (modeBox 1 0 sample10 sample11 sample12 sample13 cosBox0 cosBox0 cosBox0).narrow 0.305693025408 0.305693025413
private def d1 : Box (mode 1 1) :=
  (modeBox 1 1 sample10 sample11 sample12 sample13 cosBox1 cosBox2 cosBox3).narrow 0.255912675399 0.255912675404
private def d2 : Box (mode 1 2) :=
  (modeBox 1 2 sample10 sample11 sample12 sample13 cosBox2 cosBox3 cosBox1).narrow 0.080611604900 0.080611604905
private def d3 : Box (mode 1 3) :=
  (modeBox 1 3 sample10 sample11 sample12 sample13 cosBox3 cosBox1 cosBox2).narrow 0.010629206988 0.010629206993

/-- The grouped path budget uses the four conjugate frequency classes. -/
def groupedF := sqrt (mode 0 0+1)/mode 1 0+sqrt (2*mode 0 1+1/2)/mode 1 1+
  sqrt (2*mode 0 2)/mode 1 2+sqrt (2*mode 0 3)/mode 1 3
private def fBox : Box groupedF :=
  ((((((c0.add one).sqrt 1.096655776 1.096655781).div d0).add (((((n 2).mul c1).add (one.div (n 2))).sqrt 0.866278263 0.866278268).div d1)).add ((((n 2).mul c2).sqrt 0.212272243 0.212272248).div d2)).add ((((n 2).mul c3).sqrt 0.042994925 0.042994930).div d3)).narrow 13.6507462 13.6507473

def b := (3/π^2)/mode 1 0
private def bBox : Box b := (((n 3).div piBox.sq).div d0).narrow 0.9943424469 0.9943424472
private def amplitudeBox : Box (CircleMajorityFold.amplitude 7) :=
  (one.div (((n 2).mul (n 7)).mul (cosBox2.neg.transport halfCell_values.1))).transport (by norm_num [CircleMajorityFold.amplitude,CircleMajorityFold.halfCell])
private def cosHalfBox : Box (cos (CircleMajorityFold.halfCell 7)) :=
  sinBox2.transport (by norm_num [CircleMajorityFold.halfCell];exact halfCell_values.2)
private def diffBox := (one.div piBox).sub (bBox.mul amplitudeBox)
private def gBox : Box (G 7 b) :=
  ((diffBox.sq.add (((((n 2).mul bBox).mul amplitudeBox).mul (one.sub cosHalfBox)).div piBox)).sqrt
    0.0713815854 0.0713815857)
private def betaBox : Box (B 7 b) :=
  diffBox.absolute.greatest (((one.div piBox).sub ((bBox.mul amplitudeBox).mul cosHalfBox)).absolute)

def drift := 22*G 7 b+4*B 7 b+2*(1+b)
private def driftBox : Box drift :=
  ((((n 22).mul gBox).add ((n 4).mul betaBox)).add ((n 2).mul (one.add bBox))).narrow 5.58760532 5.58760539

def gap := 1/(7*π)^2
def ordinaryD := 2*sqrt 240/gap
def groupedD := 2*sqrt 120*groupedF
def h := 7*sqrt 1800
def v := (6/7+1-b)*sqrt 12600
private def gapBox : Box gap := one.div (((n 7).mul piBox).sq)
private def ordinaryBox : Box ordinaryD := (((n 2).mul ((n 240).sqrt 15.491933382 15.491933387)).div gapBox).narrow 14984.1268 14984.1270
private def groupedBox : Box groupedD := (((n 2).mul ((n 120).sqrt 10.954451148 10.954451153)).mul fBox).narrow 299.07286 299.07290
private def hBox : Box h := (n 7).mul ((n 1800).sqrt 42.426406869 42.426406874)
private def vBox : Box v := ((((n 6).div (n 7)).add one).sub bBox).mul ((n 12600).sqrt 112.249721601 112.249721606)

/-- The square of the five-term sufficient-width maximum for δ=ε=1/20 and N=7.
Here k is 10 for the total-energy margin and 135 for the readout-only margin. -/
def requiredWidth (D C k : ℝ) :=
  let A := 2*D
  (max (max (max (max A (sqrt 720)) (k*160/A)) (2*(h+36*A)/gap)) (1960*D*(v+C*A)))^2

private def widthBox {D C : ℝ} (dv : Box D) (cv : Box C) (k : ℕ) (hd : 0<((n 2).mul dv).lo) :
    Box (requiredWidth D C k) :=
  let av := (n 2).mul dv
  let margin := ((n k).mul (n 160)).div av hd
  let grid := ((n 2).mul (hBox.add ((n 36).mul av))).div gapBox
  let row := ((n 1960).mul dv).mul (vBox.add (cv.mul av))
  (((((av.greatest ((n 720).sqrt 26.83281572 26.83281574)).greatest margin).greatest grid).greatest row).sq)

theorem grouped_F : 13.6507462≤groupedF ∧ groupedF≤13.6507473 := by
  exact_mod_cast fBox.bounds 13.6507462 13.6507473

theorem angular_constants : 0.9943424469≤b ∧ b≤0.9943424472 ∧
    0.0071313925≤ B 7 b ∧ B 7 b≤0.0071313930 ∧
    0.0713815854≤ G 7 b ∧ G 7 b≤0.0713815857 ∧ 5.58760532≤drift ∧ drift≤5.58760539 := by
  have hb := bBox.bounds 0.9943424469 0.9943424472
  have hf := betaBox.bounds 0.0071313925 0.0071313930
  have hg := gBox.bounds 0.0713815854 0.0713815857
  have hc := driftBox.bounds 5.58760532 5.58760539
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2,by exact_mod_cast hf.1,by exact_mod_cast hf.2,by exact_mod_cast hg.1,by exact_mod_cast hg.2,by exact_mod_cast hc⟩

theorem movement_budgets : 14984.1268≤ordinaryD ∧ ordinaryD≤14984.1270 ∧
    299.07286≤groupedD ∧ groupedD≤299.07290 := by
  have a := ordinaryBox.bounds 14984.1268 14984.1270
  have g := groupedBox.bounds 299.07286 299.07290
  exact ⟨by exact_mod_cast a.1,by exact_mod_cast a.2,by exact_mod_cast g⟩

/-- All three published upward-rounded widths dominate the same finite design inequalities. -/
theorem sufficient_widths :
    requiredWidth ordinaryD (36*(1+b)) 10≤4*10^27 ∧
    requiredWidth ordinaryD drift 135≤243*10^23 ∧
    requiredWidth groupedD drift 135≤407*10^16 := by
  have a := (widthBox ordinaryBox ((n 36).mul (one.add bBox)) 10 (by decide +kernel)).bounds 0 (4*10^27)
  have g := (widthBox ordinaryBox driftBox 135 (by decide +kernel)).bounds 0 (243*10^23)
  have t := (widthBox groupedBox driftBox 135 (by decide +kernel)).bounds 0 (407*10^16)
  exact ⟨by exact_mod_cast a.2,by exact_mod_cast g.2,by exact_mod_cast t.2⟩

/-- Observable benchmark standard deviation for the seven-point interpolation law. -/
theorem reference_sd :
    0.0042290451≤sqrt (CircleSpectrum.variance 1 6) ∧
    sqrt (CircleSpectrum.variance 1 6)≤0.0042290458 := by
  let base : Box CircleSpectrum.c0 := (n 2).div piBox.sq
  have ah := mode_alias 0 (by norm_num) (by norm_num) (0:ZMod 7)
  have ah' : mode 0 0=CircleSpectrum.c0+CircleSpectrum.S 6 :=
    ah.trans (CircleTeacherRKHS.alias_zero 6 (by decide) (by decide))
  have formula : CircleSpectrum.variance 1 6=
      CircleSpectrum.c0*(1-b)^2+b^2*(mode 0 0-CircleSpectrum.c0) := by
    rw [CircleSpectrum.variance,weight_one,ah'];unfold b;ring
  let varBox := (base.mul (one.sub bBox).sq).add (bBox.sq.mul (c0.sub base))
  let result := (varBox.sqrt 0.0042290451 0.0042290458).transport (congrArg sqrt formula)
  exact_mod_cast result.bounds 0.0042290451 0.0042290458 le_rfl le_rfl

private theorem log_ratio :
    10.3209≤log (1960*sqrt 240) ∧ log (1960*sqrt 240)≤10.3212 := by
  have a : exp 0.64505625 ≤ 1.906096 := by
    apply (Real.exp_bound' (x:=0.64505625) (by norm_num) (by norm_num) (n:=9) (by decide)).trans
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have b' : 1.906128 ≤ exp 0.645075 := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.645075) 9)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have al : exp 10.3209≤30362 := by
    rw [show (10.3209:ℝ)=(16:ℕ)*0.64505625 by norm_num,exp_nat_mul]
    exact (pow_le_pow_left₀ (exp_pos _).le a 16).trans (by norm_num)
  have bh : 30368≤exp 10.3212 := by
    rw [show (10.3212:ℝ)=(16:ℕ)*0.645075 by norm_num,exp_nat_mul]
    exact (by norm_num : (30368:ℝ)≤1.906128^16).trans (pow_le_pow_left₀ (by norm_num) b' 16)
  have sq := sq_sqrt (by norm_num : (0:ℝ)≤240)
  exact ⟨(le_log_iff_exp_le (by positivity)).mpr (al.trans (by nlinarith [sqrt_nonneg 240])),
    (log_le_iff_le_exp (by positivity)).mpr ((by nlinarith [sqrt_nonneg 240] : 1960*sqrt 240≤30368).trans bh)⟩

private def logBox : Box (log (1960*sqrt 240)) :=
  ⟨10.3209,10.3212,by exact_mod_cast log_ratio.1,by exact_mod_cast log_ratio.2⟩

/-- The actual ceiling in the finite training theorem for N=7, η=1/2 and δ=ε=1/20. -/
theorem horizon :
    ⌈2/((1/2)*gap)*log (sqrt 240/min ((7:ℝ)⁻¹^3) (1/20/(2*7^2)))⌉₊=19966 := by
  have hb := (((n 4).div gapBox).mul logBox).bounds 19965.1 19965.9
  apply (Nat.ceil_eq_iff (by decide)).mpr
  norm_num [show (min ((7:ℝ)⁻¹^3) (1/20/(2*7^2)))=1/1960 by norm_num]
  rw [show (2:ℝ)/((1/2)*gap)=4/gap by ring,show sqrt 240/(1/1960)=1960*sqrt 240 by ring]
  have l : (19965.1:ℝ)≤4/gap*log (1960*sqrt 240) := by exact_mod_cast hb.1
  have u : 4/gap*log (1960*sqrt 240)≤(19965.9:ℝ) := by exact_mod_cast hb.2
  exact ⟨by linarith,by linarith⟩

/-- Round-to-nearest enclosures for all four covariance and tangent conjugacy classes. -/
theorem spectral_inputs :
    (0.20265385≤mode 0 0 ∧ mode 0 0≤0.20265395) ∧
    (0.12521895≤mode 0 1 ∧ mode 0 1≤0.12521905) ∧
    (0.02252975≤mode 0 2 ∧ mode 0 2≤0.02252985) ∧
    (0.0009242815≤mode 0 3 ∧ mode 0 3≤0.0009242825) ∧
    (0.30569295≤mode 1 0 ∧ mode 1 0≤0.30569305) ∧
    (0.25591265≤mode 1 1 ∧ mode 1 1≤0.25591275) ∧
    (0.08061155≤mode 1 2 ∧ mode 1 2≤0.08061165) ∧
    (0.01062915≤mode 1 3 ∧ mode 1 3≤0.01062925) := by
  exact ⟨by exact_mod_cast c0.bounds 0.20265385 0.20265395,
    by exact_mod_cast c1.bounds 0.12521895 0.12521905,
    by exact_mod_cast c2.bounds 0.02252975 0.02252985,
    by exact_mod_cast c3.bounds 0.0009242815 0.0009242825,
    by exact_mod_cast d0.bounds 0.30569295 0.30569305,
    by exact_mod_cast d1.bounds 0.25591265 0.25591275,
    by exact_mod_cast d2.bounds 0.08061155 0.08061165,
    by exact_mod_cast d3.bounds 0.01062915 0.01062925⟩

/-- Tight eigenvalue intervals for the RKHS comparison at frequencies zero and one. -/
theorem covariance_low_modes :
    (0.20265389603208≤mode 0 0 ∧ mode 0 0≤0.20265389603217) ∧
    (0.125219016947≤mode 0 1 ∧ mode 0 1≤0.125219016952) :=
  ⟨by exact_mod_cast c0.bounds 0.20265389603208 0.20265389603217,
   by exact_mod_cast c1.bounds 0.125219016947 0.125219016952⟩

end CircleSevenDesign
