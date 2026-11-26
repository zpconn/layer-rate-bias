module

public import CircleFiniteCoefficient
import all CircleFiniteCoefficient
import all CircleSpectrum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! A uniform fourth-order remainder for the finite-grid slope. -/
public section
noncomputable section
namespace CircleCoefficientRemainder
open CircleFiniteCoefficient CircleSpectrum Real

private theorem powers (n j : ℕ) :
    let t := rp 2 n
    let v := rp 2 j
    let z := offset n j
    aliasATerm n j ≤ t^2*v ∧
    0 ≤ aliasBTerm n j - (2*z+4*z^2) ∧
    aliasBTerm n j - (2*z+4*z^2) ≤ t^3*v := by
  dsimp only
  let z := offset n j
  have hz := off_bounds n j
  have zlo : 0 ≤ z := hz.1.le
  have zhi : z ≤ 1/4 := hz.2
  have hden : (1/2:ℝ)≤(1-z)^2 := by nlinarith [sq_nonneg z]
  have zv := (rp_bounds j).2
  have vp := (rp_bounds j).1.le
  have v2 : (rp 2 j)^2 ≤ rp 2 j := by nlinarith [mul_le_mul_of_nonneg_right zv vp]
  have v3 : (rp 2 j)^3 ≤ rp 2 j := by calc
    _ = rp 2 j*(rp 2 j)^2 := by ring
    _ ≤ 1*rp 2 j := mul_le_mul zv v2 (sq_nonneg _) (by norm_num)
    _ = _ := one_mul _
  have a : aliasATerm n j ≤ 4*z^2 := by
    change 2*z^2/(1-z)^2 ≤ _
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hden (sq_nonneg z)]
  have id : aliasBTerm n j - (2*z+4*z^2) = 2*z^3*(3-2*z)/(1-z)^2 := by
    change 2*z/(1-z)^2-(2*z+4*z^2)=_
    field_simp [show 1-z≠0 by linarith];ring
  have rem : 2*z^3*(3-2*z)/(1-z)^2 ≤ 12*z^3 := by
    rw [div_le_iff₀ (by linarith)]
    have q := mul_le_mul_of_nonneg_right (show 3-2*z ≤3 by linarith) (by positivity : 0≤2*z^3)
    nlinarith [mul_le_mul_of_nonneg_right hden (by positivity : 0≤12*z^3)]
  have tpos := (rp_bounds n).1.le
  change _ ∧ 0≤aliasBTerm n j-(2*z+4*z^2) ∧ aliasBTerm n j-(2*z+4*z^2)≤_
  rw [id]
  refine ⟨a.trans ?_,div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _),rem.trans ?_⟩
  · dsimp [z,offset]
    nlinarith [mul_le_mul_of_nonneg_right v2 (sq_nonneg (rp 2 n)),mul_nonneg (sq_nonneg (rp 2 n)) vp]
  · dsimp [z,offset]
    nlinarith [mul_le_mul_of_nonneg_right v3 (by positivity : 0≤(rp 2 n)^3),
      mul_nonneg (by positivity : 0≤(rp 2 n)^3) vp]

private theorem aliases (n : ℕ) :
    let t := rp 2 n
    let b := π^2/12
    let d := π^4/360
    aliasA n ≤ 3*t^2 ∧
    0 ≤ aliasB n-(b*t+d*t^2) ∧ aliasB n-(b*t+d*t^2) ≤ 3*t^3 := by
  dsimp only
  let t := rp 2 n
  let F := fun j => 2*offset n j+4*(offset n j)^2
  have pt (j : ℕ) : F j = t/2*rp 2 j+t^2/4*rp 4 j := by
    dsimp [F,t,offset,rp]
    field_simp
    ring
  have sum : HasSum F (π^2/12*t+π^4/360*t^2) := by
    have h := (rp_two_sum.mul_left (t/2)).add (rp_four_sum.mul_left (t^2/4))
    convert h using 1
    · funext j; exact pt j
    · ring
  have rem := (aliasB_summable n).hasSum.sub sum
  have ar : (∑' j, aliasATerm n j) ≤ (∑' j, t^2*rp 2 j) := (aliasA_summable n).tsum_le_tsum (fun j => (powers n j).1)
    (rp_two_sum.summable.mul_left (t^2))
  have er := rem.summable.tsum_le_tsum (fun j => (powers n j).2.2)
    (rp_two_sum.summable.mul_left (t^3))
  have low : 0≤(∑' j, (aliasBTerm n j - F j)) := tsum_nonneg (fun j => (powers n j).2.1)
  change (∑' j, (aliasBTerm n j-F j)) ≤ _ at er
  change 0 ≤ (∑' j, (aliasBTerm n j-F j)) at low
  rw [rem.tsum_eq] at er low
  rw [(rp_two_sum.mul_left (t^3)).tsum_eq] at er
  rw [(rp_two_sum.mul_left (t^2)).tsum_eq] at ar
  have pi2 : π^2/6 ≤3 := by nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2]
  exact ⟨ar.trans (by nlinarith [mul_le_mul_of_nonneg_left pi2 (sq_nonneg t)]),low,
    er.trans (by nlinarith [mul_le_mul_of_nonneg_left pi2 (show 0≤t^3 by exact pow_nonneg (rp_bounds n).1.le 3)])⟩

/-- The actual interpolation coefficient has the stated uniform O(N⁻⁴)
remainder after its second-order correction, including all small grids. -/
theorem uniform_remainder (n : ℕ) :
    let x := (n:ℝ)+1
    |x^2*(weight (1/2) n-weight 2 n) - (π^2/40-π^4/(1600*x^2))| ≤ 400/x^4 := by
  let t := rp 2 n
  let b := π^2/12
  let d := π^4/360
  let g := d-7/10*b^2
  let a := aliasA n/t^2
  let e := (aliasB n-(b*t+d*t^2))/t^3
  let W := b+t*(d+t*e)
  let X := t*a+W/5
  let V := t*a+W/2
  let R := 2*a+7/10*(d+t*e)+X*V
  have tp : 0<t := (rp_bounds n).1
  have tu : t≤1 := (rp_bounds n).2
  have bound := aliases n
  have ha : 0≤a ∧ a≤3 := ⟨div_nonneg (aliasA_nonneg n) (sq_nonneg _), (div_le_iff₀ (by positivity)).mpr bound.1⟩
  have he : 0≤e ∧ e≤3 := ⟨div_nonneg bound.2.1 (by positivity), (div_le_iff₀ (by positivity)).mpr bound.2.2⟩
  have p2 : π^2≤16 := by nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2]
  have p4 : π^4≤256 := by nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_four.le 4]
  have bb : 0≤b ∧ b≤2 := ⟨by dsimp [b];positivity,by dsimp [b];linarith⟩
  have dd : 0≤d ∧ d≤1 := ⟨by dsimp [d];positivity,by dsimp [d];linarith⟩
  have gg : |g|≤4 := by
    rw [abs_le];dsimp [g]
    have h := pow_le_pow_left₀ bb.1 bb.2 2
    constructor <;> nlinarith [sq_nonneg b,dd.1,dd.2]
  have de : 0≤d+t*e ∧ d+t*e≤4 := ⟨by positivity [dd.1,he.1],
    by linarith [dd.2, mul_le_mul tu he.2 he.1 (by norm_num : (0:ℝ)≤1)]⟩
  have w : 0≤W ∧ W≤6 := ⟨by unfold W; positivity [bb.1,de.1],
    by dsimp only [W]; linarith [bb.2,mul_le_mul tu de.2 de.1 (by norm_num : (0:ℝ)≤1)]⟩
  have x : 0≤X ∧ X≤5 := ⟨by unfold X; positivity [ha.1,w.1],by dsimp [X];linarith [w.2,mul_le_mul tu ha.2 ha.1 (by norm_num : (0:ℝ)≤1)]⟩
  have v : 0≤V ∧ V≤6 := ⟨by unfold V; positivity [ha.1,w.1],by dsimp [V];linarith [w.2,mul_le_mul tu ha.2 ha.1 (by norm_num : (0:ℝ)≤1)]⟩
  have r : 0≤R ∧ R≤40 := ⟨by unfold R; positivity [ha.1,de.1,x.1,v.1],by dsimp only [R];linarith [ha.2,de.2,mul_le_mul x.2 v.2 v.1 (by norm_num : (0:ℝ)≤5)]⟩
  let D := (1+t*X)*(1+t*V)
  have hd : 1≤D := one_le_mul_of_one_le_of_one_le (by linarith [mul_nonneg tp.le x.1]) (by linarith [mul_nonneg tp.le v.1])
  let E := e-g*(7/10*b)-(b+t*g)*R
  have eb : |E|≤400 := by
    have bg : |b+t*g|≤6 := calc
      _ ≤ |b|+|t| * |g| := by simpa only [abs_mul] using abs_add_le b (t*g)
      _ ≤ 6 := by rw [abs_of_nonneg bb.1,abs_of_nonneg tp.le]; linarith [bb.2,mul_le_mul tu gg (abs_nonneg g) (by norm_num : (0:ℝ)≤1)]
    have z := abs_sub (e-g*(7/10*b)) ((b+t*g)*R)
    have y := abs_sub e (g*(7/10*b))
    simp only [abs_mul,abs_of_nonneg he.1,abs_of_nonneg r.1,abs_of_nonneg bb.1,abs_of_nonneg (by norm_num : 0 ≤ (7/10:ℝ))] at z y
    dsimp only [E]
    linarith [mul_le_mul bg r.2 r.1 (by norm_num : (0:ℝ)≤6),
      mul_le_mul gg (show 7/10*b≤2 by linarith [bb.2]) (by positivity [bb.1]) (by norm_num : (0:ℝ)≤4),he.2]
  have ai : aliasA n=t^2*a := by dsimp [a];field_simp [tp.ne']
  have bi : aliasB n=t*W := by dsimp [W,e];field_simp [tp.ne'];ring
  have id : 3/10*W/D-3/10*(b+g*t) = 3/10*t^2*E/D := by
    field_simp [show D≠0 by linarith]
    dsimp only [D,E,R,X,V,W,g];ring
  have lip : |3/10*t^2*E/D|≤400*t^2 := by
    rw [abs_div,abs_mul,abs_of_nonneg (show 0≤3/10*t^2 by positivity),abs_of_nonneg (by linarith : 0≤D)]
    calc _ ≤ 3/10*t^2*400 := (div_le_self (by positivity) hd).trans (mul_le_mul_of_nonneg_left eb (by positivity))
         _ ≤ _ := by nlinarith [sq_nonneg t]
  have xt : ((n:ℝ)+1)^2*t=1 := by dsimp [t,rp];field_simp
  have bd : 3/10*(b+g*t)=π^2/40-π^4/(1600*((n:ℝ)+1)^2) := by dsimp [g,b,d,t,rp];field_simp;ring
  dsimp only
  rw [weight_difference,ai,bi,←bd]
  have eq : ((n:ℝ)+1)^2*(3/10*(t*W)/((1+t^2*a+t*W/5)*(1+t^2*a+t*W/2))) = 3/10*W/D := by
    dsimp [D,X,V]
    rw [show 1+t^2*a+t*W/5=1+t*(t*a+W/5) by ring,show 1+t^2*a+t*W/2=1+t*(t*a+W/2) by ring]
    linear_combination ((3/10)*W/((1+t*(t*a+W/5))*(1+t*(t*a+W/2))))*xt
  rw [eq,id]
  exact lip.trans_eq (by dsimp [t,rp];field_simp)

end CircleCoefficientRemainder
