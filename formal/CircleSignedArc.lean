module

public import CircleSignedAngular
import all CircleSignedAngular
import all CircleMajorityFold
import all CircleAngularGeometry
import all CircleEscape
import Mathlib.Tactic

/-! The strict active grid arc of an odd polygon, including exact gate ties. -/
@[expose] public section
noncomputable section
namespace CircleSignedArc
open Real CircleSignedAngular CircleMajorityFold CircleAngularGeometry CircleEscape Finset

private theorem points_arc (a h : ℝ) (l : ℕ) :
    sin (h/2) • (∑ i ∈ Finset.range l, point (a+h*(i:ℝ))) =
      sin ((l:ℝ)*h/2) • point (a+((l:ℝ)-1)*h/2) := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,smul_add,ih,Nat.cast_succ]
    let t := h/2
    let k := (n:ℝ)*t
    let v := a+k
    have e1 : a+((n:ℝ)-1)*h/2=v-t := by dsimp [v,k,t];ring
    have e2 : a+h*(n:ℝ)=v+k := by dsimp [v,k,t];ring
    have e3 : ((n:ℝ)+1)*h/2=k+t := by dsimp [k,t];ring
    have e4 : a+((n:ℝ)+1-1)*h/2=v := by dsimp [v,k,t];ring
    rw [e1,e2,e3,e4,show (n:ℝ)*h/2=k by dsimp [k,t];ring]
    change sin k • point (v-t)+sin t • point (v+k)=sin (k+t) • point v
    apply Complex.ext <;> simp only [point,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
      smul_eq_mul,cos_sub,sin_sub,cos_add,sin_add] <;> ring

private theorem shift (p : ℕ→ℂ) (N : ℕ) (period : ∀ i,p (i+N)=p i) (j : ℕ) :
    ∑ i ∈ Finset.range N, p (j+i) =∑ i ∈ Finset.range N, p i := by
  apply Complex.ext
  · simp only [Complex.re_sum]
    exact CircleAngularGeometry.shift_sum (fun i => (p i).re) _ (fun i => congrArg Complex.re (period i)) _
  · simp only [Complex.im_sum]
    exact CircleAngularGeometry.shift_sum (fun i => (p i).im) _ (fun i => congrArg Complex.im (period i)) _

/-- The actual strict-gate average is exactly the constant-length vector to
the midpoint of the active arc. The endpoint convention is included. -/
theorem active_arc {N : ℕ} (hn : 3≤N) (ho : Odd N) {w : ℂ} (hw : w≠0) :
    ∃ ψ : ℝ, |ψ-w.arg|≤halfCell N ∧ gridGate N w=amplitude N • point ψ := by
  obtain ⟨k,hk⟩ := ho
  have np : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have kn : (N:ℝ)=2*(k:ℝ)+1 := by exact_mod_cast hk
  have wp := norm_pos_iff.mpr hw
  let h := 2*π/N
  let q := halfCell N
  have hp : 0<h := by dsimp [h];positivity
  have hnπ : h*(N:ℝ)=2*π := by dsimp [h];field_simp
  have h4 : h=4*q := by dsimp [h,q,halfCell];ring
  have kp : h*(k:ℝ)=π-h/2 := by rw [kn] at hnπ; linarith
  let a := w.arg+2*π-π/2
  let j : ℕ := ⌊a/h⌋₊+1
  have ap : 0≤a := by dsimp [a];linarith [Complex.neg_pi_lt_arg w,pi_pos]
  have jlo : a<h*(j:ℝ) := by
    have v := (div_lt_iff₀ hp).mp (Nat.lt_floor_add_one (a/h))
    dsimp [j];push_cast;linarith
  have jup : h*(j:ℝ)≤a+h := by
    have v := (le_div_iff₀ hp).mp (Nat.floor_le (div_nonneg ap hp.le))
    dsimp [j];push_cast;linarith
  let l := if h*(j:ℝ)<a+h/2 then k+1 else k
  let t (i : ℕ) := h*(j:ℝ)+h*(i:ℝ)
  let mid := h*(j:ℝ)+((l:ℝ)-1)*h/2
  have lN : l≤N := by dsimp [l];split <;> omega
  have active (i : ℕ) (hi : i<l) : gate w (point (t i))=1 := by
    have lo : -(π/2)<t i-w.arg-2*π := by
      dsimp [t,a] at *; nlinarith only [jlo,mul_nonneg hp.le (Nat.cast_nonneg i)]
    have hi' : t i-w.arg-2*π<π/2 := by
      dsimp only [l] at hi
      split at hi
      · have qn : (i:ℝ)≤k := by exact_mod_cast (show i≤k by omega)
        dsimp only [t,a] at *
        linarith only [mul_le_mul_of_nonneg_left qn hp.le,kp,‹h*(j:ℝ)<_›]
      · have qn : (i:ℝ)+1≤k := by exact_mod_cast hi
        dsimp only [t,a] at *
        nlinarith only [mul_le_mul_of_nonneg_left qn hp.le,kp,jup,hp]
    have ca := cos_pos_of_mem_Ioo (show t i-w.arg-2*π∈Set.Ioo (-(π/2)) (π/2) from ⟨lo,hi'⟩)
    rw [cos_sub_two_pi] at ca
    exact ite_eq_left (by rw [projection];exact mul_pos wp ca)
  have inactive (i : ℕ) (li : l ≤ i) (iN : i<N) : gate w (point (t i))=0 := by
    have lo : π/2≤t i-w.arg-2*π := by
      dsimp only [l] at li
      split at li
      · have qn : (k:ℝ)+1 ≤ i := by exact_mod_cast li
        dsimp only [t,a] at *
        nlinarith only [mul_le_mul_of_nonneg_left qn hp.le,kp,jlo,hp]
      · have qn : (k:ℝ) ≤ i := by exact_mod_cast li
        dsimp only [t,a] at *
        linarith only [mul_le_mul_of_nonneg_left qn hp.le,kp,‹¬h*(j:ℝ)<_›]
    have hi : t i-w.arg-2*π≤3*π/2 := by
      have qn : (i:ℝ)+1≤N := by exact_mod_cast iN
      dsimp only [t,a] at *
      nlinarith only [mul_le_mul_of_nonneg_left qn hp.le,jup,hnπ]
    have ca := cos_nonpos_of_pi_div_two_le_of_le lo (by linarith only [hi])
    rw [cos_sub_two_pi] at ca
    exact ite_eq_right (not_lt.mpr (by rw [projection];exact mul_nonpos_of_nonneg_of_nonpos wp.le ca))
  let f (u : ℂ) := gate w u • u
  have cyc (i : ℕ) : point (h*((i+N:ℕ):ℝ))=point (h*(i:ℝ)) := by
    push_cast;rw [mul_add,hnπ,CircleAngularGeometry.point_period]
  have sum_eq : ∑ i : Fin N, f (gridPoint N i)=∑ i ∈ Finset.range l, point (t i) := by
    change (∑ i : Fin N, f (point (h*(i.val:ℝ))))=_
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (point (h*(i:ℝ)))) N,
      ←shift (fun i : ℕ => f (point (h*(i:ℝ)))) N (fun i => congrArg f (cyc i)) j]
    simp only [Nat.cast_add,mul_add]
    calc
      _=∑ i ∈ Finset.range l, f (point (t i)) := by
        symm
        apply Finset.sum_subset (Finset.range_subset_range.mpr lN)
        intro i hi il;change gate w (point (t i)) • point (t i)=0;rw [inactive i (by simpa using il) (Finset.mem_range.mp hi),zero_smul]
      _=_ := by apply Finset.sum_congr rfl;intro i hi;change gate w (point (t i)) • point (t i)=point (t i);rw [active i (Finset.mem_range.mp hi),one_smul]
  have angle : |(mid-2*π)-w.arg|≤q := by
    apply abs_le.mpr
    dsimp only [mid,l]
    split
    · rename_i hi; push_cast; dsimp only [a] at jlo jup hi
      constructor <;> nlinarith only [kp,jlo,jup,h4,hp,hi]
    · rename_i hi; dsimp only [a] at jlo jup hi
      constructor <;> nlinarith only [kp,jlo,jup,h4,hp,hi]
  have num : sin ((l:ℝ)*h/2)=cos q := by
    dsimp only [l];split <;> push_cast
    · rw [show ((k:ℝ)+1)*h/2=q+π/2 by linarith only [kp,h4],sin_add_pi_div_two]
    · rw [show (k:ℝ)*h/2=π/2-q by linarith only [kp,h4],sin_pi_div_two_sub]
  have dp := (CircleSignedAngular.half_range hn).1
  have qsmall : q<π/2 := by
    dsimp [q,halfCell]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (show 3≤(N:ℝ) by exact_mod_cast hn) pi_pos.le,pi_pos]
  change 0<q at dp
  have sq : 0<sin q := sin_pos_of_pos_of_lt_pi dp (by linarith [pi_pos])
  have cq := cos_pos_of_mem_Ioo (show q∈Set.Ioo (-(π/2)) (π/2) from ⟨by linarith,qsmall⟩)
  have den : sin (h/2)=2*sin q*cos q := by rw [show h/2=2*q by linarith,sin_two_mul]
  have coeff : (1/(N:ℝ))*(sin ((l:ℝ)*h/2)/sin (h/2))=amplitude N := by
    rw [num,den];change _=1/(2*N*sin q);field_simp
  obtain ⟨v,eqv⟩ : ∃ v : ℂ, v=∑ i ∈ Finset.range l, point (t i) := ⟨_,rfl⟩
  have geom := points_arc (h*(j:ℝ)) h l
  change sin (h/2) • (∑ i ∈ Finset.range l, point (t i))=sin ((l:ℝ)*h/2) • point mid at geom
  have vec : v=(sin ((l:ℝ)*h/2)/sin (h/2)) • point mid := by
    rw [←eqv] at geom
    have H := congrArg (fun z : ℂ => (sin (h/2))⁻¹ • z) geom
    simp only [smul_smul] at H
    rw [inv_mul_cancel₀ (by rw [den];positivity),one_smul] at H
    simpa only [div_eq_inv_mul] using H
  refine ⟨mid-2*π,angle,?_⟩
  have periodic : point (mid-2*π)=point mid := by simp [point]
  rw [periodic,gridGate,←coeff]
  change (1/(N:ℝ)) • (∑ i, f (gridPoint N i))=_
  rw [sum_eq,←eqv,vec,smul_smul]

end CircleSignedArc
