module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Rational interval certificates for the seven-point design calculation. -/
@[expose] public section
noncomputable section
namespace CircleSevenIntervals
open Real

structure Box (x : ℝ) where
  lo : ℚ
  hi : ℚ
  lower : (lo:ℝ)≤x
  upper : x≤(hi:ℝ)

namespace Box
def constant (r : ℚ) : Box (r:ℝ) := ⟨r,r,le_rfl,le_rfl⟩
def add {x y} (u : Box x) (v : Box y) : Box (x+y) :=
  ⟨u.lo+v.lo,u.hi+v.hi,by simpa using add_le_add u.lower v.lower,by simpa using add_le_add u.upper v.upper⟩
def neg {x} (u : Box x) : Box (-x) :=
  ⟨-u.hi,-u.lo,by simpa using neg_le_neg u.upper,by simpa using neg_le_neg u.lower⟩
def sub {x y} (u : Box x) (v : Box y) : Box (x-y) := u.add v.neg

theorem mul_upper {x y l h a b : ℝ} (xl : l≤x) (xh : x≤h) (yl : a≤y) (yh : y≤b) :
    x*y≤max (max (l*a) (l*b)) (max (h*a) (h*b)) := by
  have one (c : ℝ) : c*y≤max (c*a) (c*b) := by
    rcases le_total 0 c with hc|hc
    · exact (mul_le_mul_of_nonneg_left yh hc).trans (le_max_right ..)
    · exact (mul_le_mul_of_nonpos_left yl hc).trans (le_max_left ..)
  rcases le_total 0 y with hy|hy
  · exact ((mul_le_mul_of_nonneg_right xh hy).trans (one h)).trans (le_max_right ..)
  · exact ((mul_le_mul_of_nonpos_right xl hy).trans (one l)).trans (le_max_left ..)

theorem mul_lower {x y l h a b : ℝ} (xl : l≤x) (xh : x≤h) (yl : a≤y) (yh : y≤b) :
    min (min (l*a) (l*b)) (min (h*a) (h*b))≤x*y := by
  have one (c : ℝ) : min (c*a) (c*b)≤c*y := by
    rcases le_total 0 c with hc|hc
    · exact (min_le_left ..).trans (mul_le_mul_of_nonneg_left yl hc)
    · exact (min_le_right ..).trans (mul_le_mul_of_nonpos_left yh hc)
  rcases le_total 0 y with hy|hy
  · exact ((min_le_left ..).trans (one l)).trans (mul_le_mul_of_nonneg_right xl hy)
  · exact ((min_le_right ..).trans (one h)).trans (mul_le_mul_of_nonpos_right xh hy)

def mul {x y} (u : Box x) (v : Box y) : Box (x*y) where
  lo := min (min (u.lo*v.lo) (u.lo*v.hi)) (min (u.hi*v.lo) (u.hi*v.hi))
  hi := max (max (u.lo*v.lo) (u.lo*v.hi)) (max (u.hi*v.lo) (u.hi*v.hi))
  upper := by simpa using mul_upper u.lower u.upper v.lower v.upper
  lower := by simpa only [Rat.cast_min,Rat.cast_mul] using mul_lower u.lower u.upper v.lower v.upper

def inv {x} (u : Box x) (h : 0<u.lo) : Box x⁻¹ where
  lo := u.hi⁻¹
  hi := u.lo⁻¹
  lower := by
    rw [Rat.cast_inv];apply inv_anti₀ _ u.upper
    exact (show (0:ℝ)<u.lo by exact_mod_cast h).trans_le u.lower
  upper := by
    rw [Rat.cast_inv];apply inv_anti₀ _ u.lower
    exact_mod_cast h
def div {x y} (u : Box x) (v : Box y) (h : 0<v.lo := by decide +kernel) : Box (x/y) := u.mul (v.inv h)
def transport {x y} (u : Box x) (e : y=x) : Box y :=
  ⟨u.lo,u.hi,e ▸ u.lower,e ▸ u.upper⟩
def sq {x} (u : Box x) : Box (x^2) := (u.mul u).transport (pow_two x)
def nat (n : ℕ) : Box (n:ℝ) := ⟨n,n,by norm_num,by norm_num⟩
def narrow {x} (u : Box x) (l h : ℚ) (hl : l≤u.lo := by decide +kernel) (hh : u.hi≤h := by decide +kernel) : Box x :=
  ⟨l,h,(show (l:ℝ)≤u.lo by exact_mod_cast hl).trans u.lower,u.upper.trans (by exact_mod_cast hh)⟩
def absolute {x} (u : Box x) : Box |x| where
  lo := max (-u.hi) u.lo
  hi := max (-u.lo) u.hi
  lower := by
    push_cast
    exact max_le ((neg_le_neg u.upper).trans (neg_le_abs _)) (u.lower.trans (le_abs_self _))
  upper := by
    push_cast
    rw [abs_le]
    constructor
    · exact (neg_le.mpr ((neg_le_neg u.lower).trans (le_max_left ..)))
    · exact u.upper.trans (le_max_right ..)
def greatest {x y} (u : Box x) (v : Box y) : Box (max x y) :=
  ⟨max u.lo v.lo,max u.hi v.hi,by simpa using max_le_max u.lower v.lower,by simpa using max_le_max u.upper v.upper⟩

def sqrt {x} (u : Box x) (l h : ℚ) (lp : 0≤l := by decide +kernel) (hp : 0≤h := by decide +kernel)
    (ll : l^2≤u.lo := by decide +kernel) (hh : u.hi≤h^2 := by decide +kernel) : Box (Real.sqrt x) where
  lo := l
  hi := h
  lower := by
    have lb : (l:ℝ)^2≤x := (show (l:ℝ)^2≤u.lo by exact_mod_cast ll).trans u.lower
    exact (le_sqrt (by exact_mod_cast lp) (by nlinarith only [lb,sq_nonneg (l:ℝ)])).mpr lb
  upper := (sqrt_le_iff.mpr ⟨by exact_mod_cast hp,u.upper.trans (by exact_mod_cast hh)⟩)

theorem bounds {x} (u : Box x) (l h : ℚ) (hl : l≤u.lo := by decide +kernel) (hh : u.hi≤h := by decide +kernel) :
    (l:ℝ)≤x ∧ x≤(h:ℝ) :=
  ⟨(show (l:ℝ)≤u.lo by exact_mod_cast hl).trans u.lower,u.upper.trans (by exact_mod_cast hh)⟩
end Box
end CircleSevenIntervals
