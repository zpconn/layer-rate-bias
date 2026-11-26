module

public import CircleFiniteConfidence
public import CircleKernelGD

/-! Clock and sufficient width of the finite-confidence early-stopping theorem. -/
@[expose] public section
noncomputable section
namespace CircleEarlyWidth
open Real CircleFiniteConfidence
def R (δ : ℝ) := sqrt (12/δ)
def cap (N : ℕ) [NeZero N] (η δ ε : ℝ) := ⌈log (2*R δ*(N:ℝ)^2/ε)/(η*CircleKernelGD.gamma N)⌉₊
def D (N : ℕ) [NeZero N] (η δ ε : ℝ) := 2*η*cap N η δ ε*R δ
def A (N : ℕ) [NeZero N] (η δ ε : ℝ) := 2*D N η δ ε
def width (n : ℕ) (η δ ε : ℝ) :=
  let N := n+1
  let b := CircleSpectrum.weight 1 n
  let a := A N η δ ε
  let d := D N η δ ε
  let h := gridScale N δ
  let v := signedScale N b δ
  max a (max (sqrt (36/δ)) (max (10*((N:ℝ)+1)/(δ*a))
    (max (η*cap N η δ ε*(h+36*a)/log 2)
      (2*(N:ℝ)^2/ε*(2*b*R δ*(h+36*a)/CircleKernelGD.gamma N+d*(v+36*(1+b)*a))))))
end CircleEarlyWidth
