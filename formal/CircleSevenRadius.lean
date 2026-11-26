module
public import CircleSevenDesign
public import CircleFirstCosineReference
import all CircleFirstCosineReference
import all CircleSevenDesign
import all CircleSevenSpectrum
import all CircleSevenIntervals
import all CircleTeacherRKHS
import all CircleSpectrum
import Mathlib.Tactic

/-! Exact seven-point Gram solution and rational enclosures for the worked
teacher-radius example in circle/design.md. -/
@[expose] public section
noncomputable section
namespace CircleSevenRadius
open Real CircleSevenSpectrum CircleSevenIntervals CircleGridSpectrum CircleTeacherRKHS
open CircleSpectrum CircleFirstCosineReference
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

def labels (j : Fin 7) := 1+cosine j
def coeff (j : Fin 7) := (1/mode 0 0 + cosine j /mode 0 1)/7
def radiusSq := π^2/2+4
def center := (2/π^2)/mode 0 0
def powerSq := (2/π^2)*(1-center)
def slack := radiusSq-1/mode 0 0-1/(2*mode 0 1)

private abbrev k := Box.nat
private def covBox := (k 2).div CircleSevenDesign.piBox.sq
private def rBox : Box radiusSq := (CircleSevenDesign.piBox.sq.div (k 2)).add (k 4)
private def centerBox : Box center := covBox.div CircleSevenDesign.c0
private def powerBox : Box (sqrt powerSq) :=
  (covBox.mul (CircleSevenDesign.one.sub centerBox)).sqrt 0.00339530430 0.00339530439
private def slackBox : Box slack := ((rBox.sub (CircleSevenDesign.one.div CircleSevenDesign.c0)).sub
  (CircleSevenDesign.one.div ((k 2).mul CircleSevenDesign.c1))).narrow 0.0072770190 0.0072770194
theorem enclosures :
    0.999943108 ≤ center ∧ center ≤ 0.999943114 ∧
    0.00339530430 ≤ sqrt powerSq ∧ sqrt powerSq ≤ 0.00339530439 ∧
    0.0072770190 ≤ slack ∧ slack ≤ 0.0072770194 ∧
    0.0002896378 ≤ sqrt slack*sqrt powerSq ∧ sqrt slack*sqrt powerSq ≤ 0.0002896381 ∧
    0.0101489513 ≤ sqrt radiusSq*sqrt powerSq ∧ sqrt radiusSq*sqrt powerSq ≤ 0.0101489519 := by
  have c := centerBox.bounds 0.999943108 0.999943114
  have p := powerBox.bounds 0.00339530430 0.00339530439
  have s := slackBox.bounds 0.0072770190 0.0072770194
  have a := ((slackBox.sqrt 0.085305444 0.085305449).mul powerBox).bounds 0.0002896378 0.0002896381
  have b := ((rBox.sqrt 2.989113948 2.989113951).mul powerBox).bounds 0.0101489513 0.0101489519
  norm_num at c p s a b ⊢
  exact ⟨c.1,c.2,p.1,p.2,s.1,s.2,a.1,a.2,b.1,b.2⟩

private theorem value0 : mode 0 0 = c0+S 6 := by
  exact (mode_alias 0 (by norm_num) (by norm_num) (0:ZMod 7)).trans (CircleTeacherRKHS.alias_zero 6 (by decide) (by decide))
private theorem denominators : mode 0 0≠0 ∧ mode 0 1≠0 := by
  have p := CircleSevenDesign.c0.bounds 0.2 0.21
  have q := CircleSevenDesign.c1.bounds 0.12 0.13
  norm_num at p q
  constructor <;> linarith

/-- The coefficients solve the actual sampled covariance equations. -/
theorem gram_solution (i : Fin 7) : ∑ j,coeff j*sampledMatrix 0 j i=labels i := by
  let d := sampledMatrix (N:=7) 0
  have const := sampled_column (N:=7) 0 (by norm_num) (by norm_num) i
  rw [←mode_alias 0 (by norm_num) (by norm_num) (0:ZMod 7)] at const
  have hm := cosine_eigen (N:=7) 0 (by norm_num) (by norm_num) i
  have symm (j : Fin 7) : d i j=d j i := by
    rw [show d i j=inner ℝ (gridSection i) (gridSection j) from (grid_covariance i j).symm,
      show d j i=inner ℝ (gridSection j) (gridSection i) from (grid_covariance j i).symm,real_inner_comm]
  change (∑ j,d i j*cosine j)/7 = firstEigen 7 0*cosine i at hm
  change (∑ j,d j i)/7 = mode 0 0 at const
  have eig : firstEigen 7 0=mode 0 1 := by
    change aliasValue _ (1:ZMod 7)=mode 0 1
    simpa only [show (1 : ZMod 7).val=1 by decide] using (mode_alias 0 (by norm_num) (by norm_num) (1:ZMod 7)).symm
  rw [eig] at hm
  simp_rw [symm] at hm
  have e (j : Fin 7) : coeff j*d j i=(1/(7*mode 0 0))*(d j i) + (1/(7*mode 0 1))*(d j i*cosine j) := by unfold coeff;ring
  change (∑ j,coeff j*d j i)=1+cosine i
  simp_rw [e]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  rw [show (∑ j,d j i)=7*mode 0 0 by linarith,show (∑ j,d j i*cosine j)=7*(mode 0 1*cosine i) by linarith]
  field_simp [denominators.1,denominators.2]

theorem design_values : (∑ i, designWeight 6 i*labels i)=center ∧
    minVariance 6=powerSq ∧ radiusSq-(∑ i,coeff i*labels i)=slack := by
  have hs := cosine_sums (N:=7) (by decide)
  have v := value0
  constructor
  · unfold designWeight labels
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_add, Nat.cast_one, show (6:ℝ)+1=7 by norm_num]
    rw [←Finset.mul_sum,Finset.sum_add_distrib,hs.1]
    norm_num [covarianceWeight,center]
    rw [v,c0]
  constructor
  · unfold minVariance powerSq center
    change c0*S 6/(c0+S 6)=c0*(1-c0/mode 0 0)
    rw [←v]
    field_simp [denominators.1]
    rw [v];ring
  · have e (i : Fin 7) : coeff i*labels i = 1/(7*mode 0 0)+
        ((1/(7*mode 0 0)+1/(7*mode 0 1))*cosine i) + (1/(7*mode 0 1))*(cosine i)^2 := by
      unfold coeff labels; ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,hs.1,hs.2,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_zero,add_zero]
    unfold slack
    push_cast
    ring

/-- Every point of this numerical interval is achieved at the specified radius. -/
theorem sharp (s : ℝ) (hs : |s|≤1) :
    ∃ h : H, ‖h‖≤sqrt radiusSq ∧ (∀ i,inner ℝ h (gridSection i)=labels i) ∧
    (∫ u,inner ℝ h (sectionAt (2*π*u)) ∂CircleTangentDrift.angularLaw)=
      center+s*sqrt slack*sqrt powerSq := by
  have b := design_values
  have cap : 0≤radiusSq := by unfold radiusSq; positivity
  have feasible : (∑ i,coeff i*labels i) ≤ (sqrt radiusSq)^2 := by
    rw [sq_sqrt cap]; linarith [enclosures.2.2.2.2.1]
  have h := sharp_interval 6 (by decide) (by decide) coeff labels (sqrt radiusSq) s (sqrt_nonneg _) hs gram_solution feasible
  rwa [b.1,sq_sqrt cap,b.2.1,b.2.2] at h
end CircleSevenRadius
