import GaugeFieldConstruction.CloverSymmetrySlots
/-!
# Ten generators for the Weyl part

An elementary Lie-algebra calculation; expand every table identity on actual `ff`,
using the already proved curvature alternating and Bose identities. Indices are spatial
where $E_i=F_{i3}, B=(F_{12},-F_{02},F_{01})$. The plus/minus families pay products
$(E+B)_i(E+B)_j$, $(E-B)_i(E-B)_j$, respectively, where on diagonals
00 and 11 one subtracts the 22 product. These don't have to be *independent* in any
particular system to prove this symmetry obstruction.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 6000
set_option maxRecDepth 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.CloverSymmetry
open Calibration Calibration.RawBank Floor Cauchy Row Phys Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles Flux One
attribute [local instance] Stage.iA Stage.iG Stage.iX
def dPlus00 : UV four :=
    - ff 0 1 0 1 - 2 • ff 0 1 2 3 + ff 0 3 0 3 + 2 • ff 0 3 1 2 + ff 1 2 1 2 - ff 2 3 2 3
def dPlus11 : UV four :=
    - ff 0 1 0 1 - 2 • ff 0 1 2 3 + ff 0 2 0 2 - 2 • ff 0 2 1 3 + ff 1 3 1 3 - ff 2 3 2 3
def dPlus01 : UV four :=
    - ff 0 2 0 3 - ff 0 2 1 2 + ff 0 3 1 3 + ff 1 2 1 3
def dPlus02 : UV four :=
    ff 0 1 0 3 + ff 0 1 1 2 + ff 0 3 2 3 + ff 1 2 2 3
def dPlus12 : UV four :=
    - ff 0 1 0 2 + ff 0 1 1 3 - ff 0 2 2 3 + ff 1 3 2 3
def dMinus00 : UV four :=
    - ff 0 1 0 1 + 2 • ff 0 1 2 3 + ff 0 3 0 3 - 2 • ff 0 3 1 2 + ff 1 2 1 2 - ff 2 3 2 3
def dMinus11 : UV four :=
    - ff 0 1 0 1 + 2 • ff 0 1 2 3 + ff 0 2 0 2 + 2 • ff 0 2 1 3 + ff 1 3 1 3 - ff 2 3 2 3
def dMinus01 : UV four :=
    ff 0 2 0 3 - ff 0 2 1 2 + ff 0 3 1 3 - ff 1 2 1 3
def dMinus02 : UV four :=
    - ff 0 1 0 3 + ff 0 1 1 2 + ff 0 3 2 3 - ff 1 2 2 3
def dMinus12 : UV four :=
    - ff 0 1 0 2 - ff 0 1 1 3 + ff 0 2 2 3 + ff 1 3 2 3

inductive WeylInk : Type
 | dPlus00 | dPlus11 | dPlus01 | dPlus02 | dPlus12 | dMinus00 | dMinus11 | dMinus01 | dMinus02 | dMinus12

def WeylInk.slots : WeylInk → UV four
 | .dPlus00 => CloverSymmetry.dPlus00
 | .dPlus11 => CloverSymmetry.dPlus11
 | .dPlus01 => CloverSymmetry.dPlus01
 | .dPlus02 => CloverSymmetry.dPlus02
 | .dPlus12 => CloverSymmetry.dPlus12
 | .dMinus00 => CloverSymmetry.dMinus00
 | .dMinus11 => CloverSymmetry.dMinus11
 | .dMinus01 => CloverSymmetry.dMinus01
 | .dMinus02 => CloverSymmetry.dMinus02
 | .dMinus12 => CloverSymmetry.dMinus12

def orbitSpin2 : Submodule ℂ (UV four) := Submodule.span ℂ (range WeylInk.slots)
lemma WeylInk.belong (v : WeylInk) : v.slots ∈ orbitSpin2 := Submodule.subset_span ⟨v,rfl⟩
lemma k10L (c d) : ff 1 0 c d = -ff 0 1 c d := leftSkew ..
lemma k10R (c d) : ff c d 1 0 = -ff c d 0 1 := rightSkew ..
lemma k20L (c d) : ff 2 0 c d = -ff 0 2 c d := leftSkew ..
lemma k20R (c d) : ff c d 2 0 = -ff c d 0 2 := rightSkew ..
lemma k30L (c d) : ff 3 0 c d = -ff 0 3 c d := leftSkew ..
lemma k30R (c d) : ff c d 3 0 = -ff c d 0 3 := rightSkew ..
lemma k21L (c d) : ff 2 1 c d = -ff 1 2 c d := leftSkew ..
lemma k21R (c d) : ff c d 2 1 = -ff c d 1 2 := rightSkew ..
lemma k31L (c d) : ff 3 1 c d = -ff 1 3 c d := leftSkew ..
lemma k31R (c d) : ff c d 3 1 = -ff c d 1 3 := rightSkew ..
lemma k32L (c d) : ff 3 2 c d = -ff 2 3 c d := leftSkew ..
lemma k32R (c d) : ff c d 3 2 = -ff c d 2 3 := rightSkew ..
lemma ord0201 : ff 0 2 0 1 = ff 0 1 0 2 := pairExchange ..
lemma ord0301 : ff 0 3 0 1 = ff 0 1 0 3 := pairExchange ..
lemma ord1201 : ff 1 2 0 1 = ff 0 1 1 2 := pairExchange ..
lemma ord1301 : ff 1 3 0 1 = ff 0 1 1 3 := pairExchange ..
lemma ord2301 : ff 2 3 0 1 = ff 0 1 2 3 := pairExchange ..
lemma ord0302 : ff 0 3 0 2 = ff 0 2 0 3 := pairExchange ..
lemma ord1202 : ff 1 2 0 2 = ff 0 2 1 2 := pairExchange ..
lemma ord1302 : ff 1 3 0 2 = ff 0 2 1 3 := pairExchange ..
lemma ord2302 : ff 2 3 0 2 = ff 0 2 2 3 := pairExchange ..
lemma ord1203 : ff 1 2 0 3 = ff 0 3 1 2 := pairExchange ..
lemma ord1303 : ff 1 3 0 3 = ff 0 3 1 3 := pairExchange ..
lemma ord2303 : ff 2 3 0 3 = ff 0 3 2 3 := pairExchange ..
lemma ord1312 : ff 1 3 1 2 = ff 1 2 1 3 := pairExchange ..
lemma ord2312 : ff 2 3 1 2 = ff 1 2 2 3 := pairExchange ..
lemma ord2313 : ff 2 3 1 3 = ff 1 3 2 3 := pairExchange ..

lemma rDiag (B : Rotors) (a : Axis) : B.val a a = 0 := by
  have h:= skewP B a a; linarith

/- skew/lex/Bose normal form of `ff` entries -/
macro "clovers_norm" : tactic => `(tactic|
   simp (config:={failIfUnchanged:=false}) only [k10L, k10R, k20L, k20R, k30L, k30R, k21L, k21R, k31L, k31R, k32L, k32R, ord0201, ord0301, ord1201, ord1301, ord2301, ord0302, ord1202, ord1302, ord2302, ord1203, ord1303, ord2303, ord1312, ord2312, ord2313,
     leftDiag, rightDiag, map_zero, neg_smul, smul_neg, zero_smul, smul_zero,
     add_zero, zero_add, sub_zero, zero_sub, neg_neg, neg_zero])
macro "clovers_charge" r:ident : tactic => `(tactic|(
   simp only [map_sub, map_add, map_neg, map_nsmul, ffCharge, Fin.sum_univ_succ,
     Fin.sum_univ_zero, two_smul]
   -- fin normalizations to digits
   simp only [rDiag, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show ((2:Fin 3).succ) = 3 from by decide]
   simp (config:={failIfUnchanged:=false}) only [skewP $r 1 0, skewP $r 2 0, skewP $r 3 0, skewP $r 2 1, skewP $r 3 1, skewP $r 3 2,
     Complex.ofReal_neg, Complex.ofReal_zero, add_smul, neg_smul, smul_neg,
     sub_smul, smul_add, smul_sub,
     smul_zero, zero_smul, two_mul, neg_mul, show (4:ℂ)= 2+2 from by norm_num,
     add_mul, mul_add]
   clovers_norm
   abel))
lemma charge_dPlus00 (B : Rotors) :
    enlarged All four B dPlus00 =
      (-2*(B.val 0 1:ℂ)-2*(B.val 2 3:ℂ)) • dPlus01 +
      (-4*(B.val 0 2:ℂ)+4*(B.val 1 3:ℂ)) • dPlus02 +
      (-2*(B.val 0 3:ℂ)-2*(B.val 1 2:ℂ)) • dPlus12 := by
  unfold dPlus00 dPlus01 dPlus02 dPlus12
  clovers_charge B
lemma charge_dPlus11 (B : Rotors) :
    enlarged All four B dPlus11 =
      (2*(B.val 0 1:ℂ)+2*(B.val 2 3:ℂ)) • dPlus01 +
      (-2*(B.val 0 2:ℂ)+2*(B.val 1 3:ℂ)) • dPlus02 +
      (-4*(B.val 0 3:ℂ)-4*(B.val 1 2:ℂ)) • dPlus12 := by
  unfold dPlus11 dPlus01 dPlus02 dPlus12
  clovers_charge B
lemma charge_dPlus01 (B : Rotors) :
    enlarged All four B dPlus01 =
      ((B.val 0 1:ℂ)+(B.val 2 3:ℂ)) • dPlus00 +
      (-(B.val 0 1:ℂ)-(B.val 2 3:ℂ)) • dPlus11 +
      (-(B.val 0 3:ℂ)-(B.val 1 2:ℂ)) • dPlus02 +
      (-(B.val 0 2:ℂ)+(B.val 1 3:ℂ)) • dPlus12 := by
  unfold dPlus01 dPlus00 dPlus11 dPlus02 dPlus12
  clovers_charge B
lemma charge_dPlus02 (B : Rotors) :
    enlarged All four B dPlus02 =
      ((B.val 0 2:ℂ)-(B.val 1 3:ℂ)) • dPlus00 +
      ((B.val 0 3:ℂ)+(B.val 1 2:ℂ)) • dPlus01 +
      (-(B.val 0 1:ℂ)-(B.val 2 3:ℂ)) • dPlus12 := by
  unfold dPlus02 dPlus00 dPlus01 dPlus12
  clovers_charge B
lemma charge_dPlus12 (B : Rotors) :
    enlarged All four B dPlus12 =
      ((B.val 0 3:ℂ)+(B.val 1 2:ℂ)) • dPlus11 +
      ((B.val 0 2:ℂ)-(B.val 1 3:ℂ)) • dPlus01 +
      ((B.val 0 1:ℂ)+(B.val 2 3:ℂ)) • dPlus02 := by
  unfold dPlus12 dPlus11 dPlus01 dPlus02
  clovers_charge B
lemma charge_dMinus00 (B : Rotors) :
    enlarged All four B dMinus00 =
      (-2*(B.val 0 1:ℂ)+2*(B.val 2 3:ℂ)) • dMinus01 +
      (-4*(B.val 0 2:ℂ)-4*(B.val 1 3:ℂ)) • dMinus02 +
      (2*(B.val 0 3:ℂ)-2*(B.val 1 2:ℂ)) • dMinus12 := by
  unfold dMinus00 dMinus01 dMinus02 dMinus12
  clovers_charge B
lemma charge_dMinus11 (B : Rotors) :
    enlarged All four B dMinus11 =
      (2*(B.val 0 1:ℂ)-2*(B.val 2 3:ℂ)) • dMinus01 +
      (-2*(B.val 0 2:ℂ)-2*(B.val 1 3:ℂ)) • dMinus02 +
      (4*(B.val 0 3:ℂ)-4*(B.val 1 2:ℂ)) • dMinus12 := by
  unfold dMinus11 dMinus01 dMinus02 dMinus12
  clovers_charge B
lemma charge_dMinus01 (B : Rotors) :
    enlarged All four B dMinus01 =
      ((B.val 0 1:ℂ)-(B.val 2 3:ℂ)) • dMinus00 +
      (-(B.val 0 1:ℂ)+(B.val 2 3:ℂ)) • dMinus11 +
      ((B.val 0 3:ℂ)-(B.val 1 2:ℂ)) • dMinus02 +
      (-(B.val 0 2:ℂ)-(B.val 1 3:ℂ)) • dMinus12 := by
  unfold dMinus01 dMinus00 dMinus11 dMinus02 dMinus12
  clovers_charge B
lemma charge_dMinus02 (B : Rotors) :
    enlarged All four B dMinus02 =
      ((B.val 0 2:ℂ)+(B.val 1 3:ℂ)) • dMinus00 +
      (-(B.val 0 3:ℂ)+(B.val 1 2:ℂ)) • dMinus01 +
      (-(B.val 0 1:ℂ)+(B.val 2 3:ℂ)) • dMinus12 := by
  unfold dMinus02 dMinus00 dMinus01 dMinus12
  clovers_charge B
lemma charge_dMinus12 (B : Rotors) :
    enlarged All four B dMinus12 =
      (-(B.val 0 3:ℂ)+(B.val 1 2:ℂ)) • dMinus11 +
      ((B.val 0 2:ℂ)+(B.val 1 3:ℂ)) • dMinus01 +
      ((B.val 0 1:ℂ)-(B.val 2 3:ℂ)) • dMinus02 := by
  unfold dMinus12 dMinus11 dMinus01 dMinus02
  clovers_charge B

theorem keepRotation (s : SO) {v : UV four} (x : v ∈ orbitSpin2):
    ledger All four s v ∈ orbitSpin2 := by
  apply rotationMem _ _ s _ x
  intro B x hx
  suffices h : orbitSpin2 ≤ orbitSpin2.comap (enlarged All four B) from h hx
  apply Submodule.span_le.mpr
  rintro z ⟨w,rfl⟩
  have m_dPlus00 : dPlus00 ∈ orbitSpin2 := WeylInk.dPlus00.belong
  have m_dPlus11 : dPlus11 ∈ orbitSpin2 := WeylInk.dPlus11.belong
  have m_dPlus01 : dPlus01 ∈ orbitSpin2 := WeylInk.dPlus01.belong
  have m_dPlus02 : dPlus02 ∈ orbitSpin2 := WeylInk.dPlus02.belong
  have m_dPlus12 : dPlus12 ∈ orbitSpin2 := WeylInk.dPlus12.belong
  have m_dMinus00 : dMinus00 ∈ orbitSpin2 := WeylInk.dMinus00.belong
  have m_dMinus11 : dMinus11 ∈ orbitSpin2 := WeylInk.dMinus11.belong
  have m_dMinus01 : dMinus01 ∈ orbitSpin2 := WeylInk.dMinus01.belong
  have m_dMinus02 : dMinus02 ∈ orbitSpin2 := WeylInk.dMinus02.belong
  have m_dMinus12 : dMinus12 ∈ orbitSpin2 := WeylInk.dMinus12.belong
  cases w
  · change enlarged All four B dPlus00 ∈ orbitSpin2; rw [charge_dPlus00]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dPlus11 ∈ orbitSpin2; rw [charge_dPlus11]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dPlus01 ∈ orbitSpin2; rw [charge_dPlus01]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dPlus02 ∈ orbitSpin2; rw [charge_dPlus02]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dPlus12 ∈ orbitSpin2; rw [charge_dPlus12]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dMinus00 ∈ orbitSpin2; rw [charge_dMinus00]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dMinus11 ∈ orbitSpin2; rw [charge_dMinus11]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dMinus01 ∈ orbitSpin2; rw [charge_dMinus01]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dMinus02 ∈ orbitSpin2; rw [charge_dMinus02]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
  · change enlarged All four B dMinus12 ∈ orbitSpin2; rw [charge_dMinus12]; repeat' first | assumption | apply orbitSpin2.zero_mem | apply orbitSpin2.add_mem | apply orbitSpin2.smul_mem
#print axioms keepRotation
end YM.GaugeFieldConstruction.Stage.CloverSymmetry
end
