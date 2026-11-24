import GaugeFieldConstruction.StencilRaise
/-!
# Staying positive in aperture choices in the anchored convention.
Variants charged dispersion. Reflection not used, parity of ALL slotted currents provided by
 the proper vector covariance. No claim of phasing of the actual sign earned in a particular Wick room.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open Mink FirstPackMars NSF.Boundary LinearMap
variable {n m:ℕ} {Q: City} {P:Axis→Across} {L:Sheds Q P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Z:CloudsL) (F:ΧiMars) (j k b:Axis)
variable {W:Surface (SurfRimL Z)} {X:Wightman (SurfRimL Z)} {H:(SurfRimL Z).RealSpin} (D:SurfCheckL Z)
variable (c:X.Realizes (W:=W) (SurfCheckL.VesselPL p D) H)
variable (J: Axis→Test4→ₗ[ℂ] Module.End ℂ X.operators.domain)
  (K:Test4→ₗ[ℂ] Module.End ℂ X.operators.domain)
  (U:properCurrentSt p Z D c J)(v:∀ (g:Mink.Poincare) f, DragΛL X c g (K f) = K (Joint.push g f))
local notation "C§"=> spinCharge_st Z j J K
variable (f g:Test4)(t:j≠3)(w:k≠3)
local notation "ρ"=> flipLocationSt j k t w
variable (W:Test4→ₗ[ℂ] Module.End ℂ X.operators.domain)(φ:J j=W)
include U v φ
lemma directionDouble_st (y:k≠j)(a:ℝ): spinCharge_st Z j (fun _=>W) K a f g = -(spinCharge_st Z j (fun _=>W) K a (Joint.push ρ f) (Joint.push ρ g)):=by unfold spinCharge_st; rw [←φ]; exact twoExpensesSt p Z j k D c J K U v f g t w y a
set_option synthInstance.maxSize 20000 in
lemma directionEither_st (a:ℝ)(he:a≠0)(f g:Test4)(hc:SmallDoseSt f)(hw:SmallDoseSt g)(x:ℝ)
 (hx:0<x)(hv:∀ p∈ tsupport f,∀ q∈tsupport g, 2*x<YM.time q-YM.time p) (u:∀ p∈ tsupport f,∀ q∈tsupport g, p-q∈ spacelike)
 (b:ℝ)(ha:|b|=1)(z:ℂ)(h:z=(spinCharge_st Z j (fun _=>W) K b f g)) (ε:star z=z)(χ:z.re≠0)(p₀:LinearMap.IsSymmetric ((b:ℂ) • W f))(p₁:LinearMap.IsSymmetric (K g)):
 ∃ f' g':Test4, ( (f'=f ∧ g'=g) ∨ ∃ (k:Axis) (z:k≠3), k≠j ∧ f'=Joint.push (flipLocationSt j k t z) f ∧ g'=Joint.push (flipLocationSt j k t z) g ) ∧ SmallDoseSt f' ∧ SmallDoseSt g' ∧ Apart_st x f' g' ∧ LinearMap.IsSymmetric ((a:ℂ) • W f') ∧ LinearMap.IsSymmetric (K g') ∧ (spinCharge_st Z j (fun _=>W) K a f' g').im=0 ∧ ∃ δ:ℝ,0<δ∧δ<(spinCharge_st Z j (fun _=>W) K a f' g').re :=by
 have hk:z.im=0:=by have hm:= congrArg Complex.im ε; simp only[Complex.star_def,Complex.conj_im] at hm; linarith
 have hb:b≠0:=mt abs_eq_zero.mpr (by rw [ha]; norm_num)
 subst W z
 exact spinRaiseSt p Z j D c J K U v t a he f g hc hw x (fun p w q z=> ⟨by linarith [hv _ w _ z], u p w q z⟩) b hb hk χ p₀ p₁
#print axioms directionEither_st
end YM.GaugeFieldConstruction.Ember.Volumetric
end
