import GaugeFieldConstruction.StencilForecast
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
abbrev spinCharge_st (a:ℝ)(f g:Test4) :ℂ:= pairPriceSt Z (X:=X) ((a:ℂ) • J j f) (K g)
local notation "C§"=> spinCharge_st Z j J K
variable (f g:Test4)(t:j≠3)(w:k≠3)
local notation "ρ"=> flipLocationSt j k t w
lemma sign_money_st (a b:Axis): costΛ (ρ).Λ⁻¹ a b= if a=b then (bothSign j k b:ℂ) else 0:=by
 have ht(i:Axis):(ρ).Λ⁻¹.act (basis b) i= bothSign j k i*basis b i := (by -- co-moving switch, then evaluate
    rw [show (ρ).Λ⁻¹=(ρ).Λ from congrArg Poincare.Λ (come_equal j k t w)]; exact flip_at j k i (basis b))
 unfold costΛ; rw [ht]; by_cases p:a=b <;> simp [p]
include U
lemma wakeTurnSt (y:k≠j)(a:ℝ): DragΛL X c ρ (((a:ℂ) • J j f)) = -((a:ℂ) • J j (Joint.push ρ f)):=by
 have he:DragΛL X c ρ (J j f)= -(J j (Joint.push ρ f)):=by
    rw [U ρ j f]; simp_rw[sign_money_st]; rw [sum_eq_single j]
    · rw[if_pos rfl, show (↑(bothSign j k j):ℂ) = (-1:ℂ) from (by simp [bothSign,flips,y])]; exact neg_one_smul ℂ (J j (Joint.push ρ f)) -- proper
    · intro b _ p; rw [if_neg p.symm,zero_smul]
    simp
 calc
    _= (a:ℂ) • DragΛL X c ρ (J j f):=by unfold DragΛL; rw [LinearMap.smul_comp,LinearMap.comp_smul]
    _ = _:= by rw[he,smul_neg]
include v
lemma twoExpensesSt (y:k≠j)(a:ℝ): (C§) a f g = -(C§ a (Joint.push ρ f) (Joint.push ρ g)):=
    oppositeBillSt p Z j k t w D c (fun f:Test4=>(a:ℂ) • J j f) (K) f g (wakeTurnSt p Z j k D c J U f t w y a) (v ρ g)
omit U v
include c
lemma shiftedSymSt (A:Module.End ℂ X.operators.domain)(t:Mink.Poincare)(w:LinearMap.IsSymmetric A):LinearMap.IsSymmetric (DragΛL X c t A):=by
 let Z0:=LocalActΛL X c t; let Z1:=LocalActΛL X c t⁻¹
 have he : Surjective Z0 := fun x=>⟨Z1 x, LocalHomeΛL X c t x⟩
 intro a b; obtain ⟨a,rfl⟩:=he a; obtain ⟨b,rfl⟩:=he b; unfold Z0; rw [turn_wake p Z D c,turn_wake p Z D c,turn_read p Z D c,turn_read p Z D c,w]
include U v
lemma spinRaiseSt (a:ℝ)(he:a≠0)(f g:Test4)(hc:SmallDoseSt f)(hw:SmallDoseSt g)(x:ℝ)(u:Apart_st x f g)
 (b:ℝ)(ha:b≠0)(ε:(C§ b f g).im=0)(χ:(C§ b f g).re≠0)(p₀:LinearMap.IsSymmetric ((b:ℂ) • J j f))(p₁:LinearMap.IsSymmetric (K g)):
 ∃ f' g':Test4, ( (f'=f ∧ g'=g) ∨ ∃ (k:Axis) (z:k≠3), k≠j ∧ f'=Joint.push (flipLocationSt j k t z) f ∧ g'=Joint.push (flipLocationSt j k t z) g ) ∧ SmallDoseSt f' ∧ SmallDoseSt g' ∧ Apart_st x f' g' ∧ LinearMap.IsSymmetric ((a:ℂ) • J j f') ∧ LinearMap.IsSymmetric (K g') ∧ (C§ a f' g').im=0 ∧ ∃ δ:ℝ,0<δ∧δ<(C§ a f' g').re :=by
 let F:= spinCharge_st Z j J K
 obtain ⟨k,hk,t'⟩:= fare_other_st j; let ρ':= flipLocationSt j k t hk
 have hz(a:ℝ): F a (Joint.push ρ' f) (Joint.push ρ' g)= -(F a f g):= neg_eq_iff_eq_neg.mp (twoExpensesSt p Z j k D c J K U v f g t hk t' a).symm
 let r:=a/b; have h':r≠0:=div_ne_zero he ha; have hv : (a:ℂ)= (r:ℂ)*(b:ℂ):=(Complex.ofReal_mul .. ▸ congrArg ((↑):ℝ→ℂ) (div_mul_cancel₀ a ha)).symm
 have hg: IsSymmetric ((a:ℂ) • J j f):= by rw [hv,mul_smul]; exact p₀.smul (Complex.conj_ofReal _)
 have hs: F a f g=(r:ℂ)*F b f g:=by unfold F spinCharge_st; rw [payScaledSt,payScaledSt,hv,mul_assoc]
 have hx : (F a f g).re≠0:=by rw [hs,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact mul_ne_zero h' χ
 have hX: (F a f g).im=0:=by rw [hs]; simp [show (F b f g).im=0 from ε]
 rcases lt_or_gt_of_ne hx with t|t
 · have h' : 0<(F a (Joint.push ρ' f) (Joint.push ρ' g)).re:= by rw [hz,Complex.neg_re]; exact neg_pos.mpr t
   refine ⟨Joint.push ρ' f,Joint.push ρ' g,Or.inr ⟨k,hk,t',rfl,rfl⟩, foldMark_st j k (by assumption) hk f hc, foldMark_st j k (by assumption) hk g hw, fold_locale_st j k (by assumption) hk x f g u, ?_, (v ρ' g) ▸ shiftedSymSt p Z D c _ ρ' p₁, ?_,_,half_pos h',half_lt_self h'⟩
   · have t:= shiftedSymSt p Z D c _ ρ' hg; erw [wakeTurnSt p Z j k D c J U f (by assumption) hk t' a] at t; simpa only [zero_sub,neg_neg] using IsSymmetric.zero.sub t
   change (F a (Joint.push ρ' f) (Joint.push ρ' g)).im=0; rw [hz,Complex.neg_im,hX,neg_zero]
 exact ⟨f,g, Or.inl ⟨rfl,rfl⟩,hc,hw,u,hg,p₁,hX,_,half_pos t,half_lt_self t⟩
#print axioms spinRaiseSt
end YM.GaugeFieldConstruction.Ember.Volumetric
end
