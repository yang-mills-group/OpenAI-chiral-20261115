import YM.SU5.FiniteGaugeData.Tower.Distance
import YM.CF.Buffered.Diphthong
import YM.SU5.FiniteGaugeData.Tower.Float
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Move the local algebra using two mirrors

Use `Diphthong.lean` twice-theta identity with the actual pin convention (not
changing spin basis on translation/AP wrap). For these cover marks the
movement we use is by multiples of **8B** in gauge-site units in the
invariance proof, shrinks in physical units in the hierarchy. Across s the
operator naturality of this action only concerns the scaled amount. No new
cutoff sequencing needed.
-/
open Heat Fock
section transport
variable (Z:Calibration)(a:Axis){S:Finset Cover}(x y z:ℤ)
variable {wide b:Bool}{F:Family Z}
local notation "R" => mirror Z a

private lemma compose_motion (i a:Axis)(x y:ℤ)(p:Cover): (plane i x).motion ((plane i y).motion p) a= (if i=a then p a+2*(x-y) else p a):=by rw [fling_move,fling_move]; split <;> ring

def address (a:Axis)(x:ℤ)(S:Finset Cover) := S.image (fun i=>i+(2*x) • step a)
lemma support_translation: reflectedBox a x (reflectedBox a y S) = address a (x-y) S:=by
 unfold reflectedBox address; rw [Finset.image_image]; exact image_congr fun (i:Cover) h=>by
     funext t; by_cases p:a=t
     · subst t; simp [Function.comp_apply,compose_motion]
     simp [Function.comp_apply,compose_motion,p,Ne.symm p]
-- move in units 2 gauge sites (one matter shift)
def chime (a:Axis)(z:ℤ)(f:Family Z):Family Z:=mirror Z a z (mirror Z a 0 f)
local notation "M"=>chime Z a
lemma moted (p:InTest Z wide S b F)(t:x-y=z): R x (R y F)= M z F :=by
 funext n w
 unfold mirror chime reflMark reflFields
 dsimp only [Prod.map] -- does unfold chime mirror again?
 change theta _ (theta _ (F n (fling a y _ (fling a x _ w.1), fling a y _ (fling a x _ w.2))))=
   theta _ (theta _ (F n (fling a 0 _ (fling a z _ w.1),fling a 0 _ (fling a z _ w.2))))
 have he(T:Pane (Z.c n)): fling a y _ (fling a x _ T)=fling a 0 _ (fling a z _ T):=by unfold fling; rw [←kor,←kor,plane_join,plane_join,t,sub_zero]
 rw [he w.1,he w.2, theta_theta _ _ _ (firm_join a y x) ((p.support n).allV _|>.sector),theta_theta _ _ _ (firm_join a 0 z) ((p.support n).allV _|>.sector),zero_sub]
 rw [show y-x= -z by omega]

lemma flow_port (p:InTest Z wide S b F):InTest Z wide (address a x S) b (chime Z a x F) := by
 have he:=axial Z a x (axial Z a 0 p)
 exact (show reflectedBox a x (reflectedBox a 0 S)=address a x S by rw [support_translation,sub_zero]) ▸ he
lemma chime_plus {G:Family Z}: M x (F+G)=M x F+M x G:=by unfold chime; rw [mirror_plus,mirror_plus]
lemma chime_scale (c:ℂ): M x (c • F)=c • M x F:=by unfold chime; rw [mirror_scale,mirror_scale,star_star]
lemma chime_product {G:Family Z}:M x (F*G)= M x F*M x G:=by unfold chime; rw [mirror_times,mirror_times]
lemma chime_unit:M x 1=1:=by unfold chime; rw [mirror_unit,mirror_unit]
lemma chime_cov (p:InTest Z true S false F)(h:CovCover Z F):CovCover Z (M x F):=covariant_flips Z _ _ (axial Z a 0 p) (covariant_flips Z _ _ p h)
lemma chime_pay (C:ℝ)(h:pay F C): pay (M x F) C:=pay_flips Z (pay_flips Z h a 0) a x
lemma bumps (p:InTest Z true S false F): M x (M y F)=M (x+y) F:=by
 let T:=R 0 F
 rw [←moted Z a (x+y) y x (flow_port Z a y p) (by omega), show (M y F)=R y T from rfl,reversal Z a y (axial Z a 0 p)]; rfl
lemma wake (p:InTest Z true S false F):M 0 F=F:=reversal Z a 0 p

lemma chime_diag (p:InTest Z true S false F):M x (R y F)=R y (M (-x) F):=by
 rw [←moted Z a (y+x) y x (axial Z a y p) (by omega), ←moted Z a y (y+x) (-x) p (by omega),reversal Z a y p,reversal Z a y (axial Z a (y+x) p)]
-- also transverse: theta vs twist. use commutation of translations with
-- mirrors transverse, for spatial + time later. park until then if needed.
end transport
section election
-- Actual E translation invariance, independent of having a common pivot schedule.
-- Mirror symmetry on each of two well placed planes (E can see both signs
-- there by reversal), no translation invariance asserted of sharp ratios.
open Heat
local notation "Z₀"=> tent Y H
variable (a:Axis)(z:ℤ)
local notation "J" x:max=> Heat.gaugeShift Λ.block x
local notation "R" x:max y:max=>mirror Z₀ a (J x) y
local notation "M" x:max y:max=> chime (tent Y H) a (J x) y
variable {F:Family (tent Y H)}{S:Finset Cover}

private lemma reverse_area {c:ℤ}{d:ℕ}(h:∀ x∈S,x a+d≤ c): region a c d (reflectedBox a c S):=by intro x p; obtain ⟨x,g,rfl⟩:= mem_image.mp p; rw [reflected_coord]; specialize h x g; omega
include V
private lemma star_neg (p:InTest K true S false F)(h:∀ x∈S,x a+(K).ℓ≤ J z): E s (R z F)=star (E s F):=by
 let h':= reverse_area a h
 have ht:R z F∈wing K a (J z):=(show _ from ⟨reflectedBox a (J z) S,axial (tent Y H) a _ p,h'⟩)
 nth_rw 2 [← reversal K a (J z) p]; rw [mirror_band Y H V s a z ht,star_star]
private lemma mission(p:InTest K true S false F):E s (M z F)= E s F:=by
 -- set a plane y very far left of all S, x=y+z (gauge aligned). reflected once then still far left even for negative z, behind x.
 have hx:∃ y:ℤ,region a (Heat.gaugeShift Λ.block y) (K).ℓ S ∧ ∀ x∈reflectedBox a (Heat.gaugeShift Λ.block y) S,x a+(K).ℓ ≤ Heat.gaugeShift Λ.block (y+z):=by
    obtain ⟨d,H'⟩:= sizes S; obtain ⟨m,t⟩:= H' a
    let u:ℤ:= |m|+(K).ℓ+|J z|+1; have h:1 ≤ u:=by have he:=abs_nonneg (J z); have hx:= abs_nonneg m; omega
    refine ⟨-u,?_,?_⟩
    · intro x hx; have he := (t x hx).1; unfold Heat.gaugeShift; have hB:1≤ (Λ.block.val:ℤ):=by exact_mod_cast Λ.block.property
      have hf: (K).ℓ - u ≤ m:=by unfold u; have hx:=abs_nonneg (J z); have hv:=neg_le_abs m; omega
      nlinarith
    intro x hx; obtain ⟨v,w,rfl⟩:= mem_image.mp hx; rw [reflected_coord]; have he: gaugeShift Λ.block (-u+z)=gaugeShift Λ.block (-u)+gaugeShift Λ.block z:=by unfold gaugeShift; ring
    rw [he]; have hB:1≤ (Λ.block.val:ℤ):=by exact_mod_cast Λ.block.property
    have hp:= (t v w).1; have hz:= neg_le_abs m; have hv : |J z|≥ -(J z):=neg_le_abs _; have h': J (-u)≤ -u:=by unfold gaugeShift; nlinarith
    unfold u at *; omega
 obtain ⟨y,t,h⟩:= hx
 rw [←moted (tent Y H) a (J (y+z)) (J y) (J z) p (by unfold gaugeShift; ring), Tower.star_neg Y H V s a (y+z) (axial (tent Y H) a _ p) h,mirror_band Y H V s a y (show F∈wing (tent Y H) a (J y) from ⟨S,p,t⟩),star_star]

lemma SWay (p:TestFamily K true F):E s (M z F)=E s F:= mission Y H V s a z p.paid.choose_spec
lemma home_motion {D:ℕ→Family K→ Family K}(P:Resolution Y H (E:=E) D)(p:TestFamily K true F): D s (M z F) = M (Λ.R.L.val*z:ℤ) (D s F):=by
 unfold chime
 rw [P.turn _ a _ (aux_test (axial K a _ p.paid.choose_spec)),P.turn s a 0 p, mul_zero,show (Λ.R.L.val:ℤ)* (J z)= J (Λ.R.L.val*z:ℤ) by unfold gaugeShift; ring]
lemma chime_X {D:ℕ→Family K→ Family K}(P:Resolution Y H (E:=E) D)(p:TestFamily K true F)(i:ℕ): stream Y H D s i (M z F) = M (Λ.R.L.val^i*z:ℤ) (stream Y H D s i F) :=by
 unfold chime; rw [stream_flipped Y H P s i _ _ (aux_test (axial K a _ p.paid.choose_spec)),stream_flipped Y H P s i a 0 p,mul_zero,show (Λ.R.L.val:ℤ)^i * (J z)= J (Λ.R.L.val^i*z:ℤ) by unfold gaugeShift; ring]
end election
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.SWay
#print axioms YM.CF.Buffered.Afterglow.Tower.chime_X
