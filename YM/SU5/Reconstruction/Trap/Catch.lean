import YM.SU5.Reconstruction.Trap.Roll
import YM.SU5.Reconstruction.Trap.Dried
/-!
# Crossing from a light axis ray
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open Complex -- exp
open YM.Multiplier Chirp
variable {K H D:Hilbert} {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
namespace Clasp
variable (C:Clasp K H D) (L:X→ℝ)(h:Measurable L)(p:∀ x,0≤L x) (M:Y→ℝ)(b:Measurable M)(q:∀ y,0≤ M y)
   (e:ℝ)(t:e=1∨e=-1) (P : PVM H X)(Q : PVM D Y)
local notation "A"=> sail e
local notation "B"=> sail (-e)
def Tide : Prop:=∀ x:ℝ,0<x→ Pass C (order P (slopeRay (sail e) L x)) (order Q (slopeRay (sail (-e)) M x))
-- notation safe phase-specific
local notation "Z"=> P.region (onboard L)
local notation "E"=> Q.region (onboard M)
local notation "U" t:max=> singers P L t
local notation "V" t:max=> singers Q M t
variable (c:Tide C L M e P Q)
include h in
lemma ticketProj : IsStarProjection (P.region (onboard L)):= ⟨by
 change (P.region (onboard L)).comp Z=Z; rw [P.joins (arc L h) (arc L h), inter_self],P.real (arc L h)⟩
include b q h p t c
lemma ever (u:ℝ): C.Pass (singers P L u) (singers Q M u * Mint (Q.region (onboard M)) (wages e u)):= by
 let x:=starry P L u; let y:= starry Q M u; let g:=wages e u; let z:=(1-E:D.Op)
 have hz:= Noon C L h p M b q e t P Q c; have hs: V u* E=y:=by rw [(sings Q M b u|>.comm (arc M b)).eq]; exact (refreshing Q M b u).symm
 rw [show V u*_=(g:ℂ) • y+z from ?_]
 · rw [full_star P L h p u]; exact (North C L h p M b q e t P Q c u).add (C.one.sub hz)
 unfold Mint; rw [mul_add,mul_sub,mul_one,Algebra.mul_smul_comm,hs,full_star Q M b q]; change y+z-y+_= _; abel
lemma link (u:ℝ): ScalePass C Z E (singers P L u) (singers Q M u) (wages e u) := by
 let a:=ticketProj L h P; let d:=ticketProj M b Q; let g:=wages e u
 have hx: (wages e (-u))=g⁻¹:=by unfold g wages; rw [← Real.exp_neg]; ring_nf
 refine ⟨a,d,Noon C L h p M b q e t P Q c,wages_pos ..,?_ ,?_,(sings P L h u|>.comm (arc L h)), (sings Q M b u|>.comm (arc M b)), ever C L h p M b q e t P Q c u,?_⟩
 · rw [Pays,powered P L h u]; exact ⟨by simpa only [neg_neg] using choir P L h (-u),choir P L h u⟩
 · rw [Pays,powered Q M b u]; exact ⟨by simpa only [neg_neg] using choir Q M b (-u),choir Q M b u⟩
 rw [powered P L h,powered Q M b]; rw [(Mint.full (sings Q M b _|>.comm (arc M b)).symm g⁻¹).eq]; rw [←hx]; exact ever C L h p M b q e t P Q c (-u)
noncomputable def look : H≃ₗᵢ[ℂ] D:= C.Left.symm.trans C.Right -- `include` will insert? def
local notation "F"=> C.look.toContinuousLinearEquiv.toContinuousLinearMap
lemma frameInterlaces (f:ℝ→ℂ)(g:Tag f): (F).comp (order P (f ∘ L))=(order Q (f ∘ M)).comp F := by
 apply recover P Q L M h b p q F f g
 · have v:= link C L h p M b q e t P Q c 0; let X':= C.bring Z E; obtain ⟨_,vh,vd⟩:=C.capProj v.lap v.rap v.dialog
   ext1 x; obtain ⟨x,rfl⟩:= C.Left.surjective x; change C.Right (C.Left.symm (Z (C.Left x)))=(E) (C.Right (C.Left.symm (C.Left x)))
   rw [show Z (C.Left x)=C.Left (X' x) from DFunLike.congr_fun vh.symm x]; rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact DFunLike.congr_fun vd x
 intro u; let v:=link C L h p M b q e t P Q c u; let R:= halfway C v; obtain ⟨r,w⟩:= C.halftime v
 ext1 x; obtain ⟨x,rfl⟩:= C.Left.surjective x; change C.Right (C.Left.symm ((U u) (C.Left x)))=(V u) (C.Right (C.Left.symm (C.Left x)))
 rw [show (U u) (C.Left x)=C.Left (R x) from DFunLike.congr_fun r.symm x]; rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact DFunLike.congr_fun w x
-- Ad scale boost. Acting `cLeft s` boosts by -e*π*s on Aₑ generator.
noncomputable def lengthen (u:ℝ):= Real.exp (-e*Real.pi*u)
omit h p b q t c in
lemma wages_eq (u i:ℝ):sing u (wages e i * wages e i)= sing i (lengthen e u):=by
 unfold sing lengthen wages; rw [← Real.exp_add,Real.log_exp,Real.log_exp]; congr 1; push_cast; ring
lemma weightTransport (f:ℝ→ℂ)(l:Tag f)(u:ℝ): C.cLeft u * order P (f ∘ L)= order P (f ∘ (fun x=> lengthen e u * L x))* C.cLeft u:= by
 set d:= lengthen e u; set R:= C.cLeft u; let k(x:X):= d*L x; have hd:0<d:= Real.exp_pos _; have hm: onboard k=onboard L:=by ext x; change 0<d*L x ↔ _; simp [hd,onboard]
 -- rewrite? hm simp maybe
 have r1:Measurable k:=h.const_mul _
 refine recover P P L k h r1 p (fun x=> mul_nonneg hd.le (p x)) R _ l ?_ (fun i=>?_)
 · rw [hm]; exact (hourComm C (link C L h p M b q e t P Q c 0) u).eq
 let v:=link C L h p M b q e t P Q c i; let A':=U i; let x:ℂ:=sing i d
 have he:R*A'*star R=A'*(1-Z)+x • (A'*Z):= by
    have ht:= C.passage v u; rw [wages_eq] at ht; exact ht
 change R * _= _ * R -- may need comp sugar
 have hx: singers P k i=A'*(1-Z)+x • (A'*Z):= by
   have u:=sings P L h i; have t:=Registers.box P (arc L h); refine (sings P k r1 i).single (((u.times ((Registers.one P).sub t)).add ((u.times t).scale x)).agrees (sings P k r1 i|>.price) ?_); intro v; refine Eventually.of_forall fun w=>?_
   by_cases q:w∈ onboard L
   · change 0<L w at q; have q':w∈ onboard L:=q
     simp [q',smul_eq_mul,k]; rw [voices i _ _ hd q]
   have hs:L w=0:= le_antisymm (le_of_not_gt q) (p w); simp [hs,q,k]
 rw [hx,← he,mul_assoc, (C.left_credentials u).2.2.1,mul_one]
end Clasp
end YM.CrossedFrame
