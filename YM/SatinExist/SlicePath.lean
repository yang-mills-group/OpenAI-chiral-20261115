import YM.SatinExist.ColdSpring
import YM.SatinExist.Zond
/-! Pricing cuts at ONE large host in literal Fock coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 370000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {P: Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(H:Real.exp 1≤P.x)
namespace OneCup
local notation "W"=> tent Y H
variable (S: Finset Cover)(s i:ℕ) (E:Dome (tent Y H)→ₗ[ℂ]ℂ)
local notation "Γ"=> side Y i s
local notation "m"=> momentm Y i s
local notation "Q"=> FC (Single (Γ))
private lemma sails {U V:Side}(f:U=V)(X: Mark U)(h:∀ a b:Fields U,X a = X b) (a b:Fields V): ship f X a= ship f X b:= by subst V; exact h a b
private lemma sailsOne {U V: Side}(f:U=V)(X: Mark U)(h:∀ a:Fields U,∃ k:ℂ,X a= k • 1) (a:Fields V): ∃ k:ℂ, ship f X a=k • 1:=by subst V; exact h a
variable (h: Hosp S ((tent Y H).c (momentm Y i s)))
local notation "τ"=>distribute Y H s i
def portLX (V:Fields (side Y i s)): Dome (tent Y H) →ₗ[ℂ] FC (Single (side Y i s)) where
  toFun f:= (distribute Y H s i f.val) V
  map_add' f g:= congrFun ((distribute_arith Y H s i _ _ 0).1) V
  map_smul' c f := congrFun ((distribute_arith Y H s i f.val f.val c).2.2.1) V
variable {Y}
local notation "π"=> portLX Y H s i
local notation "ϕ"=> slice W E
include h
lemma examinator :∃ U : FC (Single (side Y i s))→ₗ[ℂ]ℂ, ∀ f∈bay (tent Y H) S true, PureMatter (tent Y H) f→∀ V:Fields (side Y i s), U (distribute Y H s i f.val V)= E f := by
 let M:= matterPlane W ⊓ (bay W S true).toSubmodule
 let f:= (π (1,1)).domRestrict M
 have ht:(f).ker=⊥:=LinearMap.ker_eq_bot.mpr (by
    intro u v k; apply Subtype.ext; apply Subtype.ext; apply stationary_ext Y H s S i h (show u.val∈bay W S true from u.property.2) (show v.val∈bay W S true from v.property.2)
    funext V
    have hol:PureMatter W u.val:=u.property.1; have hz:PureMatter W v.val:=v.property.1; let A:= (1,1); exact (sails (terrain ..) _ (hol (momentm Y i s)) V (1,1)).trans (k.trans (sails (terrain ..) _ (hz _) _ _)))
 obtain ⟨g,p⟩:= LinearMap.exists_leftInverse_of_injective f ht
 refine ⟨(E.domRestrict M).comp g,fun a q r V=>?_⟩; unfold distribute; rw [sails (terrain ..) _ (r _) V (1,1)]
 let x:M:=⟨a,r,q⟩; change E (M.subtype ((g.comp f) x)) = _; rw [p]; rfl
variable (U:FC (Single (side Y i s))→ₗ[ℂ]ℂ)(r:∀ f∈bay (tent Y H) S true, PureMatter (tent Y H) f→∀ V:Fields (side Y i s), U (distribute Y H s i f.val V)= E f)
omit h
include r
lemma termBy {x:Dome (tent Y H)}(hp:x∈bay (tent Y H) S true)(V:Fields (side Y i s)): π V (slice (tent Y H) E x)= U ((π V) x) • 1:=by
 obtain ⟨u,rfl⟩:=accolade W S x hp
 let G(i:Pigment S): Dome W:= ⟨scalar W (daub S i), broadCompile W S (.seed (authentic ..))⟩
 have hx: badge W S u=∑ i:Evens S, G (u i)*toastPoint W S i := by
   apply Subtype.ext; change render S W u=(screenHall W).val _
   rw [render_eq,map_sum]; apply sum_congr rfl; intro i _; rfl
 rw [hx,map_sum,map_sum,map_sum,map_sum,sum_smul]; refine sum_congr rfl fun j _=>?_ ; let y:= toastPoint W S j
 let b:=u j; have hG:PureGauge W (G b):= ⟨S,_, authentic ..,rfl⟩; have hw:PureMatter W y:=wordIndependent W (tagWord S j.val)
 let A:=π V y; obtain ⟨k,hk⟩:= sailsOne (terrain Y H (Y.ir i) s) ((G b).val (momentm Y i s)) (fun a=> ⟨daub S b _,rfl⟩) V
 rw [slicer W E _ _ hG hw,map_smul]; change E y • π V (G b)= _; rw [show π V (G b)= _ from hk]
 have hz: π V ((G b)*y)= k • A:=by
   change (τ ((G b).val*y.val)) V = _; rw [(distribute_arith Y H s i _ _ 0).2.1,Pi.mul_apply]; change _* A = _; rw [show τ (↑(G b)) V =_ from hk, Matrix.smul_mul,one_mul]
 change _= U _ • (1: FC _); rw [hz,map_smul,show U A=E y from r y (toastAt S j) hw V,smul_smul,mul_comm,smul_eq_mul] -- defeq?
#print axioms termBy
end OneCup
end YM.CF.Buffered.Afterglow.Six
