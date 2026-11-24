import SatinPP.SeaGreen

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" j:max => P.advocate 3 x j
local notation "K₁" j:max => P.ManyF j (P.advocate 3 x j)
local notation "Π'" j:max=>P.wealth j (P.advocate 3 x j)
local notation "Sh"=>Shrine (P.houses x)
local notation "W"=>P.socials x
local notation "ω"=>P.lights x

open Hierarchy.Seld

variable (j:Axis)
local notation "Y"=>P.lights x j
local notation "V"=>P.socials x j
local notation "C"=>P.Cathedral x

lemma masonry (A:P.Apron):
    ∃ T:Sh, T∈C ∧ T.f j=P.seating j x (A.engine P j (ξ j)):=by
 let s:=fun i=> (⟨A.realWidth P i,(Apron.real_width_pos P i A).le⟩:ℝ≥0)
 refine ⟨P.allot x A s, Matte.sprout_sub (P.Lore x)
    ⟨A,fun _=>le_rfl,rfl⟩,?_⟩
 change P.seating j x (P.locket j _ A (A.realWidth _ _) (A.realWidth _ _))=_
 rw [locket_own]

lemma spheres (p:Bool)(u:P.Partner j):
   ∃ T:Sh,T∈C ∧ Land.soup W ω j T p 0=(Π' j) (P.oneSide j (ξ j) u):=by
 obtain ⟨i,g,v⟩:=u
 obtain ⟨D,_,_,q⟩:=P.realizesView j (ξ j) i g v
 have hu:P.seating j x (D.engine P j (ξ j)) Y=
    (Π' j) (P.viewF j _ i v):=by rw [←q]; rfl
 change ∃ T:Sh,T∈C ∧ Land.soup W ω j T p 0=
    (Π' j) (P.viewF j _ i v)


 unfold Land.soup orbit_on
 cases p
 · obtain ⟨T,h,t⟩:=P.masonry x j D
   refine ⟨T,h,?_⟩
   rw [opt_zero,t]; exact hu
 obtain ⟨T,h,t⟩:=P.masonry x j (D.kiss P j)
 refine ⟨T,h,?_⟩
 rw [opt_zero,t,←Apron.peer,P.seating_star]
 change star (star (P.seating j x _)) _=_
 rw [star_star]; exact hu

#check SelectionAnalysis.lamp_fixed


lemma power (u:E4):(V).unit.translation u (Y) = Y:=by
 change (V).edge _ (Land.leg V u _)=_
 rw [show Land.leg V u=P.cartage j (ξ j) (roll u) from P.Q_cart j (ξ j) u]
 unfold lights; rw [cart_empty]
 exact (SelectionAnalysis.lamp_fixed V _).mpr (P.heaven_hot _ _) _

lemma chambersG(p:Bool): Seance W ω C j p:=by
 intro z h
 let B:=P.ColorHil j (ξ j)
 let f:= (innerSL ℂ z).comp (Π' j)
 have he:Submodule.span ℂ (Set.range (P.oneSide j (ξ j))) ≤ f.ker:=by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i,rfl⟩
    obtain ⟨T,e,a⟩:=P.spheres x j p i
    change inner ℂ z ((Π' j) _)=0
    rw [←a]; exact h T e _
 let v:= P.enter j (ξ j) z
 have hg:v∈ f.ker:=closure_minimal (SetLike.coe_mono he) f.isClosed_ker (P.partner_dense j (ξ j) v)
 have hr:(Π' j) v = z:=P.rewarded j (ξ j) z
 exact inner_self_eq_zero.mp (Eq.mpr (congrArg (fun y=>inner ℂ z y=0) hr.symm) hg)
#check @Breve.Pace
#print swingCone

#print swingCone
variable (k:Axis)
abbrev DayStar:=Cinema (P.socials x j)
lemma procession_LocalFieldBounds (Z:P.Ellis 3 x)(p:k≠j)(u:P.DayStar x j)(w:P.DayStar x k):
    Breve.Pace W ω j k C:=by
 exact ⟨p,⟨P.philosophize x j Z k,rlock _ _ (P.power x j),rlock _ _ (P.power x k)⟩,
   P.power x j,u,w,P.chambersG x j⟩
#print axioms procession_LocalFieldBounds
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
