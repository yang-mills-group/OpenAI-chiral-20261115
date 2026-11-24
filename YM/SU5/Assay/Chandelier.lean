import SatinFixedContrastNovember4
import YM.SU5.Assay.FloorService
import YM.SU5.Assay.DuoNotice
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Six
/-!
 The **same** caliper serves all old and new expenses. No mark
 rebilled for a new width solely to claim viewer approximability.
-/
variable {P:Spine}{D N:Doorway}{o:Orders}{j:Axis}{t:ℕ}{k r:ℤ}{w v:ℕ}
def Doorway.canopy (D N:Doorway):Set Vantage:= D.foyer.invites ∪ N.foyer.invites
local notation "Φ"=>D.canopy N
local notation "γ"=>P.FrameFace j t
local notation "τ"=>P.tock t
namespace Curtain
variable (h:P.Curtain D j t k w) (g:P.Curtain N j t r v)
include h
lemma shades : γ D.foyer.invites (D.lower j) (D.upper j) k w:=by
 refine ⟨h.width,h.left,h.right,?_⟩
 intro y i
 have : D.foyer.lower j < y j ∧ y j < D.foyer.upper j:=i j (Set.mem_univ j)
 exact ⟨h.starts.trans this.1.le,this.2.le.trans h.ends⟩
include g
lemma across (u:D.upper j≤N.lower j):∃m,γ Φ (D.lower j) (N.upper j) k m ∧ k+w≤r∧k+(m:ℤ)=r+v:=by
 have h':γ D.foyer.invites (D.lower j) (N.lower j) k w:=⟨h.width,h.left,h.right.trans u,h.shades.buys⟩
 exact h'.connect g.shades
lemma canvas (u:D.Later N o 0):∃p q l m, γ Φ p q l m :=by
 have x:=u j
 simp only [Pi.zero_apply,mul_zero,add_zero] at x
 split at x
 · obtain ⟨m,p,_⟩:=h.across g x.le; exact ⟨_,_,_,_,p⟩
 obtain ⟨m,p,_⟩:=g.across h x.le
 have q:N.canopy D=Φ:=Set.union_comm ..
 exact ⟨_,_,_,_,q ▸ p⟩
end Curtain

lemma Tickets.light (h:P.Tickets D t)(g:P.Tickets N t)(u:D.Later N o 0):
 P.FrameFloor t Φ ∧ ∃i w,P.FrameFace 3 t Φ (D.lower 3) (N.upper 3) i w:=by
 constructor
 · intro j;obtain ⟨i,w,x⟩:=h j;obtain ⟨l,v,y⟩:=g j;exact x.canvas y u
 obtain ⟨i,w,x⟩:=h 3;obtain ⟨l,v,y⟩:=g 3
 obtain ⟨m,p,_⟩:=x.across y (u.split.1.trans u.split.2).le
 exact ⟨_,_,p⟩
variable {A B:P.Apron}{F G:SampleDose} {c d:Bool} {l m:P.Folio}{x:P.Spectrum0 3}
local notation "f"=>P.prepared t A F
local notation "g"=>P.prepared t B G
local notation "X"=>P.spacePrice A F
local notation "Y"=>P.spacePrice B G
local notation "M"=>P.asked_at t
lemma asked_at.lift {y:P.Test}{U V:Set Vantage}(h:M y U)(u:U⊆V):M y V:=by obtain ⟨v,r,t⟩:=h;exact ⟨_,r,t.trans u⟩
lemma Notice.hangs (u:P.Notice x t D A c l F):X⊆D.foyer.invites:= fun _ y j _=> (u.admits j).aperture y
namespace DuoNotice
variable (h:P.DuoNotice x t D A c l F N B d m G)
include h
lemma hangs : X⊆Φ ∧ Y⊆Φ ∧ X∪Y⊆Φ:=
 ⟨h.first.hangs.trans subset_union_left,h.second.hangs.trans subset_union_right, union_subset_union h.first.hangs h.second.hangs⟩
lemma lights:M f Φ ∧ M g Φ ∧ M (f*g) Φ:=
 ⟨h.first.prices.localFunds.lift h.hangs.1,h.second.prices.localFunds.lift h.hangs.2.1,h.prices.localFunds.lift h.hangs.2.2⟩
end DuoNotice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
