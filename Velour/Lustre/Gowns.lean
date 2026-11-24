import Velour.Escutcheon.Torte
import Velour.Lustre.Stars
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour


open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open Boundary Probe
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "𝓗"=> P.ManyF j ξ
local notation "σ"=> P.seasons j ξ

local notation "U"=> P.Latent x
variable (y:P.invCrown j (P.advocate 3 x j))

lemma dotCoin (a:U) :
 (σ).Cashable (P.twink x j a):=(P.behold x j a).ribbon.cash -- lemma better

def wears : (σ).Livery (U) where
 Q:= P.twink x j
 Y:= P.glimmers x j
 m u:= ((σ).cashed (P.dotCoin x j u)).choose
 G u:= ((σ).cashed (P.dotCoin x j u)).choose_spec.choose
 Ω:=P.firstTulle j ξ
 vacE:=P.heaven_hot j ξ
 vacU:=P.crown_vac j ξ y
 sewn:= (P.meander x j).1
 prepaid u:=((σ).cashed (P.dotCoin x j u)).choose_spec.choose_spec
-- include y? parameter used in body Lean doesn't auto include? defs yes
def pressed (p:E4):Vantage:= fun i=> p i


lemma sybaris (p:E4):
 Hierarchy.Seld.M (σ) (SEP j p).val = P.cartage j ξ (pressed p):=by
 rw [laneslot,P.uses_cart,eyes_toFace _ (SEP _ p)]
 exact congrArg _ (congrArg _ (funext fun i=>by
   have g:i.val≠j:=i.property
   change (p-(p j) • basis j) i.val = p i.val
   simp [basis,g] ))

variable {I:Type}
local notation "L"=> P.wears x j y

lemma sybarites (u:I→U)(p:I→E4)(l r:I→ℝ)(i:I)
 (d:l i<p i j)(e:p i j<r i):
 (L).styled u p l r i=P.fleck x j (u i) (pressed (p i)) (l i) (r i):=by
 rw [(L).styled_q u p l r i d e,P.sybaris,
     show - (SEP j (p i)).val=(SEP j (-(p i))).val from by rw [map_neg];rfl,P.sybaris]
 rfl

include y
lemma glade_star (u:I→U)(p:I→E4)(J:List I)
 (w:Curtains (fun i=>p i j) (fun i=>p i j) J):
 (L).glade u p J=P.sunPrint x j u (pressed∘p) J w.first w.last:=by
 rw [← (L).glade_styled u p _ _ J
      (fun i t=>⟨w.inside i t, w.outside i t⟩) w.joins]
 -- substitute mapped list

 rw [show J.map ((L).styled u p w.first w.last)
     = J.map (fun i=>P.fleck x j (u i) (pressed (p i)) (w.first i) (w.last i)) from
        List.map_congr_left fun i t=>P.sybarites x j y u p _ _ i (w.inside i t) (w.outside i t)]
 rfl

omit y
lemma eachOrder {r:ℕ} (g h:Equiv.Perm (Fin r)):
 ((Each r).map g).Perm ((Each r).map h):=by
  refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange r).map g.injective)
     ((List.nodup_finRange r).map h.injective)).mpr fun i=>
     iff_of_true (List.mem_map.mpr ⟨_,List.mem_finRange _,g.apply_symm_apply i⟩)
       (List.mem_map.mpr ⟨_,List.mem_finRange _,h.apply_symm_apply i⟩)
lemma eachAsc {n:ℕ} (p:Fin n→E4)(g:Equiv.Perm (Fin n))
     (r:StrictMono fun i=>p (g i) j): Ascends j (pressed ∘ p) ((Each n).map g):=by
 refine List.pairwise_map.mpr ?_
 exact (List.pairwise_lt_finRange n).imp (fun {_ _} e=>r e)

include y
theorem excels (b:Axis)(v:P.invCrown b (P.advocate 3 x b))
 (R:P.Ellis 3 x):
 Pact L (P.wears x b v):=by
 intro r a p g h t f
 let w:= eachAsc j p g t
 let z:= eachAsc b p h f

 obtain ⟨c⟩:= Ascends.curtain _ _ _ w
 obtain ⟨d⟩:= Ascends.curtain _ _ _ z
 rw [(L).glade_shape a p g, (P.wears x b v).glade_shape a p h,
    P.glade_star x j y a p _ c, P.glade_star x b v a p _ d]
 exact P.star_draped x j a _ _ c d (eachOrder _ _) R w z
#print axioms excels


