import Bay.C.Blue
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise



open Rate LocalLimit Preparation Pitching Focus 
set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
local notation "VΔ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


open Buffered Lifted Sour
variable {c f:Side}
variable (G:Ratio c f)

abbrev drift (L:Side):ℕ:= Finset.univ.sup fun r:Site L=>2*Laurent.size (lift r)

lemma alcove (x:Site f):
 let z:=((isle G).symm x).1
 separation (node x) (node (heel G z)) ≤ drift G.count:=by
 rintro z
 let r:=((isle G).symm x).2
 have h:x-heel G z=wrap f (lift r):=by
   have b:= (isle G).apply_symm_apply x
   change isle G (z,r)=x at b
   unfold heel
   calc
    _=isle G (z,r)-isle G (z,0):=by rw [b]
    _= _:= by
     rw [isle_apply,isle_apply]

     rw [show lift (0:Site G.count)=0 from by simp,map_zero]; abel
 let a:= heel G z
 have j:node x-node a=wrap (More f) ((2:ℕ) • lift r):= by

   have y:x=wrap f (lift r+ lift a):=by rw [map_add,wrap_lift a,←h,sub_add_cancel]
   have t:node x=wrap (More f) (nodeC (lift r+lift a)):=by
       calc
        _=node (wrap f (lift r+lift a)):=congrArg node y
        _= _:=node_of ..
   have u:node a=wrap (More f) (nodeC (lift a)):=by
       calc
        _=node (wrap f (lift a)):=congrArg node (wrap_lift a).symm
        _= _:=node_of ..
   rw[t,u,←map_sub]
   congr 1
   unfold nodeC
   rw[smul_add]
   abel
 rw [separation,j]
 exact ((Zephyr.Chern.pdist_wrap _ _).trans_eq (Zephyr.Chern.size_two _)).trans
    (le_sup (f:=fun r=>2*Laurent.size (lift r)) (mem_univ r))



open Swell Push.Uniform

namespace HullF
variable (w:HullF)
abbrev steeple:Prop:=drift w.L ≤ 24*w.newb.p.B
abbrev dport (x:Site w.sea)(s:Sweep w.sea) :Site w.home:=
 ((isle w.G).symm ((Tofu (castX s) w.sea).symm x)).1
abbrev flagroot (x:Site w.sea)(s:Sweep w.sea):Seat w.sea:=
 boxA s (node (heel w.G (w.dport x s)))
lemma berthroot (x:Site w.sea)(s:Sweep w.sea)
 (b:w.steeple):
 w.flagroot x s ∈ grooveB 24 w.newb.p (node x):=by
 let y:= (Tofu (castX s) w.sea).symm x
 have t:boxA s (node y)=node x:=by
     rw [show boxA s (node y) = node (Tofu (castX s) w.sea y) from ((castX s).nodex ..).symm,(Tofu (castX s) w.sea).apply_symm_apply]
 refine halo_spec.mpr ⟨_,mem_singleton.mpr t,?_⟩
 unfold flagroot
 rw [sitT]
 exact (alcove w.G y).trans b

#print Multiplicity

variable (x:Site w.sea)(s:Sweep w.sea){M:ℕ}
 {I:Type}[LinearOrder I][Fintype I]

lemma gridLib (T:I→SealV w.sea)
 (p:Fintype.card I ≤ M)
 (e:∀i,(T i).root=w.flagroot x s):
 w.grid M (fun _=>w.dport x s) (fun i=>watch s (T i)):=by
 let f:=gr (fun i=>watch s (T i))
 let z:= node (heel w.G (w.dport x s))
 have r(i):f i=z:=by change (boxA s).symm (T i).root = z; rw[e i];exact (boxA s).symm_apply_apply z

 have q (p:I→Prop)[DecidablePred p]:
     (univ.filter p).card≤M:=
   (card_le_card (filter_subset ..)).trans_eq card_univ |>.trans ‹Fintype.card I ≤ M›
 refine ⟨funext r,⟨fun i=>q _, ?_⟩,fun _=>q _⟩
 intro i j h
 exact False.elim (h ((r i).trans (r j).symm))
#check Berth.Rig.sizeB
