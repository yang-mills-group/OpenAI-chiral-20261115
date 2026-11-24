import ZecaRelic
import ZecaQDeriv
import ZecaShell
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

local notation "MH"=> Hierarchy.Seld.Zeca.Moment

open Hierarchy.Seld.Poin Hierarchy.Seld.Zeca.Monument
open Boundary
abbrev Tent (P:Spine)(x:P.Spectrum0 3)(ι:Type) :=
    Canopy (P.ManyF 3 (P.advocate 3 x 3)) ι
variable {ι:Type}(N:P.Tent x ι)
local notation "wΩ"=>P.nova 3 ξ
local notation "J"=>Grotto S N Ω
local notation "H'"=> chapel S N Ω
local notation "Z"=>springs S N Ω
local notation "qΩ"=> saint S N ν wΩ
local notation "op"=>mast S N ν wΩ
local notation "qv"=>mastV S N ν wΩ
local notation "lens"=>(H').lens Z qΩ

abbrev Vh:= Action (Grotto (P.seasons 3 (P.advocate 3 x 3)) N (P.heaven 3 (P.advocate 3 x 3)))


lemma att_compact (F:SampleDose): HasCompactSupport (⇑(att F)):=
  (F.budget.comp_homeomorph backV.toHomeomorph).mono
    (fun _ h e=>h (Complex.ofReal_eq_zero.mpr e))
local notation "Γ"=>Sachet S N

structure Board (D:P.Cilium x)(F U:SampleDose)(V:Vh P x N)(d:Lead.Clan→Sachet S N):Prop where
 crisp: Relic S N ν wΩ V
 one:∀y:J,(∀p:E4,V.orbit.translation p y=y)→∃z:ℂ,y=z • (qΩ).val
 primitive:∀ t:N.Chip,∃Y,P.Bought 3 ξ (letter N t) Y

 entry:∀j, (d j).val=D j
 earlier:∀j,op (twin S N (d j)) (att F) ∈
       Cirrus.PavilionM.Hull Z qΩ H' Set.univ (tsupport ⇑(att F))
 later:∀j,op (d j) (att U) ∈ Cirrus.PavilionM.Hull Z qΩ H' Set.univ (tsupport ⇑(att U))
 mink:∀i j,P.minkPrice x D F U i j=
    inner ℂ (lens qv) (lens (op (twin S N (d i)) (att F) (op (d j) (att U) qv)))
 -- E Eu quotes via Bool pair
 eu:∀p q:Vantage,p 3<q 3→∀i j,P.euPrice x D p q i j=quoteL Z (qΩ).val
    (usher (side S N ν (twin S N (d i))) (side S N ν (d j))) (spY 3 (usher p q))
    (fun k=>usher p q k 3) [false,true]

variable (D:P.Cilium x)(F U:SampleDose)(V:P.Vh x N)(d:Lead.Clan→Sachet (P.seasons 3 (P.advocate 3 x 3)) N)
  (q:Relic (P.seasons 3 (P.advocate 3 x 3)) N (P.nv _ _) (P.nova _ _) V)
  (e:∀j,(d j).val=D j)
include q e
local notation "mearlier" z:max=>op (twin S N (d z)) (att F)
local notation "mlater" z:max=>op (d z) (att U)
lemma mink_on (i j:Lead.Clan):P.minkPrice x D F U i j=
    inner ℂ (lens qv) (lens ((mearlier i) ((mlater j) qv))):= by
 rw [P.mink_is]

 change _=inner ℂ (Door S N ν wΩ qv).val (Door S N ν wΩ ((mearlier i) ((mlater j) qv))).val
 rw [q.sold,q.sold,q.init,← e i, ← e j]; rfl
lemma eu_on (p t:Vantage)(h:p 3<t 3)(i j:Lead.Clan):
 P.euPrice x D p t i j=quoteL Z (qΩ).val
    (usher (side S N ν (twin S N (d i))) (side S N ν (d j))) (spY 3 (usher p t))
    (fun k=>usher p t k 3) [false,true]:=by
 let v:= usher (twin S N (d i)) (d j)
 have w:= q.wordEuro Bool v (spY 3 (usher p t)) (fun k=>usher p t k 3) [false,true]
                     (List.pairwise_pair.mpr h)
 have α:=congrArg (fun f=>quoteL Z (qΩ).val f (spY 3 (usher p t)) (fun k=> usher p t k 3) [false,true])
       (show usher (side S N ν (twin S N (d i))) (side S N ν (d j))=
         (fun k=>side S N ν (v k)) by funext b;cases b<;>rfl)
 have β:=congrArg (fun f=> quoteL S Ω f (spY 3 (usher p t)) (fun k=>usher p t k 3) [false,true])
       (show (fun b=>(v b).val)=usher (D i).dagger (D j) by rw [← e i,← e j];funext b;cases b<;>rfl)
 exact (α.trans (w.trans β)).symm

lemma aboard (o:Anchor S Ω)(g:∀t:N.Chip,∃Y,P.Bought 3 ξ (letter N t) Y):
   P.Board x N D F U V d:=
   ⟨q,q.anchorTransfer o,g,e,fun i=>q.per_net _ _ (att_compact ..),
      fun i=>q.per_net _ _ (att_compact ..),P.mink_on x N D F U V d q e,P.eu_on x N D V d q e⟩
#print axioms aboard
