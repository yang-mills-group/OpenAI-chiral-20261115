import ZecaPere
import ZecaClip
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
variable {ι:Type}(N:P.Tent x ι)
local notation "wΩ"=>P.nova 3 ξ
local notation "J"=>Grotto S N Ω
local notation "H'"=> chapel S N Ω
local notation "Z"=>springs S N Ω
local notation "qΩ"=> saint S N ν wΩ
local notation "op"=>mast S N ν wΩ
local notation "qv"=>mastV S N ν wΩ
local notation "lens"=>(H').lens Z qΩ

local notation "Γ"=>Sachet S N

structure ZecaTrellis (D:P.Cilium x)(F U:SampleDose)(d:Lead.Clan→Sachet S N):Prop where
 crisp: Trinket S N ν wΩ
 one: Anchor Z (qΩ).val

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

variable (D:P.Cilium x)(F U:SampleDose)(d:Lead.Clan→Sachet (P.seasons 3 (P.advocate 3 x 3)) N)
  (q:Trinket (P.seasons 3 (P.advocate 3 x 3)) N (P.nv _ _) (P.nova _ _))
  (e:∀j,(d j).val=D j)
include q e
local notation "mearlier" z:max=>op (twin S N (d z)) (att F)
local notation "mlater" z:max=>op (d z) (att U)
lemma mink_on0 (i j:Lead.Clan):P.minkPrice x D F U i j=
    inner ℂ (lens qv) (lens ((mearlier i) ((mlater j) qv))):= by
 rw [P.mink_is]

 change _=inner ℂ (Door S N ν wΩ qv).val (Door S N ν wΩ ((mearlier i) ((mlater j) qv))).val
 rw [q.sold,q.sold,q.init,← e i, ← e j]; rfl
lemma eu_on0 (p t:Vantage)(h:p 3<t 3)(i j:Lead.Clan):
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

lemma resting0 (o:Anchor S Ω):
   P.ZecaTrellis x N D F U d:=
   ⟨q,q.anchorTransfer o,e,fun i=>q.per_net _ _ (att_compact ..),
      fun i=>q.per_net _ _ (att_compact ..),P.mink_on0 x N D F U d q e,P.eu_on0 x N D d q e⟩
#print axioms resting0

omit q e
variable {K:P.Register}{c r:ℕ→ℕ}{R:P.Ellis 3 x}{i₀:ℕ}
 {A:ℕ→P.Apron}{n:ℕ→ℕ}{w:Lead.Clan→Prism}
 {V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j)}
 {g h:ℕ}{X:P.HandleWith x c r A n}
def Stay (B: MH G):Prop:=
 (∀j,(D j).Copy S B) ∧ (∃ d,P.ZecaTrellis x (Quadra B) D F U d)
lemma stay
  (p:P.Shell K c r x R i₀ F U A n w V g h X D) (B: MH G)
  (price:P.Bought 3 ξ B A) :
      P.Stay x D F U B:=by
  have uni:‖(ν).val‖=1:=P.stone_norm ..
  have t:=P.Flares x A p.silver.found price
  have b(i:Lead.Clan):Paid S (Quadra B) (D i):=
     ⟨qPrimary B,(qPrice B).symm ▸ t i⟩ -- subst B inside? try refine
  exact ⟨t,_,P.resting0 x (Quadra B) D F U
     (fun i=>⟨_, b i⟩) (trinket S _ ν wΩ uni)
     (fun _=>rfl) (P.anchorShelf x p)⟩
#print axioms stay
