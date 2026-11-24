import ZecaCell
import SatinThinQuizPair
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

variable (A:ℕ→P.Apron) (c r n:ℕ→ℕ) (w:Lead.Clan→Prism)
 (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
 (T:P.HandleWith x c r A n)(R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)

abbrev Cilium (P:Spine)(x:P.Spectrum0 3):= Lead.Clan → Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3))
variable (D:Cilium P x)
 (b:∀i, P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i))

local notation "ℒ"=>Lead.Clan

/-- exact wick kern of real fields (field for z1 dagger,
field for z2 plain). Arguments on p3<q3 ONLY. -/
def euPrice (p q:Vantage): CrossRead:=
 let u:=usher p q
 Matrix.of (fun z1 z2:Lead.Clan=>
    quoteL S Ω (usher (D z1).dagger (D z2))
      (spY 3 u) (fun i=> u i 3)
      [false,true])

def euRead (F U:SampleDose) : CrossRead:=
 Matrix.of (fun z1 z2:Lead.Clan=>
   ∫ p:Vantage, ∫ q:Vantage,(F.val p:ℂ)*(U.val q:ℂ)*P.euPrice x D p q z1 z2)

local notation "W"=> P.soldTrumpet A c r n w
local notation "B" z:max i:max=>P.sold_birth x A c r n w z i T

include R b

lemma euProfile(z:ℒ)(t:ℝ)(p:0<t) :
 P.profilesZ x V w z t = parabola S (D z).n t ((D z).op Ω):=
 tendsto_nhds_unique (R.heated_points z t p).2
  (P.broodProfile x (D z) _ (fun i=>B z i) (b z).1 t p)

lemma euVac (z:ℒ): WitZero S ν (D z):= P.brood_zero x (D z)
   _ (fun i=> B z i) (b z).1 (R.vacuum z)
include J

lemma euPoint(p q:Vantage)(v:p 3<q 3):
 P.pointPrism x V w (q-p)=P.euPrice x D p q:=by
 ext1 i j
 let d:=usher (D i).dagger (D j)
 let t:=usher p q
 let z:=fun k=>usher ((W i k).kiss P 3) (W j k)
 let l:List Bool:=[false,true]
 have h': Tendsto (fun k=> P.commonWell 3 x (z k) t l) atTop (𝓝 (P.euPrice x D p q i j)) :=
   P.quoteWell 3 x J d z t (fun _=>t) l l .rfl
    (fun a=>match a with
    | false=>(b i).2
    | true=>(b j).1)
    (fun _=> tendsto_const_nhds)
    (List.pairwise_pair.mpr v)
 exact tendsto_nhds_unique (P.illuminate_globe x A c r n w V g h T R J i j v) h'

lemma euLimit (μ:ℝ) (F U:SampleDose) (u:0<μ)
   (i:backwardSite F μ)(j:forwardSite U μ):
 P.readPrism x V w μ F U=P.euRead x D F U:=by
 ext1 r k
 rw [P.illuminate_price x A c _ n w V g h T R μ r k F U u i j]
 refine integral_congr_ae (Eventually.of_forall fun p=>
       integral_congr_ae (Eventually.of_forall fun q=>?_))
 by_cases a:F.val p=0
 · simp [a]
 by_cases e:U.val q=0
 · simp [e]
 dsimp only
 rw [P.euPoint x A c _ n w V g h T R J D b p q (by linarith only [i p (subset_closure a),j q (subset_closure e),u])]
#print axioms euLimit
