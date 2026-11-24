import ZecaSilver
import ZecaAureole
import SatinThinQuizMargin
import ZecaSlip
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


variable (D:Cilium P x)
 (b:∀i, P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i))

local notation "ℒ"=>Lead.Clan

variable (U W:Doorway)(K:P.Register)(μ:ℝ)(uc:U.upper 3≤ -μ)(wc:μ≤W.lower 3)
 (m:0<μ)


include uc wc m
lemma silverware
 (a:P.Aureole x A c r n)(ga:P.GalaxyShow x g h A V)
 (l:∀w,P.ThinArmada x A c r n w T V g h)(B:P.Experiment K c r x J)
 (e:U.Later W thinAlongOrder 0):
  ∀ᶠ i:ℕ in atTop, ∃ (F L:SampleDose)(w:ℒ→Prism)(D:P.Cilium x),
 P.FullPrismLab x A c r n w V g h T μ F L U W (c i) (r i) K ∧
 P.Silver x A c r n w V D U W μ F L:=by
 have t:= P.ordersPrism x g h V μ ga J K U.spare W.spare (U.spareLater e)
   ((U.sparesU _).le.trans uc) (wc.trans (W.sparesL _).le)
   B m
 have a':=limit_width B.launch

 filter_upwards [t, (a' 3).eventually (gt_mem_nhds m),U.spareCosts _ a', W.spareCosts _ a', B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i qi d j k y
 have f:= (show U.upper 3+P.probeWidth (c i) (r i) 3<0 by linarith only [uc,show P.probeWidth (c i) (r i) 3< μ from d])
 have p:= (show 0+P.probeWidth (c i) (r i) 3<W.lower 3 by linarith only [wc,show P.probeWidth (c i) (r i) 3< μ from d])

 obtain ⟨_,_,w,r'⟩:=qi
 obtain ⟨s',u₁,k',u₂,_,_,_,v₂,v₁⟩:=r'.centers
 obtain ⟨M,l₁,l₂⟩:=P.mintage x A c r n w a
 obtain ⟨F,L,H,m',l',w'⟩:=P.zecaEncore x A c r n w V g h T (l w) J M l₁
    U W K μ uc wc m _ _ y f p j k s' k' u₁ u₂ v₁ v₂
 exact ⟨F,L,w,M, P.honorLab x A c r n w V g h T (l w) J μ F L U W _ _ K e uc wc H,
  P.yields x A c r n w V g h T (l w) J M l₁ U W μ uc wc m F L l₂ l' w' H.read m'⟩
#print axioms silverware
#check @silverware
