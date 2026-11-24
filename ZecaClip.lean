import ZecaBoard
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 125000
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

variable (P:Spine){K:P.Register}{c r:ℕ→ℕ}(x:P.Spectrum0 3){R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}
 {A:ℕ→P.Apron}{n:ℕ→ℕ}{w:Lead.Clan→Prism}
 {V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j)}
 {g h:ℕ}{X:P.HandleWith x c r A n}{D:P.Cilium x}



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


variable (p:P.Shell K c r x R i₀ F U A n w V g h X D)
include p
omit p in lemma anchorOld (w:P.lodestarHere 3 (P.advocate 3 x 3)):
 Anchor S Ω:=by
  intro y q
  have a:∀t:ℝ,(S).edge t y=y:=fun t=>
      (DFunLike.congr_fun (Hierarchy.Seld.timeslot S t).symm y).trans (q _)
  have b:∀u:OS.Cross 3,(S).U u y=y:=fun u=>
      (DFunLike.congr_fun (Hierarchy.Seld.laneslot S u).symm y).trans (q _)
  obtain ⟨z,e⟩:=Submodule.mem_span_singleton.mp ((P.heavenRank 3 _ w y).mpr ⟨a,b⟩)
  exact ⟨z,e.symm⟩


lemma anchorHere:P.lodestarHere 3 ξ := by
  let w:=p.scores.native.2.1
  have t: SixElection P K x c r:= ⟨w.launch,w.ready,w.ground⟩
  exact t.star_carrier
lemma anchorShelf: Anchor S Ω:= anchorOld P x (anchorHere P x p)
theorem Peg (d: N.Tile S ν)
    (a:N.Chip)
    (paid:∀ t:N.Chip,∃Y,P.Bought 3 ξ (letter N t) Y)
    (price:P.Bought 3 ξ (letter N a) A) :
    ∃ V d,P.Board x N D F U V d:=by
  have uni:‖(ν).val‖=1:=P.stone_norm ..
  obtain ⟨V,h⟩:=relic (S) N ν wΩ uni d
  have b(t:Lead.Clan):Paid S N (D t):=
       ⟨a,P.Flares x A p.silver.found price t⟩
  exact ⟨V,_,P.aboard x N D F U V (fun t=>⟨_,b t⟩) h (fun _=>rfl) (P.anchorShelf x p) paid⟩
#print axioms Peg
