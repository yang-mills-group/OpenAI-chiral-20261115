import ZecaArgon
import ZecaCP4
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


variable (T:P.Shiver x N)(Y:N.Chip→ℕ→P.Apron)(a:N.Chip)(B:Gilt.Regime)

/-- Caution: These estimates, especially `angular`, are inputs still needing proof. -/
structure Coronation (A:ℕ→P.Apron):Prop where
 letter: P.Bought 3 (P.advocate 3 x 3) (Monument.letter N a) A
 full: P.Regalia x N T Y
 angular: P.RawArch x N Y B


lemma regalia_buy (H:P.Regalia x N T Y)(u:N.Chip):
 P.Bought 3 ξ (letter N u) (Y u):=by
 rw [show letter N u=Gilt.coin (K:=P.Retinue x) N T timeAxis u from ?_]
 · exact H.buys 3 u
 unfold Gilt.coin; rw [Gem.usea];rfl

lemma ruby_hat(R:P.Ellis 3 x) (L:P.Coronation x N T Y a B A):
 N.Tile S ν := Gem.tileR (K:=P.Retinue x) _ _ _ _ _ rfl
    ((arch_real B R L.full).mp L.angular)

theorem ruby_claim
      (p:P.Shell K c r x R i₀ F U A n w V g h X D)
      (L:P.Coronation x N T Y a B A):
     ∃ V d,P.Board x N D F U V d :=
   P.Peg x N p (ruby_hat P x N T Y a B R L) a (fun u=>⟨_,regalia_buy P x N T Y L.full u⟩) L.letter

#print axioms ruby_claim
