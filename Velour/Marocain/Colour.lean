
import Velour.Marocain.Trooping
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 110000
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
open Boundary Probe

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "D"=> (Σ₁).muslin
local notation "Φ"=> (Σ₁).Detector
local notation "U"=> (Σ₁).unit.translation
local notation "Ω"=> P.heaven j x



variable {n:ℕ}
local notation "s"=>P.seasons j x
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝒜" => Fin n → P.Bobbin j x
local notation "𝒦" => Fin n → ℕ
local notation "𝓙" => Joint n


theorem troop_estimate (b:𝒜):
 ∃(d:𝒦)(A:Fin n→ℝ),∀ (l r:𝓛)(F:Joint n)(p:ℕ)(z:D),
   ‖(s).weight p (P.troop j x b l r F z)‖ ≤ wingSpan j d p A F * ‖(s).weight (sheaf d+p) z‖:=by
 let h:=P.bobToast j x b
 have g:=(P.bobToast j x b)
 choose k X t using g
 exact ⟨k, fun i=>‖X i‖,
     cortege_cost h t (fun _=>le_refl _)⟩


theorem march_whole (b:𝒜) (m:∀i,(b i).Joint)
 {L J:ℕ→Fin n→ℝ≥0}{l r:𝓛}
 {k:ℕ→Fin n→ℕ}(p:∀a,Tendsto (fun i=>k i a) atTop atTop)
 (e:Tendsto L atTop (𝓝 l))(g:Tendsto J atTop (𝓝 r))
 {V:ℕ→Joint n}{F:Joint n}(t:Tendsto V atTop (𝓝 F)):
 (s).Surges atTop (fun i=>P.follow j x b (k i) (L i) (J i) (V i)) (P.troop j x b l r F):=by
 choose d A X h using (fun i=>(m i).receives)
 exact surge_ribs h (P.bobToast j x b) (fun i=> (b i).ribbon.delivery) p e g t



theorem follow_estimate (b:𝒜) (m:∀i,(b i).Joint):
 ∃(d:𝒦)(A:Fin n→ℝ),∀ (l r:𝓛)(F:Joint n)(p:ℕ)(z:D)(k:𝒦),
   ‖(s).weight p (P.follow j x b k l r F z)‖ ≤ wingSpan j d p A F * ‖(s).weight (sheaf d+p) z‖:=by
 choose d A X h using (fun i=>(m i).receives)
 exact ⟨d,A,fun l r F p z k=> wings_width h l r k F p z⟩

#print axioms march_whole
#print axioms follow_estimate
end Spine

