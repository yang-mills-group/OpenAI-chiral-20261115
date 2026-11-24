import SatinPP.Equerry
import SatinPP.Splay
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
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
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

local notation "H"=> P.ColorHil 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Δ"=> P.truck 3 ξ
local notation "ω"=> P.colorZero 3 ξ

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:ℒ→ Prism)(g h:ℕ)
variable (T:P.HandleWith x c r A n)
local notation "W"=> P.soldTrumpet A c r n w
local notation "B[" a "," i "]"=> P.sold_birth x A c r n w a i T
local notation "η"=>P.enter 3 ξ

variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)
variable (b:Bool)(q:ℝ)(F:SampleDose)
local notation "Xᵦ"=>P.pastureGrid x A c r n w T b
local notation "ν"=>P.wave x V w b q
include R J
omit R J
local notation "𝒱"=>P.WalkVoucher x V
/-- Original review boxes, at wall 0. `P.hardRide` uses physical
macro-mesh velocities. No assertion more finely than this run's consultation height. -/
structure Porch_LocalFieldBounds (F U:SampleDose) (d ϵ:ℝ) :Prop where
  nearer: P.SoftRide x (P.wave x V w false 1 F) d ϵ
  farther: P.SoftRide x (P.wave x V w true 1 U) d ϵ
  furnished:∀ᶠ i in atTop,∀t≥ c (n i),
    (∀a:ℒ,
      (∃ k:P.Test,P.reflectTest 3 k=P.prepared t ((W a i).kiss P 3) F ∧
        ∃e:P.birthF 3 t k,P.viewF 3 (P.advocate 3 x 3) t e=P.pastureGrid x A c r n w T false F i t a) ∧
      (∃ e:P.birthF 3 t (P.prepared t (W a i) U), P.viewF 3 (P.advocate 3 x 3) t e =
          P.pastureGrid x A c r n w T true U i t a)) ∧
    P.HardRide x (P.pastureGrid x A c r n w T false F i t) t d ϵ ∧
    P.HardRide x (P.pastureGrid x A c r n w T true U i t) t d ϵ

include R J
lemma hostPorch {K:P.Register}(C:P.Experiment K c r x J)
  (U:SampleDose)(y:𝒱 w F U):
 ∃ d>0, ∃ e>0,P.Porch_LocalFieldBounds x V A c r n w T F U d e:=by
 obtain ⟨q₀,d,h₀,z,r',f,p,p₁,p₂,p₃,Y,Z,W₀,W₁⟩:=y
 have q':0<q₀:=zero_lt_one.trans_le p
 obtain ⟨v₀,t₀,A₀⟩:=P.soft_arch x V A c r n w g h T R false q₀ F p₁ p₂ Y.wall q' W₀ p₃ p
 obtain ⟨v₁,t₁,A₁⟩:=P.soft_arch x V A c r n w g h T R true q₀ U p₁ p₂ Z.wall q' W₁ p₃ p
 obtain ⟨v₂,t₂,A₂⟩:=P.hard_arch x V A c r n w g h T R J false q₀ F p₁ p₂ q' W₀ p₃ f Y
 obtain ⟨v₃,t₃,A₃⟩:=P.hard_arch x V A c r n w g h T R J true q₀ U p₁ p₂ q' W₁ p₃ f Z
 let e:=min (min v₀ v₁) (min v₂ v₃)
 have t:0<e∧e≤v₀∧e≤v₁∧e≤v₂∧e≤v₃:= ⟨by unfold e; positivity,
  (min_le_left ..).trans (min_le_left ..),
  (min_le_left ..).trans (min_le_right ..),
  (min_le_right ..).trans (min_le_left ..),
  (min_le_right ..).trans (min_le_right ..)⟩

 obtain ⟨te,u₀,u₁,u₂,u₃⟩:=t
 refine ⟨d,p₁,e,te,⟨fun j j₀ l l₀ le'=>A₀ j j₀ l l₀ (le'.trans u₀),fun j j₀ l l₀ le'=>A₁ j j₀ l l₀ (le'.trans u₁),?_⟩⟩
 have T':∀ᶠ i in atTop,∀a:ℒ,(W a i).realWidth P 3<q₀:=eventually_all.mpr fun a=>
    (R.slender a 3).eventually (gt_mem_nhds q')
 filter_upwards [A₂,A₃,T'] with i H₀ H₁ Y₁ t' u
 have le' : i ≤ t':= (C.launch.smaller.comp T.fast).le_apply.trans u
 refine ⟨fun a=>?_,fun j j₀ l l₀ ht=> H₀ t' le' j j₀ l l₀ (ht.trans u₂),
    fun j j₀ l l₀ ht=> H₁ t' le' j j₀ l l₀ (ht.trans u₃)⟩

 exact ⟨P.thin_grid_flip x t' _ B[a,i] F (fun p t''=>by
    have Y₀ :q₀≤ -(p 3):= Y.wall p t''
    change p 3+(W a i).realWidth P 3 < 0 -- tune
    linarith only [Y₀,Y₁ a]) u,
    P.thin_grid_view x t' _ B[a,i] U (fun p t''=>by
    have Z₀:q₀≤p 3:=Z.wall p t''
    exact lt_of_eq_of_lt (zero_add _) ((Y₁ a).trans_le Z₀)) u⟩
#print axioms hostPorch
