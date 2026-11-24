import SatinPP.Cochere

set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
open Germ Alliance Selected FirstWindows

variable (j:Axis)
local notation "C" => P.room
local notation "χ"=>P.chateau x j
local notation "L"=>P.sitting x j
local notation "ξ"=>P.advocate 3 x j
local notation "H"=>P.ColorHil j (P.advocate 3 x j)
local notation "B" s:max f:max=> Selected.bud P.run P.large P.law s P.history P.projection.clipped j false (C j) (χ) f
local notation "ℱ"=>P.voxTest j

local notation "R"=>P.revolving x j
local notation "Θ"=>P.physicalEnergy j (P.advocate 3 x j)
local notation "δ"=>Selected.ride P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)
local notation "M"=>timeMesh P.par
local notation "ℛ"=>P.voyageF j ξ
local notation "ℛ'"=>turnstile P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)

open ConePrice SelectionAnalysis
abbrev nativesFull:= P.Viewers j ξ=⊤ ∧ P.DayStar x j
abbrev glitter:=mainsea P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)
local notation "o"=>P.glitter x j
def centerbelt: Sunbelt j (MeshClock.marks (timeMesh P.par)) (P.ColorHil j (P.advocate 3 x j)) where
 track:=ℛ
 list:=Tower.look j
 traverses:= (o).traverses
 unique_list:= (o).unique_list
 heat _:=0
 smooth _:=continuous_const
 diffusion _:=continuous_const
local notation "y"=>P.centerbelt x j
lemma nativ_press(e:ℝ)(a:0<e) :
 P.nativesFull x j ↔ GridHeat (Θ) (y) e :=
 (operator_pressure (Θ) (daylight M) (y) (P.colorMoveE j ξ) a).symm

lemma play_gate(m:Axis→ MeshClock.marks (timeMesh P.par))(u:H):
 R (transverse_play (y) m u)=transverse_play (o) m (R u):= P.spins_raw x j (Tower.look j) _ _
lemma gild_press(e:ℝ):
 GridHeat (Θ) (y) e ↔ GridHeat (δ) (o) e := by
   unfold GridHeat
   apply forall_congr';intro m
   apply imp_congr_right; intro _
   refine ((R).surjective.forall (p:=fun u:L=>
      let t:=(face m j).toNNReal
      ‖(δ).E t (transverse_play (o) m u) - (δ).E t u‖ ≤ ‖u-(δ).E t u‖)).trans ?_ |>.symm
   refine forall_congr' fun i=>?_
   dsimp only
   simp only [←P.play_gate, ←P.spins_heat, ← map_sub,LinearIsometryEquiv.norm_map]
#print axioms nativ_press
#check Function.Surjective.forall

open LightBudget
abbrev baking:= BoostBacking P.run P.large P.law P.projection P.room 3 (P.glasshouseCharacter 3 x)
abbrev breathG:= saunters P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)=⊤∧
   Forward (peninsula P.run P.large P.law P.history P.projection.clipped j false (C j) (χ))

lemma house_keeps_axis :
 P.nativesFull x j ↔ P.breathG x j:=
 (P.nativ_press x j 1 zero_lt_one).trans ((P.gild_press x j 1).trans
   (operator_pressure (δ) (daylight M) (o)
     (follows_road P.run P.large P.law P.history P.projection.clipped j false (C j) (χ))
     zero_lt_one))
/-- Matching the exact requested arguments (no assumption on P,x, election not repeated). -/
lemma aisle : P.baking x ↔ ∀ i,P.nativesFull x i:=by
 constructor
 · intro h i
   exact (P.house_keeps_axis x i).mpr ⟨h.present _,h.forward _⟩
 intro h
 refine (real_boost_purchase P.run P.large P.law P.projection P.room 3 (P.glasshouseCharacter 3 x) (show 0≤(0:ℝ) from le_rfl) zero_lt_one).mp ⟨fun i=>?_⟩
 exact twoShotPays _ _ _ _ _ _ _ <| (LightBudget.true_spectrum P.run P.large P.law P.projection i (C i) _ le_rfl zero_lt_one).mpr ((house_keeps_axis _ _ i).mp (h i))
#print axioms aisle
