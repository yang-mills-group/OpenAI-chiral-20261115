import YM.SU5.Reconstruction.Trap.Rebate
import YM.SU5.Reconstruction.Cone.Affords
/-!
# Pose measurements which exactly orient pressure
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "ψ"=> marks (timeMesh Λ)
local notation "θ"=> gram j (tent Y H)
local notation "aU"=> shop j (tent Y H)
local notation "bF"=> floor j (tent Y H)
/-- JUST grid displacing (+z,+z) one axis. v transverse. Arbitrarily tiny only.
Don't require read anything at separate z₁ and z₂ displacements or inequality all real, even
when ground-state budgets at nearby positions not presently available. -/
def Ivory (r e:ℝ) : Prop:= ∀ (a:Axis)(_:a≠j)(z:ψ), 0<(z:ℝ)→(z:ℝ)<e → let t:= Picket.byStamp j a z
                                                                            ∀ f:Sky (tent Y H), f∈Domain Y H G true (flank j r) →
                                                                              ∀ (k₁ : θ (aU t f)∈ Domain Y H G false univ) (k₂ : θ (bF t f)∈ Domain Y H G false univ),
                                                                               ( (F) ⟨θ (aU t f),k₁⟩).re ≤ ( (F) ⟨θ (bF t f),k₂⟩).re
variable {r e:ℝ}
lemma ivory_equiv (p:0≤r): Ivory Y H V G j C χ r e ↔ Picket.PacePrice (L) (Ω₀) e:=by
 constructor
 · intro t a z h hz x; let w:=Picket.byStamp j a z; let d:=(coordinates Λ w j).toNNReal; have hp : coordinates Λ w∈ ConePrice.CostDomain j e:= Picket.starch (Ω₀) a z h hz
   let Eq x:=(L).E d x; let S₀:= ConePrice.transverse_play (Ω₀) w
   let T:={x : J₀|‖Eq (S₀ x)-Eq x‖≤ ‖x-Eq x‖}
   have hE: Continuous Eq:= ((L).E _).continuous
   have hT: IsClosed T:= isClosed_le (((hE.comp S₀.continuous).sub hE).norm) ((continuous_id.sub hE).norm)
   refine closure_minimal ?_ hT (TimeMesh.dense_flanks Y H V G j C χ r x)
   rintro _ ⟨f,k,v,rfl⟩; obtain ⟨g,g'⟩:= pressure_coverage Y H V G j w f k p hp
   let h1:=domain_loose Y H G _ g; let h2:= domain_loose Y H G _ g'; exact (pressure_test Y H V G j C χ f w hp.1.le v h1 h2).1 (t a a.property z h hz _ k h1 h2)
 intro h a b z t e y f s k k'; let v:= (Picket.starch (Ω₀) ⟨a,b⟩ z t e); refine (pressure_test Y H V G j C χ f _ v.1.le (domain_mono Y H G (TimeMesh.flank_mono j p) s) k k').2 (h ⟨a,b⟩ z t e _)
lemma twoShotPays (h:TwoShot Y H V G j C χ r e): Ivory Y H V G j C χ r e := fun a v z p q f b => h (Picket.byStamp j a z) (Picket.starch (Ω₀) ⟨a,v⟩ z p q) _ b
variable (p:0≤r)(v:0<e)(h: Ivory Y H V G j C χ r e)
include h v p
lemma grants: saunters Y H V G.history G.clipped j false C χ=⊤ ∧ ∀ a:Axis,a≠ j→ Picket.Paces a (peninsula Y H V G.history G.clipped j false C χ):=by
 let t:= (ivory_equiv Y H V G j C χ p).1 h
 have hu:= follows_road Y H V G.history G.clipped j false C χ
 exact ⟨Picket.cost_room (L) (Ω₀) hu v t,fun a p=> Picket.cost_paces (L) (daylight Gt) (Ω₀) hu v t ⟨a,p⟩⟩
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
