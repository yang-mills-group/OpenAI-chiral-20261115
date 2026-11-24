import YM.SU5.Registration.Heave.Depots
import YM.SU5.Registration.Heave.FlowAt
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets Drums
/-! # Time-jet payment, recursive actual stencil. Every power is at the SAME height.

Break into one-tick difference, t/2 gap must also be granted on the current
priced operator (not just its limiting predecessor or on the uncolored system).
Use the result at EACH strictly positive t, for every point and spacetime cap
estimates. The proportional bills below are polynomial in the allowance.
-/
variable (P:Spine)(A:P.Apron)(x:P.Spectrum0 3)
local notation "ε"=> P.advocate 3 x 3
local notation "θ"=>(3:Axis)
local notation "U"=> P.ColorHil θ ε
local notation "G"=> P.ManyF θ ε
local notation "w"=>A.u θ
local notation "v"=>A.allowance P θ
local notation "s"=> A.s
local notation "S"=>P.physicalEnergy θ ε
local notation "E"=>P.seasons θ ε
local notation "SH"=> (P.physicalEnergy θ ε).E
local notation "EH"=> (P.seasons θ ε).E
local notation "M" x:max k:max=> whenly (timeMesh P.par) x k
local notation "d"=>P.burst s

/-- exact one-tick (same ruler in all orientations of this experiment). -/
def drumStep : P.Apron where
    «s»:=A.s
    u:=fun i=> A.u i+1
    pos:=fun _=> by omega
    F:= P.tubaField A.s A.F 1
    «S»:= P.tubaStencil A.S 1
    bay:= P.tuba_bay A.s A.F 1 A.S A.bay
    realM:= P.tuba_real A.s A.F 1 A.realM
    shelter j:= P.tubaShelter j (A.shelter j) 1
local notation "B"=> P.drumStep A
lemma step_s (j:Axis): (B).allowance P j = A.allowance P j+ d:= when_add ..
lemma step_price (t:ℝ≥0)(p:(P.drumStep A).allowance P θ ≤ t): P.stageH θ ε (P.drumStep A) t t = (duration d)⁻¹ • (P.stageH θ ε A (t+d) (t-d) - P.stageH θ ε A t t):=by
 let K₀:= P.shifts θ (1:ℕ) A.F
 let v₀:= (B).u θ
 have h:v₀= w+1:=rfl
 let q:= add_pos ((B).pos θ) ((B).pos θ)
 have hu: A.zoom P s θ+ 1 ≤ v₀:=by rw [Apron.zoom_at,h]
 let k:= P.shifted_deposit θ ε s v₀ q A 1 le_rfl hu; let r:= P.leaf_deposit θ ε s v₀ q A le_rfl (by omega); rw [A.full_at] at k r
 let W:= (k.sub P θ ε s v₀ q r).scale P θ ε s v₀ q (duration d)⁻¹
 exact P.deposit_at_finger θ ε (B) W t p
lemma step_price_G (t:ℝ≥0)(p:(P.drumStep A).allowance P θ ≤ t): P.stageG θ ε (P.drumStep A) t t = (duration d)⁻¹ • (P.stageG θ ε A (t+d) (t-d) - P.stageG θ ε A t t):=by
 unfold stageG; rw [P.step_price A x t p,map_smul,map_sub]
private lemma air_weights (t:ℝ≥0)(p:(P.drumStep A).allowance P θ ≤ t/2) :
    A.allowance P θ ≤ t ∧ v ≤ t-d ∧ v ≤ t/2 ∧ v ≤ t/2-d ∧ d≤t ∧
    t/2-d≤ t-d ∧ t-d-(t/2-d)=t/2∧t/2≤ t ∧ t-t/2=t/2 :=by
 let x' := v; let z:=t/2
 rw [step_s P A θ] at p; have hx:d ≤ z:= by exact le_trans (_root_.le_add_of_nonneg_left (show 0 ≤ v from zero_le)) p
 have hc:z≤t:= half_le_self (zero_le); have he:d≤t:= le_trans hx hc
 have hp:v ≤ z-d:= (le_tsub_iff_right hx).2 p
 have hK:v ≤ z:=(le_add_of_nonneg_right (show 0 ≤ d from zero_le)|>.trans p)
 have hz:t-z=z:= by rw [show t-z=z+z-z from congrArg (·-z) (_root_.add_halves t).symm,add_tsub_cancel_right]
 refine ⟨hK.trans hc,hp.trans (by gcongr),hK,hp,he,tsub_le_tsub_right hc _,?_,hc,hz⟩
 exact (show t-d-(z-d)= t-z from by rw [←add_tsub_add_eq_tsub_right (t-d) d (z-d),tsub_add_cancel_of_le hx, tsub_add_cancel_of_le he]).trans hz

local notation "C"=> P.stageH θ ε A
local notation "D"=> P.stageG θ ε A
-- factored step with enough room reduce
lemma conducts (t:ℝ≥0)(p:(P.drumStep A).allowance P θ ≤ t/2) : P.stageH θ ε (P.drumStep A) t t= action (S) (t/2) (mesh_diff (S) d * SH (t/2)) (C (t/2) (t/2-d)) := by
 obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩:= air_weights P A t p
 have he:t+d-t=d:= add_tsub_cancel_left ..
 have hx: t-(t-d)=d:= tsub_tsub_cancel_of_le h5 -- `tsub_tsub_self`
 let y:= t/2; have hf: C t (t-d)= SH y*C y (y-d)*SH y:=by rw [P.stage_more θ ε A h3 h8 h4 h6,h7,h9]
 rw [P.step_price A x t (p.trans h8)]
 have hp:C (t+d) (t-d)=SH d * C t (t-d):=by rw [P.stage_more θ ε A h1 (show t ≤ t+d from le_add_of_nonneg_right (zero_le)) h2 (le_refl (t-d)), tsub_self,he,show SH 0=(1:(U).Op) from (S).eZero,mul_one]
 have hv:C t t= C t (t-d)* SH d:=by rw [P.stage_more θ ε A h1 le_rfl h2 (show t-d≤t from tsub_le_self), tsub_self,hx,show SH 0=(1:(U).Op) from (S).eZero,one_mul]
 rw [hp,hv,hf]; exact raw_action ..
lemma conductsG (t:ℝ≥0)(p:(P.drumStep A).allowance P θ ≤ t/2) : P.stageG θ ε (P.drumStep A) t t= action (E) (t/2) (mesh_diff (E) d * EH (t/2)) (D (t/2) (t/2-d)) := by
 -- mirror algebra using G-Rules; prices paid on respective charge kernels even after moving gaps
 obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩:= air_weights P A t p
 have he:t+d-t=d:= add_tsub_cancel_left ..
 have hx: t-(t-d)=d:= tsub_tsub_cancel_of_le h5
 let y:= t/2; have hf: D t (t-d)= EH y*D y (y-d)*EH y:=by rw [P.toGlate x A h3 h8 h4 h6,h7,h9]
 rw [P.step_price_G A x t (p.trans h8)]
 have hp:D (t+d) (t-d)=EH d * D t (t-d):=by rw [P.toGlate x A h1 (show t ≤ t+d from le_add_of_nonneg_right (zero_le)) h2 (le_refl (t-d)), tsub_self,he,show EH 0=(1:(G).Op) from (E).eZero,mul_one]
 have hv:D t t= D t (t-d)* EH d:=by rw [P.toGlate x A h1 le_rfl h2 (show t-d≤t from tsub_le_self), tsub_self,hx,show EH 0=(1:(G).Op) from (E).eZero,one_mul]
 rw [hp,hv,hf]; exact raw_action ..
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.conductsG
#print axioms Spine.conducts
