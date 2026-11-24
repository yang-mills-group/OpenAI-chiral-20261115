import Prism.Tap
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Py Heat

local notation "K"=> tent Y h
-- header from Wake check missing
variable {P:Preparation}{l:ℕ}(a:Course P (VolumeCape.Dream.Nimbus l))(s:ℕ)
lemma circumvol (A D:ℝ)(p:0<D): ∀ᶠ k in atTop, ∀ i:ℕ,∀ h:(a.voyage i).kick≤k, Ferry a s i k∧ ∀ F:Mark (side a i s), Envelope F →(∀ x,‖F x‖ ≤ Real.exp (A * game (a.ir i)))→ ‖compass a i k s F - solder a i k h s F‖≤D :=by
 filter_upwards [ferry_all a s, a.UV.tendsto_atTop.eventually (Decaf.topdeck a.meter P.C a.τ A s P.b _ p)] with k w W i h
 let Z:=w i h
 refine ⟨Z,fun F f g=>?_⟩
 have ht:= mark_pay ((a.voyage i).ownership s |>.paid.bill) f
 exact (Z.fire.mark_bound _ _ ht.meas (fun x=> g _)).2.2.trans (W _ ((a.voyage i).domain k h))
#check Mark
#print axioms circumvol
end YM.CF.Buffered.Afterglow.Journey
end
