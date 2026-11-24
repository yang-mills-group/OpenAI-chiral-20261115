import Mussel.Deck
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Broker
variable (P:Spine)(W:Bool)(s t:ℕ)(i:Cover)(F:SampleDose)
local notation "K₀"=>P.calibration
open Tower.Reconstruction
/-- Product-at-level, two staggered subquestions (main and sensor tail). -/
structure FrameZ where
 mainStem : P.Test
 tailZ : P.Test
 S0 : Finset Cover
 T0 : Finset Cover
 mainPin: mainStem∈bay P.calibration S0 true
 tailPin: tailZ∈bay P.calibration T0 true
 clearF : Disjoint (P.pinFoot s S0) (P.pinFoot s T0)
 tailSense : tailZ∈ P.sensing T0 s W
 mainColor:mainStem∈enclave P.calibration
 tailColor:tailZ∈enclave P.calibration
-- cfg FrameZ order P W s
#check FrameZ
namespace FrameZ
variable {P W s}{D:FrameZ P W s}
def question(D:FrameZ P W s):P.Test:=D.mainStem * D.tailZ
def batch(D:FrameZ P W s):P.Test:=∑ i∈ P.usedGrid t F,P.activation t F i • pilot P s t i D.question
abbrev swept(D:FrameZ P W s):Finset Cover:=fence P s t i (D.S0∪D.T0)
variable (D)
lemma taped : D.question∈ bay K₀ (D.S0∪D.T0) true:=
 Subalgebra.mul_mem _ (tallerBay K₀ _ _ subset_union_left D.mainPin) (tallerBay K₀ _ _ subset_union_right D.tailPin)
lemma destinedU : D.question∈enclave K₀:= Subalgebra.mul_mem _ D.mainColor D.tailColor
lemma fullID : pilot P s t i D.question=pilot P s t i D.mainStem * pilot P s t i D.tailZ:= trailer s t i D.mainPin D.tailPin D.clearF -- tune
lemma in_sweep : pilot P s t i D.question ∈ bay K₀ (D.swept t i) true := tram s t i D.taped
lemma in_charge: pilot P s t i D.question∈ enclave K₀:= P.cruise_color Vacancy.ordinate i (P.refine_keeps s _ D.destinedU _)
lemma pin_commission (p:s ≤ t): Disjoint (P.pinFoot t (fence P s t i D.S0)) (P.pinFoot t (fence P s t i D.T0)) := by
 apply Set.disjoint_left.mpr; intro x a b
 exact Set.disjoint_left.mp D.clearF (stretch s t i p a) (stretch s t i p b)
lemma pin_batch (x:Vantage)(p:s ≤ t)(w:x∈P.pinFoot t (D.swept t i)): x-P.meshPose t i∈P.pinFoot s (D.S0∪D.T0):= stretch s t i p w
lemma in_big: fence P s t i D.T0 ⊆ D.swept t i:= P.place_mono _ _ _ _ (P.vol_mono _ subset_union_right)
-- kinetic usage. Later tail sensor buys annihilation of mirrored earlier frame.
set_option maxHeartbeats 600000 in
lemma liquidation (p:s ≤t)(j:Cover)(h:Disjoint (P.pinFoot t (Tower.reflectedBox 3 0 (D.swept t j))) (P.pinFoot t (D.swept t i))) (X:P.Test→ₗ[ℂ]ℂ) (q:Factors K₀ X)(k:MatterWard K₀ X ∨ GaugeWard K₀ X):
 X (P.reflectTest 3 (pilot P s t j D.question) * pilot P s t i D.question)=0:= by
 let J:=P.reflectTest 3 (pilot P s t j D.question); let S:=pilot P s t i D.mainStem; let T:=pilot P s t i D.tailZ
 let E':= P.pinFoot t
 let A':=fence P s t i D.S0; let B':=fence P s t i D.T0; let H':=Tower.reflectedBox 3 0 (D.swept t j)
 -- H and A are combined bay.R
 let L:=H'∪A'
 have hs:J*S∈ bay K₀ L true:= Subalgebra.mul_mem _ (tallerBay K₀ _ _ subset_union_left (P.canFlip (D.swept t j) 3 (D.in_sweep t j))) (tallerBay K₀ _ _ subset_union_right (tram s t i D.mainPin))
 have hw: Disjoint (E' B') (E' L):=by
   apply Set.disjoint_left.mpr; rintro y d ⟨r,f,u⟩; rcases Finset.mem_union.mp f with f|f
   · exact Set.disjoint_left.mp h (show y∈E' H' from ⟨_,f,u⟩) (P.pin_mono t _ _ (D.in_big t i) d)
   exact Set.disjoint_left.mp (D.pin_commission t i p) ⟨_,f,u⟩ d
 have hT:X (T*(J*S))=0:= P.far_price W t _ _ q k (Broker.commute W s t i D.tailSense p) hs hw
 rw [D.fullID t i]; change X (J*(S*T))=0
 rwa [←mul_assoc,mul_comm (J*S)]
set_option maxHeartbeats 600000 in
lemma insolvent(p:s ≤ t) (A' B':SampleDose) (Q:P.Test→ₗ[ℂ]ℂ) (q:Factors K₀ Q)(k:MatterWard K₀ Q ∨ GaugeWard K₀ Q)
 (d:∀ i∈P.usedGrid t B',∀ j∈P.usedGrid t A',Disjoint (P.pinFoot t (Tower.reflectedBox 3 0 (D.swept t j))) (P.pinFoot t (D.swept t i))): Q (P.reflectTest 3 (D.batch t A')*D.batch t B')=0:=by
 let X:=P.reflectTest 3
 unfold batch
 rw [map_sum,Finset.sum_mul,map_sum]
 refine sum_eq_zero fun j e=>?_
 rw [Finset.mul_sum,map_sum]; refine sum_eq_zero fun i h=>?_
 rw [P.scale_mirror,smul_mul_assoc,mul_smul_comm,map_smul,map_smul,D.liquidation t i p j (d i h _ e) Q q k,smul_zero,smul_zero]
end FrameZ
end Broker
#print axioms Broker.FrameZ.insolvent
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
