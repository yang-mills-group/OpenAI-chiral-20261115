import YM.SU5.Assay.Pharos
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.base j x
local notation "κ"=>P.coffee j x
local notation "𝔤"=>P.Grips j x
local notation "ξ"=>P.prepared
local notation "μ"=>P.singleState j
local notation "⟪" T "⟫"=>inner ℂ Ω ((T:Y) Ω)
local notation "η"=>P.pharos j x
local notation "τ"=>P.otherLag j x
local notation "ρ"=>P.slot j x
local notation "Φ"=>P.thrust j x
local notation "Ψ"=>P.retort j x
variable {P j x}{T:P.LagOp j x}{a b d e w:ℝ}{F:SampleDose}
lemma thrust_step (h:(S).Credits w T)(u:Walled j F a b w)(t:d ≤ a):
 Φ T F d=ω (a-d) (Φ T F a):=by
 rw [←(thrust_launch h (u.outer t le_rfl)).2,←(thrust_launch h u).2,coffee_cuts h u t le_rfl]
 unfold sand;rw [sub_self,wax_zero,mul_one]; rfl
lemma retort_step (h:(S).Credits w T)(u:Walled j F a b w)(t:b ≤ d):Ψ T F d=ω (d-b) (Ψ T F b):=by
 rw [thrust_retort h u,thrust_retort h (u.outer le_rfl t),thrust_step (other_credits h) u.flip (neg_le_neg t),neg_sub_neg]
lemma thrust_go (h:(S).Credits w T)(u:Walled j F a b w)(p:Vantage):Φ T (moveDose F p) (p j+a)=W p (Φ T F a):=by
 rw [←(thrust_launch h (u.move p)).2,←(thrust_launch h u).2,coffee_moved _ h u,P.cart_vac]
lemma retort_go (h:(S).Credits w T)(u:Walled j F a b w)(p:Vantage):Ψ T (moveDose F p) (p j+b)=W p (Ψ T F b):=by
 rw [←(retort_land h (u.move p)).2,←(retort_land h u).2,coffee_moved _ h u,P.locate_star,P.cart_vac]

-- Moving the LATER smear upwards along price axis.
lemma thrust_more (h:(S).Credits w T)(u:Walled j F a b w){p:Vantage}
 (v:0 ≤ p j)(z:∀i≠j,p i=0):Φ T (moveDose F p) a=ω (p j) (Φ T F a):=by
 rw [thrust_step h (u.move p) (le_add_of_nonneg_left v),add_sub_cancel_right,thrust_go h u p,P.cart_same j x (z:=0) z,P.cart_null];rfl
lemma retort_more (h:(S).Credits w T)(u:Walled j F a b w){p:Vantage}
 (v:p j ≤ 0)(z:∀i≠j,p i=0):Ψ T (moveDose F p) b=ω (-p j) (Ψ T F b):=by
 rw [retort_step h (u.move p) (add_le_of_nonpos_left v),show b-(p j+b)= -p j by abel,retort_go h u p,P.cart_same j x (z:=0) z,P.cart_null];rfl

variable (P j x)
def two_call (A:Lag)(F:SampleDose)(c:ℝ)(A':Lag)(G:SampleDose):ℂ:= inner ℂ (Ψ A F c) (Φ A' G c)
local notation "Ξ"=>P.two_call j x
variable {P j x}{T':P.LagOp j x}{G:SampleDose}{c v r:ℝ}
lemma two_call_from (h:(S).Credits w T)(h':(S).Credits v T')
 (u:Walled j F a b w)(u':Walled j G b c v):
 Ξ T F b T' G=⟪κ T a b F*κ T' b c G⟫:=by
 rw [two_call,←(thrust_launch h' u').2, ←(retort_land h u).2]
 exact ContinuousLinearMap.adjoint_inner_left ..
lemma two_call_go (h:(S).Credits w T)(h':(S).Credits v T')
 (u:Walled j F a b w)(u':Walled j G b c v)(p:Vantage):
 Ξ T (moveDose F p) (p j+b) T' (moveDose G p)=Ξ T F b T' G:=by
 rw [two_call,thrust_go h' u',retort_go h u,P.inner_pay];rfl
lemma two_call_wall (h:(S).Credits w T)(h':(S).Credits v T')
 (u:Walled j F a b w)(u':Walled j G b c v)(t:Walled j F d e w)(t':Walled j G e r v):
 Ξ T F b T' G=Ξ T F e T' G:=by
 unfold two_call
 rcases le_total b e with q|q
 · rw [retort_step h u q,thrust_step h' t' q];exact ((S).swing ..).symm
 rw [retort_step h t q,thrust_step h' u' q]; exact (S).swing ..
lemma two_call_eq (h:(S).Credits w T)(u:Walled j F a b w):
 Ξ (τ T) (flipDose F j) (-a) T' G=inner ℂ (Φ T F a) (Φ T' G (-a)):=by
 rw [two_call,thrust_retort (other_credits h) u.flip,P.other_other,flip_twice,neg_neg]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
