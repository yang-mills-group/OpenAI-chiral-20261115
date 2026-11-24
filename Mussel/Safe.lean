import Mussel.Thread
import GlazeS.Locations
import Crape.Halo
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
namespace Hemlock
open PledgeT MiterT
variable (P:Spine)(s t w n:ℕ)(u:Vantage)
local notation "K₀"=>P.calibration
local notation "T"=>timeMesh P.par
local notation "V0"=> ruler P.par.block
local notation "L"=> P.par.R.L
abbrev pace:ℝ:=(mill T s:ℝ≥0)
abbrev lane:ℝ:=(whenly T s w:ℝ≥0).val
private lemma pillar(i:ℕ):lane P s i=(i:ℝ) * pace P s:=by
 rw [lane,← natural_time]; unfold bell pace; push_cast; rfl
lemma lane_eq(i:ℕ):lane P s i=(i:ℝ) * (mill (timeMesh P.par) s:ℝ):=pillar P s i
lemma span_lane {A:Finset Cover} (g:Between K₀ 3 0 (V0*(w:ℤ)) A) {y:Vantage}(h:y∈P.pinFoot s A): 0 ≤ y 3 ∧ y 3 ≤ lane P s w :=by
 obtain ⟨a,e,p⟩:=h
 obtain ⟨l,r⟩:=g a e
 let R:=precisionAt P.par s
 obtain ⟨hl,hr⟩:=abs_le.mp (show |R*(2*y 3)-(a 3:ℝ)|≤(reserve P.par P.width:ℝ) from p 3)
 have he :2*lane P s w= (↑((V0)*(w:ℤ)):ℝ)/R:=by rw [lane,←natural_time, Apron.distance_mark]
 have hp:0<R:= Tapestry.positiveScale ..
 let z:=reserve P.par P.width
 have hu:(z:ℝ) ≤ (a 3:ℝ):=by exact_mod_cast (show (z:ℤ) ≤ a 3 from (by change 0+ (z:ℤ)≤a 3 at l; omega))
 have ht:(a 3:ℝ)+(z:ℝ) ≤ (↑((V0)*(w:ℤ)):ℝ):=by exact_mod_cast (show (a 3:ℤ)+(z:ℤ) ≤ V0*(w:ℤ) from r)
 change -(z:ℝ)≤ _ at hl; change _≤(z:ℝ) at hr
 field_simp at he; constructor<;> apply (mul_le_mul_iff_right₀ hp).mp <;> linarith
noncomputable def frost(k:ℕ):Cover:=fun i=> if i=(3:Axis) then (2*thickStep P s k w:ℕ) else ⌈u i/pace P k⌉
lemma snow(k:ℕ)(h:s ≤ k) : P.meshPose k (frost P s w u k) 3=2* lane P s w:=by
 let r:=thickStep P s k w
 change bell T k (if _ then _ else _) = _; rw [if_pos rfl,Nat.cast_mul,Nat.cast_ofNat,two_mul,bell_add, natural_time]
 change lane P k r + lane P k r=2* lane P s w; rw [lane,step_when (P:=P) k w s h]; change lane P s w+lane P s w=_; ring
lemma glaze(k:ℕ)(i:Axis)(h:i≠3): |P.meshPose k (frost P s w u k) i-u i|≤ pace P k:=by
 change |(↑(if i=3 then ((2*thickStep P s k w:ℕ):ℤ) else ⌈u i/pace P k⌉):ℝ)*pace P k-u i|≤_
 let z:=pace P k
 rw [if_neg h,abs_le]
 have hz:0<z:=mill_pos ..
 have hl:= (div_le_iff₀ hz).mp (Int.le_ceil (u i/z))
 have hr: (↑⌈u i / z⌉:ℝ) < u i / z+1:=Int.ceil_lt_add_one ..
 field_simp at hr; change -z≤ _ ∧ _≤z
 constructor<;> linarith
#check Apron.distance_mark
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
