import Mussel.GleamM
import SatinThinField
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
open YM.Six
variable (s n t:ℕ)(F R:SampleDose)(f:tsupport F.val⊆reviewEarlierBox.invites)(e:tsupport R.val⊆reviewLaterBox.invites)(u:F.Normalized)(v:R.Normalized)
local notation "D"=> puppet P Z s n
local notation "Q"=> flipDose F 3
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "τ" t:max=> P.singleState 3 t x
private lemma earlier {x:Vantage}(h:x∈reviewEarlierBox.invites):x 3<(-1:ℝ):= (h (3:Axis) (Set.mem_univ _)).2
private lemma later {x:Vantage}(h:x∈reviewLaterBox.invites): (1:ℝ)<x 3:= (h (3:Axis) (Set.mem_univ _)).1
include f
private lemma friend {y:Vantage}(h:y∈tsupport (flipDose F 3).val): (1:ℝ)<y 3:=by
 rw [flipBudget] at h
 have k:=earlier (f h); change opposeR 3 y 3 < -1 at k; rw [show opposeR 3 y 3= -y 3 from if_pos rfl] at k; linarith
local notation "N" n:max s:max t:max=> P.prepared t (puppet P Z s n) R
local notation "D'" n:max s:max t:max=> P.reflectTest 3 (P.prepared t (puppet P Z s n) (flipDose F 3))
private lemma flipagain: flipDose (flipDose F 3) 3=F:=by
 cases F with|mk v h q=> unfold flipDose; congr 1; funext x; exact congrArg v (reflectPose_twice 3 x) -- omit f!
omit f
lemma forecastPilot (F R:SampleDose)(f:tsupport F.val⊆reviewEarlierBox.invites)(q:tsupport R.val⊆reviewLaterBox.invites)(h:P.calibration.ℓ<n)(w:P.probeWidth s n 3<1)(l:s ≤ t): ∃ X, Comparison P.calibration (P.singleState 3 t x) X ∧ GaugeWard P.calibration X ∧ MatterWard P.calibration X ∧ X ((P.reflectTest 3 (P.prepared t D (flipDose F 3))) * P.prepared t D R)=0:=by
 have wb:P.WallBefore ((D).kiss P 3) F 0:=by intro u ht; change u 3+P.probeWidth s n 3<0; linarith only [w,earlier (f ht)]
 have wf:P.WallAfter D R 0:=by intro u ht; change 0+P.probeWidth s n 3<u 3; linarith only [w,later (q ht)]
 let p:= P.comparator t x; let X:=p.choose; let m:=p.choose_spec
 have eq:(P.reflectTest 3 (P.prepared t D (flipDose F 3)))=P.prepared t ((D).kiss P 3) F:=by rw [←P.prepared_opposition, flipagain F f]
 exact ⟨X,m.1,m.2.2.1,m.2.2.2,(congrArg (fun a:P.Test=> X (a * P.prepared t D R)) eq).trans (P.split_test t ((D).kiss P 3) F D R (P.test_apart _ _ 0 _ _ wb wf) l l Z.2 (P.sensor_mirror Z.2 3 D (aware P Z s n h)) X m.1.factors (.inl m.2.2.2))⟩
include f u e v B
-- fuses puppet tested BOTH on given smears. zero comparison.
#check @oneGlimpse
structure Reception (K:P.Register)(F R:SampleDose) (Z:Lead.Clan) (x:P.Spectrum0 3)(c r:ℕ→ℕ):Prop where
 forth (U:SampleDose)(p:∀ y∈tsupport U.val,(1:ℝ)<y 3)(h:U.Normalized): Tendsto (fun i=> field (x:=x) (A:=puppet P Z (c i) (r i)) U (brightR ..)) atTop (𝓝 (P.heaven 3 (P.otherSpectrum 3 3 x)))
 one (U:SampleDose)(p:∀ y∈tsupport U.val,(1:ℝ)<y 3)(h:U.Normalized): Tendsto (fun i=>limUnder atTop (fun t=>P.singleState 3 t x (P.prepared t (puppet P Z (c i) (r i)) U))) atTop (𝓝 1)
-- define functions for performance/export
 joint: Tendsto (fun i=>limUnder atTop (fun t=>P.singleState 3 t x ((P.reflectTest 3 (P.prepared t (puppet P Z (c i) (r i)) (flipDose F 3))) * P.prepared t (puppet P Z (c i) (r i)) R))) atTop (𝓝 1)
 split: ∀ᶠ i in atTop,∀ t,c i ≤ t → ∃ X,Comparison P.calibration (P.singleState 3 t x) X ∧ GaugeWard P.calibration X ∧ MatterWard P.calibration X ∧ X ((P.reflectTest 3 (P.prepared t (puppet P Z (c i) (r i)) (flipDose F 3))) * P.prepared t (puppet P Z (c i) (r i)) R)=0
-- ranges info retain (prove below eventually)
 tiny(ε:ℝ)(p:0<ε):∀ᶠ i:ℕ in atTop,P.FitsAll (c i) (r i) ε -- puppet aperture exactly same; see apertureE
section abstract
omit f u e v B
private lemma balance {X:Hilbert}(Y:ℕ→SampleDose→X)(z:X)(hz:inner ℂ z z=(1:ℂ))(F Gz:SampleDose)(pos:SampleDose→Prop)(a:pos F)(b:pos Gz)(l:∀ U,pos U → Tendsto (fun k=> Y k U) atTop (𝓝 z))(R:ℕ→ℕ→SampleDose→ℂ)(W:ℕ→ℕ→ℂ)
   (h:∀U,pos U→∀ k,Tendsto (fun i=>R k i U) atTop (𝓝 (inner ℂ z (Y k U))))(p:∀ k,Tendsto (fun i=> W k i) atTop (𝓝 (inner ℂ (Y k F) (Y k Gz)))) :
   (∀U,pos U→Tendsto (fun k=>limUnder atTop (fun i=>R k i U)) atTop (𝓝 1)) ∧ Tendsto (fun k=>limUnder atTop (fun i=>W k i)) atTop (𝓝 1) :=by
 constructor
 · intro U u
   have he:= (show Tendsto (fun k=>inner ℂ z (Y k U)) atTop (𝓝 (inner ℂ z z)) from tendsto_const_nhds.inner (l U u))
   rw [hz] at he; exact he.congr fun k=>(h U u k).limUnder_eq.symm
 have he := (l F a).inner (𝕜:=ℂ) (l Gz b); rw [hz] at he; exact he.congr fun k=> (p k).limUnder_eq.symm
end abstract
-- ordered limit.F
set_option maxHeartbeats 800000 in
lemma puppet_end (K0:P.Register) : Reception K0 F R Z x c r:=by
 let C:=puppet P Z
 let g(i:ℕ)(U:SampleDose):=field (x:=x) (A:=C (c i) (r i)) U (brightR ..)
 have l(U:SampleDose)(p:∀ y∈tsupport U.val,(1:ℝ)<y 3)(h:U.Normalized):Tendsto (fun i=>g i U) atTop (𝓝 (Ω)):=by
    let b:ℝ≥0:=1
    have ht:= short_born B Z b zero_lt_one
    refine (tailPeg x U h b zero_lt_one (fun i H'=> (p i H').le) _ ht).congr fun i=>?_
    exact congrArg (fun a:P.ColorHil 3 ξ=>peg x a U) (shine P Z (c i) (r i) x).symm
 have he:inner ℂ (Ω) Ω=1:=(inner_self_eq_norm_sq_to_K ..).trans (show (↑‖(Ω)‖:ℂ)^2=1 by rw [P.stone_norm]; norm_num)
 let W:=onTheseWindows B f e u v
 let pos(U:SampleDose):= (∀ y∈tsupport U.val,(1:ℝ)<y 3) ∧ U.Normalized
 let Gl:=flipDose F 3; have pg : pos Gl:=⟨fun y h=>friend F f h,flipPay F u 3⟩
 have pr:pos R:=⟨fun y h=> later (e h),v⟩
 let α(i k:ℕ)(U:SampleDose):=P.singleState 3 k x (P.prepared k (C (c i) (r i)) U)
 let β(i k:ℕ):= P.singleState 3 k x ((P.reflectTest 3 (P.prepared k (C (c i) (r i)) Gl))* P.prepared k (C (c i) (r i)) R)
 have b:=balance g Ω he Gl R pos pg pr (fun U H'=>l U H'.1 H'.2) α β (fun U p i=> oneGlimpse x J (A:=C (c i) (r i)) U (fun y h=>zero_le_one.trans (p.1 y h).le) (brightR ..)) (fun i=> twoGlimpse x J (A:=C (c i) (r i)) (C:=C (c i) (r i)) Gl R (fun y h=>zero_le_one.trans (pg.1 y h).le) (fun y h=>zero_le_one.trans (pr.1 y h).le) (brightR ..) (brightR ..))
 exact ⟨l,fun U p q=> b.1 U ⟨p,q⟩,b.2,W.holds.mono (fun i h t v=> forecastPilot Z _ _ t F R f e h.nlarge h.small v),W.thin⟩
#print axioms puppet_end
#check @twoGlimpse
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
