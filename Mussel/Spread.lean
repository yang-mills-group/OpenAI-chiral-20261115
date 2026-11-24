import SatinFixedContrastNovember4
import GlazeS.Room
import YM.SU5.Six.ViewHom
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
open PledgeT.MiterT
private lemma surf (f:P.Test)(j:Axis)(z:Cover)(L:List (Trans j)):
    P.cruise (Vacancy.spare j L) z f=P.luggage j L (fun i=>z i.val) f:=by
 induction L with |nil=>rfl |cons i L h=> rw [P.ship_started,←h]; rfl
lemma gossip_eq (A:P.Apron)(t:ℕ)(z:Cover): P.issuing t A z=gibbert P A.s t A.F z :=by
 unfold issuing gibbert; rw [←surf _ _ _ (look 3),P.cruise_mesh,P.chart_transverse]; rfl
variable (A:P.Apron)(D:SampleDose)(q:P.birthF 3 A.s A.F)
local notation "T" => P.physicalEnergy 3 (P.otherSpectrum 3 3 x)
local notation "Z₀" => P.viewF 3 (P.otherSpectrum 3 3 x) A.s q
noncomputable def raySum(x:P.Spectrum0 3)(w:P.ColorHil 3 (P.otherSpectrum 3 3 x))(D:SampleDose)(t:ℕ):P.ColorHil 3 (P.otherSpectrum 3 3 x):=
    ∑ i ∈ P.usedGrid t D,P.activation t D i • P.truck 3 _ (P.vtile t i) ((P.physicalEnergy 3 _).E (P.meshPose t i 3).toNNReal w)
noncomputable abbrev peg(x:P.Spectrum0 3)(w:P.ColorHil 3 (P.otherSpectrum 3 3 x))(D:SampleDose):=
    ∫ y:Vantage,scoop P x w D y
include J
lemma spread (g: G): Tendsto (fun k:ℕ=> raySum x g D k) atTop (𝓝 (P.enter 3 ξ (peg x g D))) := verge P D x (J: P.Ellis 3 x) g -- J not included!
omit J
variable(x)(t:ℕ)
local notation "I"=>P.usedGrid t D
local notation "u"=>P.otherSpectrum 3 3 x
noncomputable def rayAt (w:P.ColorHil 3 u)(t:ℕ)(i:Cover):=
 (P.truck 3 u (P.vtile t i)) ((P.physicalEnergy 3 u).E ((P.meshPose t i 3).toNNReal) w)
private lemma advanceOne (h:∀ y∈tsupport D.val,0 ≤ y 3)(v:A.s ≤ t)(i:Cover)(hi:i∈P.usedGrid t D)(k:ℂ): ∃ b:P.birthF 3 t (k • P.issuing t A i),P.viewF 3 u t b=k • rayAt x (P.viewF 3 u A.s q) t i :=by
 have h1: 0 ≤ i 3:=by
    apply (bell_le (timeMesh P.par) t 0 _).mp; rw [show bell (timeMesh P.par) t 0=0 by simp [bell]]
    exact h _ ((P.usedPose t D i).mp hi)
 let b0:=fill_gossip P _ _ u q v i h1
 let b:=b0.choose
 have w:= b0.choose_spec
 let c:= (P.births 3 t).smul_mem k (show gibbert P A.s t A.F i ∈ P.births 3 t from b)
 let z:= congrArg (fun a:P.Test=> k • a) (gossip_eq A t i)
 let d:P.birthF 3 t (k • P.issuing t A i) := (congrArg (P.birthF 3 t) z.symm).mp c
 refine ⟨d,(P.identical_F 3 u t d c z).trans ((P.view_smul 3 u t b k).trans (congrArg (fun a:P.ColorHil 3 u=> k • a) w))⟩
lemma advanceW (h:∀ y∈tsupport D.val,0 ≤ y 3)(v:A.s ≤ t): ∃ b:P.birthF 3 t (P.prepared t A D),P.viewF 3 u t b=raySum x (P.viewF 3 u _ q) D t:= P.birthSum u _ _ _ _ (fun i hi=> advanceOne x A D q t h v i hi _)

end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
