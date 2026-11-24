import Mussel.Foil
import Mussel.Super
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
open Broker PledgeT MiterT
open Py.Rate.Pitching.Focus (Morn)
open Calico
abbrev served (F R:SampleDose):Prop:=F.Normalized ∧ R.Normalized ∧ tsupport F.val ⊆ reviewEarlierBox.invites∧tsupport R.val⊆reviewLaterBox.invites
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
variable (F R:SampleDose)
local notation "Ft"=>flipDose F 3
local notation "A" s:max=> agent P d C D s B Z
local notation "TX" t:max=>P.singleState 3 t x
local notation "Fh" i:max q:max=>dealt q (central P d i)
local notation "Φ"=>P.reflectTest 3
noncomputable def chunk (s t:ℕ)(U:SampleDose):=(agent P d C D s B Z).batch t (dealt U (central P d s))
noncomputable def vistaH(s:ℕ)(U:SampleDose):=(agent P d C D s B Z).delivery (dealt U (central P d s)) x (agentBorn ..)
local notation "Ck" s:max t:max U:max=> chunk B Z d C D s t U
local notation "Pl" s:max U:max=> vistaH B Z d C D s U
local notation "P0" U:max=> MiterT.cloud P d C D x U
#print vistaH
structure Tour : Prop where
 convergent(U:SampleDose)(h:∀ y∈tsupport U.val,(1:ℝ)< y 3)(v:U.Normalized): Tendsto (fun s=> Pl s U) atTop (𝓝 (P0 U))
 fine :∀ᶠ s:ℕ in atTop,Tendsto (fun t:ℕ=> P.singleState 3 t x ((P.reflectTest 3 (Ck s t Ft))* Ck s t R)) atTop (𝓝 (inner ℂ (Pl s Ft) (Pl s R))) ∧ Tendsto (fun t=>P.singleState 3 t x (Ck s t Ft)) atTop (𝓝 (inner ℂ (Ω) (Pl s Ft)))∧ Tendsto (fun t=>P.singleState 3 t x (Ck s t R)) atTop (𝓝 (inner ℂ (Ω) (Pl s R)))
 thin:Tendsto (fun s=> (4:ℝ)*Hemlock.radius P d s) atTop (𝓝 0)
 posing(s t:ℕ)(u:offer_update P d C D s B Z ≤ t)(A':SampleDose): P.asked_at t (Ck s t A') {y| ∃ v∈tsupport A'.val, ∀ j:Axis, |y j-v j| ≤4* Hemlock.radius P d s}
 comparator :∀ᶠ s:ℕ in atTop,∀ t:ℕ,offer_update P d C D s B Z ≤ t→ let a:=P.reflectTest 3 (Ck s t Ft); let b:= Ck s t R; ∃ X, Comparison P.calibration (P.singleState 3 t x) X∧ MatterWard P.calibration X ∧ X a=0∧X b=0 ∧ X (a*b)=0
 widthJoint:Tendsto (fun s=>limUnder atTop (fun t:ℕ=> P.singleState 3 t x ((P.reflectTest 3 (Ck s t Ft))*Ck s t R))) atTop (𝓝 (inner ℂ (P0 Ft) (P0 R)))
 widthOne(U:SampleDose)(h:∀ y∈tsupport U.val,(1:ℝ)< y 3)(v:U.Normalized): Tendsto (fun s=>limUnder atTop (fun t=>P.singleState 3 t x (Ck s t U))) atTop (𝓝 (inner ℂ (Ω) (P0 U)))
-- reflected support deduce using pin-mirror & inverse (existing mirror_back). color support.
#check Tour
variable(M:Morn P.par.K)(hM:∀ i:ℕ,d ≤ i → Accordance P M d i (C i) (D i))(hq:RobeRoad P d C D x)(hs:served F R)
private def bound(U:SampleDose):Prop:=∀ y ∈ tsupport U.val, (1:ℝ)< y 3
private lemma delivered:(h:served F R) → bound Ft ∧ bound R :=by
 intro h; refine ⟨fun i p=>?_,fun i p=>((h.2.2.2 p) 3 (Set.mem_univ _)).1⟩
 rw [flipBudget] at p; have e: (poseMirror 3 i) 3< (-1:ℝ):=((h.2.2.1 p) 3 (Set.mem_univ _)).2
 change opposeR 3 i 3 < -1 at e
 rw [show opposeR 3 i 3= -i 3 from if_pos rfl] at e; linarith
include B hM hq
private lemma completed (U:SampleDose)(p:bound U) (v:U.Normalized): Tendsto (fun s=> Pl s U) atTop (𝓝 (P0 U)):= tailored B Z d C D M hM hq U p v
omit hM hq
lemma fine_pay (s:ℕ)(U V:SampleDose)(p:bound U)(v:bound V)(h:tidal P d s <1): Tendsto (fun t:ℕ=>P.singleState 3 t x ((P.reflectTest 3 (Ck s t U))* Ck s t V)) atTop (𝓝 (inner ℂ (Pl s U) (Pl s V)))∧ Tendsto (fun t:ℕ=> P.singleState 3 t x (Ck s t V)) atTop (𝓝 (inner ℂ (Ω) (Pl s V))):=by
 have e:= (agent P d C D s B Z).earned (Fh s V) (Fh s U) x J (agentBorn ..) (inside_d d V v s h) (inside_d d U p s h); exact e.symm
include hM hq hs
lemma sealed:Tour B Z d C D F R:=by
 let Q:=completed B Z d C D M hM hq
 obtain ⟨q,b⟩:=delivered F R hs
 have heps:∀ᶠ s:ℕ in atTop,tidal P d s<1:= (recessVanish P d).eventually (gt_mem_nhds zero_lt_one)
 have hz:Tendsto (fun s:ℕ=>4*Hemlock.radius P d s) atTop (𝓝 0):=by simpa using (radiusTiny P d).const_mul 4
 refine ⟨fun U=>Q U,heps.mono (fun s h=>⟨(fine_pay B Z d C D s Ft R q b h).1,(fine_pay B Z d C D s Ft Ft q q h).2,(fine_pay B Z d C D s Ft R q b h).2⟩),hz,fun s t v U=>(agent P d C D s B Z).reading_space t U v (central P d s) _ (deputized P d C D s B Z).coordinates,?_,?_,?_⟩
 · filter_upwards [hz.eventually (ge_mem_nhds zero_lt_one)] with s he t p
   let κ:=P.comparator t x; let m:= κ.choose_spec; let A0:= agent P d C D s B Z
   exact ⟨κ.choose,m.1,m.2.2.2,A0.foresF t p _ κ.choose m.1.factors m.2.2.2,A0.foresee t p _ κ.choose m.1.factors m.2.2.2,A0.solvent t R (Ft) p _ he (deputized P d C D s B Z).coordinates b q κ.choose m.1.factors m.2.2.2⟩
 · refine ((Q (Ft) q (flipPay F hs.1 3)).inner (𝕜:=ℂ) (Q R b hs.2.1)).congr' (heps.mono fun i h=> (fine_pay B Z d C D i Ft R q b h).1.limUnder_eq.symm)
 intro U j k
 exact (show Tendsto (fun s=> inner ℂ (Ω) (Pl s U)) atTop (𝓝 (inner ℂ (Ω) (P0 U))) from tendsto_const_nhds.inner (Q U j k)).congr' (heps.mono fun i h=> (fine_pay B Z d C D i U U j j h).2.limUnder_eq.symm)
#print axioms sealed
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
