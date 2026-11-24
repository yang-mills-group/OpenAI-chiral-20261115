import Verts.Enroll
import Verts.Doses
import Verts.Competence
import AuroraB.Passage
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
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
open PledgeT MiterT Broker Aloft
open Py.Rate.Pitching.Focus (Morn)
namespace AuroraB.Verts
open Calico _root_.Yoland
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "χ" t:max=>P.singleState 3 t x
local notation "isp" v:max=>aislePt (3:Axis) v
local notation "kd" s:max=> offer_update P d C D s B Z
local notation "Τ" s:max => agent P d C D s B Z
local notation "X" s:max t:max n:max U:max=> schema B Z d C D s t n U
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
open MiterT
variable (w:ℝ)(A A':SampleDose)(n:ℕ)
local notation "Γ" t:max=> fieldLimit x d C D n t
variable (M:Morn P.par.K)(p:∀ s:ℕ,d ≤ s → Accordance P M d s (C s) (D s))(hq:RobeRoad P d C D x)(e:0<w)
local notation "ψ" z:max=> zoomV x d C D n z
local notation "ϕ'"=>P.reflectTest 3
-- W>0 clearance as tested.Limit readings and costs show convergence. carry canonical laws true. For ALL smears on that clearance, simultaneous all w.
set_option synthInstance.maxHeartbeats 320000 in
structure College :Prop where
 weighted :∃ (R:ℝ)(f:ℕ→ℝ),0 ≤ R∧ Tendsto f atTop (𝓝 0) ∧
    (∀ A:SampleDose,claimV w A→‖Γ A‖ ≤ allowanceV A * R ∧ Integrable (fun z:Vantage=> (A.val z:ℂ) • ψ z)) ∧
    ∀ᶠ s:ℕ in atTop,∀ A:SampleDose,claimV w A→‖works B Z d C D s n A-Γ A‖ ≤ allowanceV A * f s
 -- integrability and linearity fields
 realLin : ∀(A V:SampleDose),claimV w A→ claimV w V →∀ r:ℝ, Γ (combine A V r)= (r:ℂ) • (Γ A)+Γ V ∧ claimV w (combine A V r)
 zeroLin : claimV w silent∧ Γ silent= (0:H)
 -- Vec(Color) births and limits t.
 trials: ∀ᶠ s:ℕ in atTop,∀ (A:SampleDose),claimV w A→
    (∀ t:ℕ,offer_update P d C D s B Z ≤ t →P.birthF 3 t (schema B Z d C D s t n A))∧
    Tendsto (fun t:ℕ=>absorb (x:=x) t (schema B Z d C D s t n A)) atTop (𝓝 (P.enter 3 ξ (works B Z d C D s n A)))
 charge : ∀ A:SampleDose,claimV w A → Tendsto (fun s:ℕ=>limUnder atTop (fun t:ℕ=>absorb (x:=x) t (schema B Z d C D s t n A))) atTop (𝓝 (P.enter 3 ξ (Γ A)))
 -- actual readings of regulated-body.Promotion
 frank : ∀ᶠ s:ℕ in atTop,∀ (U V:SampleDose)(i:Lead.Clan)(m:ℕ),claimV w U→ claimV w V→ let g:= works B Z d C D s n U; let h:=works B i d C D s m V; let f(t:ℕ):P.Test:=ϕ' (schema B Z d C D s t n U); let z(t:ℕ):P.Test := schema B i d C D s t m V;
    Tendsto (fun t=> (χ t) ((f t)*(z t))) atTop (𝓝 (inner ℂ g h)) ∧ Tendsto (fun t=> (χ t) (f t)) atTop (𝓝 (inner ℂ g (Ω)))∧ Tendsto (fun t=> (χ t) (z t)) atTop (𝓝 (inner ℂ (Ω) h))∧
    ∀ᶠ t:ℕ in atTop,∀Q:P.Test→ₗ[ℂ]ℂ,Comparison P.calibration (P.singleState 3 t x) Q→ Q ((f t)*(z t))=0∧ Q (f t)=0 ∧ Q (z t)=0
 gestures: ∀ (U V:SampleDose)(i:Lead.Clan)(m:ℕ), claimV w U→claimV w V→ Positions B Z d C D i n m U V (inner ℂ (Γ U) (fieldLimit x d C D m V)) (inner ℂ (Γ U) (Ω)) (inner ℂ (Ω) (fieldLimit x d C D m V))
#check @voider
#check @Positions
include B p hq e
set_option synthInstance.maxHeartbeats 320000 in
set_option maxHeartbeats 1180000 in
lemma college : College B Z d C D w n:=by
 let hr:=funded B Z d C D w e n M p hq
 obtain ⟨F,r,u,f,he,ht⟩:= hr
 have hs:∀ᶠ s:ℕ in atTop,tidal P d s ≤ w:= (recessVanish P d).eventually (ge_mem_nhds e)
 refine ⟨⟨r,F,u,f,he,ht⟩, fun A V h v r=>⟨combine_eq x d C D A V r n ((he _ h).2) ((he _ v).2),combine_support A V h v _⟩,⟨zero_pose w,zenith0 d C D x n⟩,hs.mono (fun s h A wA=>⟨fun t k=> birth_schema B Z d C D k h A wA n,sheen B Z d C D h A wA n⟩),fun A v=>embodied B Z d C D w n A M p hq e v,?_,fun A V i m a b=> presented B Z d C D i w n m A V M p hq e a b⟩
 have hv: Tendsto (fun s:ℕ=>4*Hemlock.radius P d s) atTop (𝓝 (0:ℝ)):=by simpa only [mul_zero] using (radiusTiny P d).const_mul 4
 filter_upwards [hs,hv.eventually (ge_mem_nhds e)] with s k h U V i m g q
 have he:= codaU B Z d C D s n m U V w g q i k
 exact ⟨he.1,he.2.1,he.2.2,((eventually_ge_atTop (kd s)).and (eventually_ge_atTop (offer_update P d C D s B i))).mono (fun t y R b=>voider B Z d C D s t n m w i U V g q y.1 y.2 h R b)⟩
#check @combine_eq
#check @zero_pose
#check @zenith0
#check @embodied
#print axioms college
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
