import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
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
open PledgeT MiterT Broker
namespace AuroraB
open PledgeT MiterT Broker
open Py.Rate.Pitching.Focus (Morn)
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "Γ" j:max s:max=> agent P d C D s B j
local notation "qt" j:max s:max=> offer_update P d C D s B j
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "zQ" s:max=> MiterT.central P d s
variable (W:Lead.Clan)
local notation "aX" i:max s:max t:max n:max V:max=> schema B i d C D s t n V
local notation "cK" i:max s:max t:max V:max=> chunk B i d C D s t V
local notation "B₀" i:max s:max n:max V:max =>works B i d C D s n V
local notation "μ" t:max=> P.singleState 3 t x
local notation "ϕ"=> P.reflectTest 3
variable (U H': SampleDose)(s t:ℕ)
lemma wards(q:hosp U):∀ {h:ℝ},0 ≤h→ hosp (shuf U h):=by
 intro h a i j; obtain q0:= q (i-aislePt 3 h) ((shuf_iff ..).mp j); rw [Pi.sub_apply,location₁] at q0; linarith
lemma hosp_shift (q:hosp U)(h:tidal P d s <1):∀ i∈ tsupport (dealt U (zQ s)).val, 0 ≤ i 3:=inside_d d U q s h -- avoid sintax
include B
lemma each(a:hosp U)(b:hosp H')(h:tidal P d s < 1):
 Tendsto (fun t:ℕ=> (μ t) (ϕ (cK Z s t U)*cK W s t H')) atTop (𝓝 (inner ℂ (B₀ Z s 0 U) (B₀ W s 0 H')))∧
 Tendsto (fun t:ℕ=> (μ t) (cK W s t H')) atTop (𝓝 (inner ℂ (Ω) (B₀ W s 0 H'))):=by
 let T:= Γ Z s; let E:= Γ W s; let A0:=dealt U (zQ s); let G0:=dealt H' (zQ s); let p:=agentBorn P d C D s B Z; let q:=agentBorn P d C D s B W
 exact ⟨twoGlimpse x J (A:=T.placid) (C:=E.placid) A0 G0 (inside_d d U a s h) (inside_d d H' b s h) p q,oneGlimpse x J (A:=E.placid) G0 (inside_d d H' b s h) q⟩
variable (Q:ℕ→P.Test→ₗ[ℂ]ℂ)(f:∀ t:ℕ,Comparison P.calibration (P.singleState 3 t x) (Q t))
-- CP comparator choose covers.AS
include f
private lemma womb (r:ℕ): MatterWard P.calibration (Q r) ∧ Factors P.calibration (Q r):= by
 let R:=P.comparator r x; have p:=R.choose_spec; exact ⟨(Comparison.unique _ _ p.1 (f r)) ▸ p.2.2.2,(f r).factors⟩
lemma killed (a:hosp U)(b:hosp H')(t0:4*Hemlock.radius P d s≤ 1)(g:qt Z s ≤ t)(h:qt W s ≤ t): Q t (ϕ (cK Z s t U)*cK W s t H')=0 ∧ Q t (cK W s t H')=0 ∧ Q t (ϕ (cK W s t H'))=0:=by
 have p:=womb B Q f t -- include B? unused section var h.
 exact ⟨fare3 B Z t d C D s U H' W g h t0 a b _ p.2 p.1, (Γ W s).foresee t h _ (Q t) p.2 p.1,(Γ W s).foresF t h _ (Q t) p.2 p.1⟩
-- u-v.-
lemma avoids(a:hosp U)(b:hosp H')(t0:4*Hemlock.radius P d s≤ 1)(g:qt Z s ≤ t)(h:qt W s ≤ t)(n m:ℕ): Q t (ϕ (aX Z s t n U)*aX W s t m H')=0∧ Q t (aX W s t m H')=0 ∧ Q t (ϕ (aX Z s t n U))=0:=by
 let R₀:=Q t; let F(X:SampleDose):=shuf X (P.macroStep s); have vA(X:SampleDose)(t:hosp X):hosp (F X):=wards X t (P.macroStep_pos _|>.le)
 let ξ':=(φ s)⁻¹
 induction n generalizing U with
 | zero=>
    induction m generalizing H' with
    | zero=> exact ⟨(killed B Z d C D W U H' s t Q f a b t0 g h).1, (killed B Z d C D W U H' s t Q f a b t0 g h).2.1, (killed B Z d C D Z U U s t Q f a a t0 g g).2.2⟩
    | succ m ih=>
       have hp:=ih H' b; have ht:=ih _ (vA H' b)
       rw [rSchema, Algebra.mul_smul_comm,mul_sub,map_smul,map_sub,ht.1,hp.1,sub_zero,smul_zero, map_smul,map_sub, ht.2.1,hp.2.1,sub_zero,smul_zero]; exact ⟨rfl,rfl,hp.2.2⟩
 | succ n ih=>
    have hp:=ih U a; have ht:=ih _ (vA U a)
    rw [rSchema,P.scale_mirror, map_sub, smul_mul_assoc, _root_.sub_mul,map_smul,map_sub,ht.1,hp.1,sub_zero,smul_zero, map_smul,map_sub, ht.2.2,hp.2.2,sub_zero,smul_zero]; exact ⟨rfl,hp.2.1,rfl⟩
#print axioms each
#check @fare3
#check @killed
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
