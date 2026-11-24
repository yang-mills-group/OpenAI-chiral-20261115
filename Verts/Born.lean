import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 12000
set_option maxHeartbeats 670000
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
/-- admissible at any strict RP temporal clearance w. -/
def claimV (u:ℝ)(D:SampleDose):=∀ i∈tsupport D.val, u < i 3
lemma Shuffled {u:ℝ} (U:SampleDose)(h:claimV u U)(z:ℝ)(k:0 ≤ z):claimV u (shuf U z):=by
 intro i hq; have v:=h _ ((shuf_iff ..).mp hq); rw [Pi.sub_apply, location₁] at v; linarith
lemma Invor {P:Spine}(d:ℕ){w:ℝ}(U:SampleDose)(p:claimV w U)(s:ℕ)(h:tidal P d s ≤ w): ∀ i∈tsupport (dealt U (central P d s)).val,0 ≤ i 3:=by
 intro i hz; have x:= p _ ((star_iff ..).mp hz); rw [Pi.add_apply,center3] at x; linarith
variable {s t:ℕ}{w:ℝ}(k:offer_update P d C D s B Z ≤ t)(h:tidal P d s ≤ w)(U:SampleDose)(v:claimV w U)
private lemma formula_sub{R:Hilbert}(q r:R)(z:ℂ):(z • (q-r))=(z • q-z • r):=smul_sub z q r
include k h v
lemma birth_schema(n:ℕ) : P.birthF 3 t (X s t n U):=by
 induction n generalizing U with
 | zero=>
    let D₀:=Τ s
    let V:=dealt U (central P d s)
    let q:=agentBorn P d C D s B Z
    exact (advanceW (P:=P) x D₀.placid V q t ( Invor d U v s h) k).choose
 | succ n ih=>
    change ((φ s)⁻¹ • (schema B Z d C D s t n _ - schema B Z d C D s t n _)) ∈ (P.births 3 t)
    let r:=P.macroStep s
    let V:= shuf U r
    let p' := ih V (Shuffled U v r (P.macroStep_pos s).le)
    let p:= ih U v
    exact (P.births 3 t).smul_mem _ ((P.births 3 t).sub_mem (show X s t n V ∈ P.births 3 t from p') (show X s t n U ∈ P.births 3 t from p))
noncomputable def absorb(t:ℕ)(y:P.Test):G:= if he:P.birthF 3 t y then P.viewF 3 ξ t he else 0
omit k h v in
lemma BornAt {T:P.Test}(p:P.birthF 3 t T): absorb (x:=x) t T=P.viewF 3 ξ t p:=dif_pos p
omit k
include B -- J
lemma sheen(n:ℕ): Tendsto (fun t:ℕ=>absorb (x:=x) t (X s t n U)) atTop (𝓝 (P.enter 3 ξ (works B Z d C D s n U))):=by
 induction n generalizing U with
 | zero=>
    let V:=dealt U (central P d s); let y:=(kd s); let Q:=P.viewF 3 ξ y (agentBorn P d C D s B Z)
    have hp:=spread (J:=J) V Q
    refine hp.congr' ((eventually_ge_atTop y).mono fun t ht=>?_) -- no definitional id: portal deployment.Works
    have hj:=advanceW x (Τ s).placid V (agentBorn P d C D s B Z) t ( Invor d U v s h) ht
    exact hj.choose_spec.symm.trans (BornAt (t:=t) hj.choose).symm
 | succ n ih=>
    let r:=P.macroStep s; let z:ℂ:=(φ s)⁻¹
    let V:=shuf U r; have e:=Shuffled U v r (P.macroStep_pos s).le
    have hp:= ( (ih V e).sub (ih U v)).const_smul z
    have he : z • (P.enter 3 ξ (works B Z d C D s n V) - P.enter 3 ξ (works B Z d C D s n U))=P.enter 3 ξ (works B Z d C D s (n+1) U):=rfl -- likely rfl
    refine hp.congr' ((eventually_ge_atTop (kd s)).mono fun t k=>?_)
    have a:= birth_schema B Z d C D k h V e n; have b:=birth_schema B Z d C D k h U v n; have c:=birth_schema B Z d C D k h U v (n+1)
    change z • (absorb (x:=x) t (schema B Z d C D s t n V) - absorb (x:=x) t (schema B Z d C D s t n U))=absorb (x:=x) t (schema B Z d C D s t (n+1) U)
    let hy:= congrArg₂ (fun l m:G=>z • (l-m)) (BornAt (x:=x) a) (BornAt (x:=x) b)
    apply Eq.trans hy; apply Eq.trans _ (BornAt (x:=x) c).symm
    exact (congrArg (fun q:G=>z • q) (P.view_sub 3 ξ t a b).symm).trans ((P.view_smul 3 ξ t ((P.births 3 t).sub_mem a b) z).symm)
#print axioms sheen
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
