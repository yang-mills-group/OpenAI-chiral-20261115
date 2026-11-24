import Verts.Uniform
import Verts.DotFeed
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
open _root_.YM.Preen DoseTravel _root_.Acacia
variable (w:ℝ)(e:0<w)(m:ℕ)
local notation "Q₀" U:max=> fieldLimit x d C D m U
variable (j:ℕ)(y:P.ManyF 3 (P.otherSpectrum 3 3 x))(v:PeriodS P d C D x j y)(a:d ≤ j)(b:tidal P d j < w)
local notation "ι"=>tidal P d j
local notation "δ"=>w- tidal P d j
local notation "YQ"=> _root_.Yoland.pay (Ψ) m (δ)
local notation "pQ" s:max=> _root_.Yoland.frame (Ψ) m (P.macroStep s) (_root_.Yoland.dawn (Ψ) (δ))
local notation "uQ" V:max=> MiterT.cloud P d C D x (shuf V (-(δ)))
local notation "ν" s:max=> Λ (recoup P d C D ξ s j)
local notation "Rj" s:max=>Hemlock.radius P d s+‖ν s-y‖
include v b
lemma point_prep(U:SampleDose)(h:claimV w U): Q₀ U=(YQ) (uQ U):=
 (financed x d C D j y v U w h b m).trans (congrArg (fun k:(H)=> (YQ) k) (translate x d C D j y v U w h b (r:=w-tidal P d j) rfl).symm)
lemma point_norm(U:SampleDose)(h:claimV w U): ‖Q₀ U‖ ≤ allowanceV U * (‖YQ‖*‖y‖):=by
 let V':= shuf U (-(δ)); have he:claimV ι V':=by
    intro i k; have hv:= h _ ((shuf_iff ..).mp k); rw [Pi.sub_apply,location₁] at hv; linarith
 let m':= (YQ)
 let g':= uQ U
 have hv:‖g'‖ ≤ allowanceV U * ‖y‖:= (cloud_cost x d C D j y v V' he).trans_eq (congrArg (fun t:ℝ=>t * ‖y‖) (shuf_charge U _))
 exact (congrArg (fun z:(H)=>‖z‖) (point_prep d C D w m j y v b U h)).trans_le (((m'.le_opNorm g').trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))).trans_eq (by ring))
variable (M:Morn P.par.K)(p:∀ s:ℕ,d ≤ s → Accordance P M d s (C s) (D s))(t:RobeRoad P d C D x)
omit v b

private lemma thy {R:Hilbert}(x:R)(r:ℕ→R.Op)(g:R.Op)(q:ℕ→R)(p:Tendsto q atTop (𝓝 x))(b:ℕ→ℝ)(h:Tendsto b atTop (𝓝 (0:ℝ)))(v:Tendsto r atTop (𝓝 g)): Tendsto (fun s=>‖r s‖ * (b s+ ‖q s-x‖) + ‖r s-g‖*‖x‖) atTop (𝓝 0):=by simpa only [add_zero,mul_zero,zero_mul] using ((v.norm.mul (h.add (tendsto_iff_norm_sub_tendsto_zero.mp p))).add ((tendsto_iff_norm_sub_tendsto_zero.mp v).mul (show Tendsto (fun _ : ℕ=> ‖x‖) atTop (𝓝 ‖x‖) from tendsto_const_nhds)))
include B a v b e
set_option maxHeartbeats 600000 in
/-- order-zero gapped distributions (also for all time-difference symbols), op-norm uniform in supported L¹-weights. -/
lemma funded₀ : ∃ (Y:ℕ→ℝ)(K:ℝ), 0 ≤ K ∧ Tendsto Y atTop (𝓝 (0:ℝ)) ∧ (∀ (U:SampleDose),claimV w U→ ‖Q₀ U‖ ≤ allowanceV U * K ∧
 Integrable (fun z:Vantage=> (U.val z:ℂ) • zoomV x d C D m z))∧ ∀ᶠ s:ℕ in atTop,∀ U:SampleDose,claimV w U→ ‖works B Z d C D s m U-Q₀ U‖ ≤ allowanceV U * Y s:=by
 let k:=y
 let j₀:=j; let g₀:=a; let h₂:=v; let l₀:=b
 let ha:= tidal P d j₀ -- local ι not θ
 let η:=w-ha; let A:=_root_.Yoland.pay (Ψ) m η; let F(s):= _root_.Yoland.frame (Ψ) m (P.macroStep s) (_root_.Yoland.dawn (Ψ) η)
 let Qs(s):=‖Λ (recoup P d C D ξ s j₀)-k‖
 let y'(s):=Hemlock.radius P d s + Qs s
 let L(s:ℕ):=‖F s‖ * y' s + ‖F s-A‖*‖k‖
 refine ⟨L,‖A‖ * ‖k‖,by positivity,?_,fun U h=>⟨point_norm d C D w m j₀ k h₂ l₀ U h, integrationV x d C D j₀ k h₂ U w h l₀ m⟩,?_⟩
 · have hf:Tendsto F atTop (𝓝 A):= lobeR (Ψ) η (sub_pos.mpr l₀) m _ (P.macroStep_pos) ( macroStep_zero P)
   exact thy (R:=H) k F A _ h₂.1 _ (radiusTiny P d) hf
 filter_upwards [eventually_ge_atTop j₀,(recessVanish P d).eventually (ge_mem_nhds (tide_price P d j₀))] with s hs e₀ U h
 let P₀:= vistaH B Z d C D s
 exact (congrArg (fun z:(H)=> ‖works B Z d C D s m U-z‖) (point_prep d C D w m j₀ k h₂ l₀ U h)).trans_le (teen B Z d C D j₀ k h₂ w l₀ U s m g₀ hs e₀ h)
#print axioms point_norm
#check @funded₀
#print axioms funded₀
#check @coreH
omit a v b
include B p t
set_option maxHeartbeats 750000 in
lemma funded : ∃ (Y:ℕ→ℝ)(K:ℝ), 0 ≤ K ∧ Tendsto Y atTop (𝓝 (0:ℝ)) ∧ (∀ (U:SampleDose),claimV w U→ ‖Q₀ U‖ ≤ allowanceV U * K ∧
 
 Integrable (fun z:Vantage=> (U.val z:ℂ) • zoomV x d C D m z))∧ ∀ᶠ s:ℕ in atTop,∀ U:SampleDose,claimV w U→ ‖works B Z d C D s m U-Q₀ U‖ ≤ allowanceV U * Y s := by
 let v:= ((eventually_ge_atTop d).and ((recessVanish P d).eventually (gt_mem_nhds e))).exists
 let s:=v.choose
 have h:=v.choose_spec
 let hc:=coreH P M d C D x p t s h.1
 exact funded₀ B Z d C D w e m s hc.choose hc.choose_spec h.1 h.2
#print axioms funded
#check @funded
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
