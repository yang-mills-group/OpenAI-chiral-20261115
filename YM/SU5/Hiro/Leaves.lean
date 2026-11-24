import YM.SU5.Hiro.Patch
import YM.SU5.Circuit.Concert
import YM.SU5.Circuit.Zinnias
import YM.SU5.Regis.Voyance
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function NormedSpace Filter Metric Fock SU Finset Lat Lattice Cube RP Reflect Nacre -- remove unknown
open Wilson Push.SectorMeasure RG Cube Lat Spire Scroll ProbabilityTheory MeasureTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Buffered.Lifted Cliplet Reed CF.Lamour.Bridge CF.Lamour.Bridge.Celeste
open Girt
open Afterglow -- tune
open Pannier Regis.Head Preparation Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical ContDiff Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Regis.Head.Brecht Next.SectorChange
open YM.Stationary (Gaia)
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l)) (K H:ℕ→ℕ)
local notation "Yk"=>Y.voyage
local notation "G"=>SU.group
local notation "L"=>P.R.L
local notation "Λ"=>P.V.L
variable {K H} (h:Real.exp 1≤ P.x)
variable {T:ℕ→ Buffered.Family (tent Y h)→ℕ→ℂ} {E:ℕ →Buffered.Family (tent Y h)→ℂ} (V:Universal Y h K H T E)
variable (F D:PlaqAxes) {R t:ℕ→ℝ}{U W:ℕ→ Cover} {X:Gaia}
local notation "A"=>speckleV F D SU.group X
variable (u:∀ i,0<R i)(w:Tendsto R atTop atTop) (Z:Tendsto (fun i=>Onyx.riseX (R i) (U i-W i)) atTop (𝓝 X)) (j:X≠0) (f:∀ i,0<t i)(p:Tendsto (fun i=> R i^4/t i) atTop (𝓝 0))
local notation "Δ" i:max=> (R i:ℂ)^4
local notation "μF" i:max=> plateView F D (U i) (W i) G (f i)
def Hu : ℂ → ℂ → ℝ → ℝ → ℂ:= fun a c t u=>a*(t:ℂ)-(u:ℂ)^2*c
private lemma flow_hu {P Q:ℂ}{f g:ℕ→ℝ}{x y:ℝ}(B:Tendsto f sceneL (𝓝 x))(G₁:Tendsto g sceneL (𝓝 y)): Tendsto (fun i=> ‖Hu P Q (f i) (g i)‖) sceneL (𝓝 ‖Hu P Q x y‖):= Filter.Tendsto.norm (((Complex.continuous_ofReal.continuousAt.tendsto.comp B).const_mul P).sub (((Complex.continuous_ofReal.continuousAt.tendsto.comp G₁).pow 2).mul_const Q))
include u w Z j f p V
lemma chicory (ε:ℝ)(θ:0<ε):∀ᶠ i in atTop,∀ s,‖Hu (Δ i) A (ornament (μF i) Y K H s) (Aster Y K H s)‖≤ ε:=by
 let Q:=P.K; let P₁:= Q.top; let q:= P₁.clip
 filter_upwards [quoteA F D q (P.V.W.parcel) Q.width (zero_lt_one.trans_le P.V.up) u w Z j G f p ε θ] with i h' s
 let k:=μF i; apply le_of_tendsto (flow_hu (P:=Δ i) (Q:=A) (terrace_ultra k Y K H s).2 (astral Y K H s).2)
 apply Nat.hyperfilter_le_atTop; filter_upwards [((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually h'] with m hp
 let a:= K m; let n:=count Y s a; apply le_of_tendsto (flow_hu (P:=Δ i) (Q:=A) (innerTel k Y H s a).2 (tint_height Y H s a).2)
 apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y s a)] with j x
 let y:=Y.uv (H j)-s; let b:=H j; let x':=overlay Y s a b; have he:x'=actual Y s a b:= afforded Y s (((Real.exp_pos 1).trans_le h).trans_le (Vale.crown L P.x s)) a b x.enters
 have hx:=actual_span Y s a b; have hy:= P.V.L.roof y; have hy':hy=hy:=rfl; change ‖Hu (Δ i) A (hatsMuseo Y k s a b) (actual Y s a b)‖≤ _; rw [← he]; exact hp (P.V.L.H y) hy.1 (hy.2.1 _) (P.V.L.path y) (P.V.L.mood y) (P.V.L.tied y) x' (by rw [he,abs_of_pos ((by norm_num: (0:ℝ)<1/2).trans_le hx.1)]; exact hx.2)
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.chicory
