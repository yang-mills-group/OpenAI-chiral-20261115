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
private lemma height_atlas(x:ℕ→ℝ)(p:∀ i,x i∈ Set.Icc (1/2:ℝ) 2): ∃ T:ℝ,T∈Set.Icc (1/2:ℝ) 2 ∧ Tendsto x sceneL (𝓝 T):= IsCompact.ultrafilter_le_nhds' (f:=(Filter.hyperfilter ℕ).map x) isCompact_Icc (show ∀ᶠ i in sceneL,x i∈Set.Icc (1/2:ℝ) 2 from Eventually.of_forall p)
abbrev overlay(s i k:ℕ):ℝ:= museumV (P:=P) s * coupling (gram Y s i k).beta
abbrev actual(s i k:ℕ):ℝ:= min 2 (max (1/2) (overlay Y s i k))
lemma actual_span(s i k:ℕ): actual Y s i k∈Set.Icc (1/2:ℝ) 2:= ⟨le_min (by norm_num) (le_max_left ..),min_le_left ..⟩
abbrev tint (s i:ℕ):= (height_atlas _ (fun j=> actual_span Y s i (H j))).choose
lemma tint_height (s i:ℕ): tint Y H s i∈Set.Icc (1/2:ℝ) 2∧ Tendsto (fun j=>actual Y s i (H j)) sceneL (𝓝 (tint Y H s i)):= (height_atlas _ (fun j=> actual_span Y s i (H j))).choose_spec
def Aster (s:ℕ):ℝ:= (height_atlas _ (fun i=> (tint_height Y H s (K i)).1)).choose
lemma astral (s:ℕ): Aster Y K H s∈Set.Icc (1/2:ℝ) 2∧ Tendsto (fun i=> tint Y H s (K i)) sceneL (𝓝 (Aster Y K H s)):= (height_atlas _ (fun i=> (tint_height Y H s (K i)).1)).choose_spec
variable {K H} (h:Real.exp 1≤ P.x)
variable {T:ℕ→ Buffered.Family (tent Y h)→ℕ→ℂ} {E:ℕ →Buffered.Family (tent Y h)→ℂ} (V:Universal Y h K H T E)
variable (F D:PlaqAxes) {R t:ℕ→ℝ}{U W:ℕ→ Cover} {X:Gaia}
local notation "A"=>spectrumColor F D SU.group X
variable (u:∀ i,0<R i)(w:Tendsto R atTop atTop) (Z:Tendsto (fun i=>Onyx.riseX (R i) (U i-W i)) atTop (𝓝 X)) (j:X≠0) (f:∀ i,0<t i)(p:Tendsto (fun i=> R i^8/t i) atTop (𝓝 0))
local notation "Δ" i:max=> (R i:ℂ)^8
local notation "φ" i:max=> blazing SU.group F (U i) (t i) (f i)
local notation "χ" i:max=> blazing SU.group D (W i) (t i) (f i)
local notation "Φ" i:max s:max=>ornament (φ i) Y K H s
local notation "Ψ" i:max s:max=>ornament (χ i) Y K H s
def Horo(F:ℂ)(R:ℂ)(t u v b:ℝ):= F*(↑(t-u*v):ℂ)-(b:ℂ)^4*R
private lemma cont_flux {P Q:ℂ}{f g h d:ℕ→ℝ}{x y z w:ℝ}(B:Tendsto f sceneL (𝓝 x))(G₁:Tendsto g sceneL (𝓝 y))(H:Tendsto h sceneL (𝓝 z))(D:Tendsto d sceneL (𝓝 w)): Tendsto (fun i=> ‖Horo P Q (f i) (g i) (h i) (d i)‖) sceneL (𝓝 ‖Horo P Q x y z w‖):= Filter.Tendsto.norm (((Complex.continuous_ofReal.continuousAt.tendsto.comp (B.sub (G₁.mul H))).const_mul P).sub (((Complex.continuous_ofReal.continuousAt.tendsto.comp D).pow 4).mul_const Q))
lemma afforded (s:ℕ)(a:0<Vale.hat L P.x s)(i k:ℕ)(p:s≤Y.uv k): overlay Y s i k = actual Y s i k:=by obtain ⟨b,c,d,v,g⟩:=prices_plot Y s i k p; have h: overlay Y s i k∈Set.Icc (1/2:ℝ) 2:= Etch.railB v.1 v.2 a; rw [actual,max_eq_right h.1,min_eq_right h.2]
include u w Z j f p V
lemma imagery (ε:ℝ)(θ:0<ε):∀ᶠ i in atTop,∀ s,‖Horo (Δ i) A (ornament ((φ i).radial (χ i)) Y K H s) (Φ i s) (Ψ i s) (Aster Y K H s)‖≤ ε:=by
 let Q:=P.K; let P₁:= Q.top; let q:= P₁.clip
 filter_upwards [quoteV F D q (P.V.W.parcel) Q.width (zero_lt_one.trans_le P.V.up) u w Z j G f p ε θ] with i h' s
 let g:=φ i; let v:=χ i; let k:= g.radial v; apply le_of_tendsto (cont_flux (P:=Δ i) (Q:=A) (terrace_ultra k Y K H s).2 (terrace_ultra g Y K H s).2 (terrace_ultra v Y K H s).2 (astral Y K H s).2)
 apply Nat.hyperfilter_le_atTop; filter_upwards [((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually h'] with m hp
 let a:= K m; let n:=count Y s a; apply le_of_tendsto (cont_flux (P:=Δ i) (Q:=A) (innerTel k Y H s a).2 (innerTel g Y H s a).2 (innerTel v Y H s a).2 (tint_height Y H s a).2)
 apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y s a)] with j x
 let y:=Y.uv (H j)-s; let b:=H j; let x':=overlay Y s a b; have he:x'=actual Y s a b:= afforded Y s (((Real.exp_pos 1).trans_le h).trans_le (Vale.crown L P.x s)) a b x.enters
 have hx:=actual_span Y s a b; have hy:= P.V.L.roof y; have hy':hy=hy:=rfl; change ‖Horo (Δ i) A (hatsMuseo Y k s a b) (hatsMuseo Y g s a b) (hatsMuseo Y v s a b) (actual Y s a b)‖≤ _; rw [← he]; exact hp (P.V.L.H y) hy.1 (hy.2.1 _) (P.V.L.path y) (P.V.L.mood y) (P.V.L.tied y) x' (by rw [he,abs_of_pos ((by norm_num: (0:ℝ)<1/2).trans_le hx.1)]; exact hx.2)
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.imagery
