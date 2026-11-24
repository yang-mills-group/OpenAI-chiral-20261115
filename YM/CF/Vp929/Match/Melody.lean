import YM.CF.Vp929.Match.Rays
import YM.CF.Vp929.Pre.Livery
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)
local notation "opV" I:max k:max=> Timer (Cadre.chip (cribR (Ω.note+Ω.note)) I) (Ω.note+Ω.note) r₁ (wu p) wΨ (widthK n p.B) (spanV p.B) γΓ dΓ (spanV p.B*dΓ) dΓ k (Ω.note+Ω.note)
include Ω Th
lemma olderν (F:Vow.Cusp n)(q:Billable p W B F m₁ m₂): MonoQ p W (ρL p) (rebP F) θΓ:=by
 obtain ⟨I,t,pL,q'⟩:=q
 let i:=Classical.arbitrary πχ
 let op:opV I 1:= (Ω.honor Th (fun i j v=> (t i j v).merit.wage (zero_le_one.trans Ω.floor)) pL q').1
 have hv:0 ≤ ρL p:=by unfold ρL wΨ; linarith [p.exponent_pos]
 have hu:ρL p ≤ wu p:= by unfold ρL wu wΨ; linarith
 have hp:0 < wΨ:=by norm_num [wΨ]
 let P:= Th.transit
 obtain ⟨ht,g,G,-⟩:= glyph_c Ω.floor (Ω.κm i I_) (Xp) F I (Ω.kernel _ _ Complex.norm_I).1 t op hv hp (by unfold ρL wΨ wu; linarith) wΨ m₁ vδ θΓ hp le_rfl (fun x=> (tall_m _ (fun i=> (t i _ (empty_subset _)).merit.wage (zero_le_one.trans Ω.floor)) hu x).trans (pL x)) Th.lead P.ht P.earn P.wings
 exact ⟨_,G,dutyK ht⟩
variable {K:Set ℂ}(j:ℂ→Pair (ΘS r))(F:ℂ→Vow.Cusp n)
lemma sunrise_(u:ℂ)(t:‖u‖=1)(pK:IsOpen K)(i:Orbit n)(tF:∀ x∈K,Billable p W B (F x) m₁ m₂)(hF:∀ (X:Aura n),∀ D⊆ X.val,DifferentiableOn ℂ (fun x=> F x X D i) K)(hZ:∀ (X:Aura n)(v:Orbit n),DifferentiableOn ℂ (fun x=> Ω.χm (j x) u X v) K)(X:Aura n)(D:SO)(pD:D⊆ X.val): DifferentiableOn ℂ (fun x=> Ω.chest (j x) (F x) u X D i) K:= by
 let μ(x:ℂ):= if h:x∈K then (tF x h).choose else 0; have he x (p:x∈K):μ x=(tF x p).choose:= dif_pos p
 apply growing F i hF hZ (fun x h=> (Ω.kernel u (j x) t).2) (P₀:=μ) (fun x h=>he x h|>.symm ▸ (tF x h).choose_spec.1) (fun x h=>(Ω.kernel u (j x) t).1) (fun x h=>he x h|>.symm ▸ (Ω.honor Th (fun i D u=> ((tF x h).choose_spec.1 i D u).merit.wage (zero_le_one.trans Ω.floor)) (tF x h).choose_spec.2.1 (tF x h).choose_spec.2.2).2) (by norm_num [wΨ] : 0 < wΨ) (by unfold wu wΨ; linarith [p.exponent_pos]) Ω.floor X D pD pK
lemma nuΦ (u:ℂ)(t:‖u‖=1)(pK:IsOpen K)(v:Orbit n)(pZ:∀ X:Scree.Hub n, DifferentiableOn ℂ (fun x=> Ω.seekR (j x) u X v.1) K)(tF:∀ x∈K,Billable p W B (F x) m₁ m₂)(hF:∀ (i:Orbit n)(X:Aura n),∀ D⊆ X.val,DifferentiableOn ℂ (fun x=> F x X D i) K)(hZ:∀ (X:Aura n)(i:Orbit n),DifferentiableOn ℂ (fun x=> Ω.χm (j x) u X i) K)(X:Aura n):DifferentiableOn ℂ (fun x=> Ω.nuR (j x) (F x) u X v) K:= by
 have hw:0 ≤ p.supportExponent+1+1:=by linarith [p.exponent_pos]
 let pF:FeeBook p.B θΓ wΨ:=⟨Th.transit.ht, by norm_num [wΨ], Th.transit.earn, mul_nonneg (by norm_num) (Trees.stretch_pos _ Th.transit.ht (by norm_num [wΨ])).le⟩
 unfold nuR Nu zenS; split_ifs; swap; · exact differentiableOn_const _
 exact (((pF.analytic hw Ω.floor pK _ (fun x h=>(Ω.assertK Th u (j x) _ (tF x h) t).2.1) (fun X V=> Ω.sunrise_ Th j F u t pK V tF (hF V) hZ X ∅ (empty_subset _)) X v).sub (pF.analytic hw Ω.floor pK _ (fun x h=> Ω.olderν Th _ (tF x h)) (fun X V=>hF V X _ (empty_subset _)) X v)).sub (DifferentiableOn.fun_sum fun x _=>pZ x))
omit Th Ω
local notation "η" => (starRingEnd ℂ) ⁻¹' K
abbrev Scen(K:Set ℂ)(j:ℂ→Pair (ΘS r)):Prop:= Py.Rate.Form K (fun z=> ((j z).1.val,(j z).2.val))
abbrev Queries (K:Set ℂ)(U:ℂ→Pair (Vow.Cusp n)):= Query (fun i=> {z|z⊆ i.val}) K U
lemma probe_line {X Y:Type*}{E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E][FiniteDimensional ℂ E]
 (U: ΘS r→ X→ Y→ E)(p:Poetic U)(Z:IsOpen K)(t:Scen K j): Census K (fun z=> (U (j z).1,U (j z).2)):= by
 obtain ⟨L,hL⟩:=p; intro i k
 let H:SpaceM→L[ℝ] E := ((LinearMap.proj k).comp ((LinearMap.proj i).comp L)).toContinuousLinearMap
 unfold Scen at t; exact ((t.probe H).congr (fun u v=> Prod.ext (congrFun (congrFun (hL _).symm i) k) (congrFun (congrFun (hL _).symm i) k))).holo Z
variable (Y0:ℂ→Pair (Vow.Cusp n))(pZ:IsOpen K)(t:Scen K j)
include Ω Th t pZ
lemma trackZ (hY:Queries K Y0)(pY:∀ u∈K,Coverable p W B (Y0 u) m₁ m₂): Queries K (fun u=> Ω.waveW (j u) (Y0 u)) ∧ Census K (fun u=> Ω.νpoint (j u) (Y0 u)):=by
 let j' z:=j (star z)
 let Δ:= Ω.chest; let Λ':=Ω.χm
 let F (z:ℂ):= Pair.plus (Y0 z); let G(z:ℂ):= Pair.minus (Y0 (star z))
 let A(z:ℂ):= Δ (j z) (F z) I_; let Z(z):= Δ (j' z) (G z) (-I_)
 let B:= probe_line j Ω.lerC Ω.lerQ.2.2 pZ t
 let H:= probe_line j Ω.lyr (Ω.lerQ.1.add Ω.lerQ.2.1) pZ t
 -- plus equals A.entry! minus post after conjugate.
 have hF(i:Orbit n)(X:Aura n)(D:SO)(u:D⊆ X.val): DifferentiableOn ℂ (fun z=> F z X D i) K:= (hY X D u i).1
 have hG(i:Orbit n)(X:Aura n)(D:SO)(u:D⊆ X.val): DifferentiableOn ℂ (fun z=> G z X D i) η:= (hY X D u i).2
 let t₀:= pZ.preimage Complex.continuous_conj
 have hZ(X i): DifferentiableOn ℂ (fun z=> Ω.χm (j z) I_ X i) K:= B.plus_curve X i
 have ht(X i): DifferentiableOn ℂ (fun z=> Ω.χm (j' z) (-I_) X i) η := (B.minus_curve X i).congr fun a y=> by unfold χm j' Pair.minus; rw [neg_smul,←sub_eq_add_neg]
 have u:‖-Complex.I‖=1:=by simp
 constructor
 · intro X D a i; exact holo_cat (f:=fun z=>A z X D i) (g:=fun z=> Ω.chest (j z) (Pair.minus (Y0 z)) (-I_) X D i) (Ω.sunrise_ Th j F I_ Complex.norm_I pZ i (fun u h=>(pY u h).1) (hF i) hZ X D a) (Ω.sunrise_ Th j' G (-I_) u t₀ i (fun u h=>(pY _ h).2) (hG i) ht X D a)
 refine Census.recombine (fun X k=> Ω.nuΦ Th j F I_ Complex.norm_I pZ k (fun j=> (H.plus_curve j k.1)) (fun u h=>(pY u h).1) hF hZ X) (fun X k=> Ω.nuΦ Th j' G (-I_) u t₀ k (fun Y=>?_) (fun u h=>(pY _ h).2) hG ht X)
 exact (H.minus_curve Y k.1).congr fun a _=> by unfold seekR j' Pair.minus; rw [neg_smul,←sub_eq_add_neg]
lemma trackTX (hY:Queries K Y0)(pY:∀ u∈K,Coverable p W B (Y0 u) m₁ m₂)(τ:Ids n)(U0:ℂ→Pair (RegBudget n))(u:Census K U0) : Census K (fun z=> Ω.txStar (j z) (Y0 z) (U0 z) τ) ∧ Census K (fun z=> Ω.rollT (j z) (Y0 z) (U0 z) τ):=by
 let H:=(Ω.trackZ Th j Y0 pZ t hY pY).2
 have he:Census K (fun z=> Ω.txStar (j z) (Y0 z) (U0 z) τ):=by
    apply Census.plus pZ (u.plus pZ (probe_line j Ω.lerW Ω.lerQ.2.1 pZ t)); intro j0 V; exact (((H (Bake.lagE j0) (V,τ)).form pZ).probe ((bassH (Bake.lagE j0)) • (ContinuousLinearMap.id ℝ (Cipher n)))).holo pZ
 exact ⟨he,Census.plus pZ he (probe_line j Ω.ler Ω.lerQ.1 pZ t)⟩
end Technique
end MatchW
end YM.CF.Sour
