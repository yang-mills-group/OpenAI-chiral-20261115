import YM.CF.Vow.Fair
import YM.CF.Vow.Law
import YM.CF.Stax.Flow
import YM.CF.Vp929.Match.Rays

/- XIX/XXI. Port of Vow/Fair:enough_v for halo assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
variable {X D Y Z:Support (More n)}{U:Pane n}
-- all seeds use child scales $Y∈H$. cost numerator.Post.S.Unit. equations read even if paux markers.H.St.
open Trees
variable {K W:Cusp n}
variable {C:blazeK n}{G:Aura n→ℝ}
variable(S:Aura n)(T:Finset (Palot.Duo (More n))) (p:D⊆S.val)
def sheltersForce (r:ℕ)(F:ForceBudget n):Prop:=∀ i:Scree.Force n,∀ x:Orbit n,F i x≠0→ halo r i.val.2⊆i.val.1.val.2
def shelters (r:ℕ)(F:Cusp n):Prop:=∀ (i:Aura n)(D:Support (More n)), D.Nonempty→ D⊆i.val→∀ x:Orbit n,F i D x≠0→ halo r D⊆i.val

variable {r:ℕ}(w:shelters r K)
include p w in
lemma shelterGem (V:Orbit n)(g:gemB D K W T (beamH S.val) V ≠0): halo r D⊆ S.val:=by
 rw [gear_v] at g; split at g; swap; · exact False.elim (g rfl)
 rename_i h
 intro x u
 obtain ⟨y,hy,z⟩:= Lattice.halo_spec.mp u
 obtain ⟨i,v,q⟩:=deck_r S T p h y hy
 let D':= D∩i.val
 have hp:K i D' V ≠0:=by
    intro a; apply g; rw [Pi.mul_apply,Finset.prod_apply,prod_eq_zero v a,zero_mul]
 let H:= stun_v S T h i v
 exact H.2 (w i _ H.1 inter_subset_right V hp (halo_spec.mpr ⟨_,q,z⟩))
lemma shelters.glow (W:Cusp n) {r:ℕ}(w:shelters r K): shelters r (glowV K W):= by
 intro i D _ p V hx; unfold glowV mintF at hx; rw [if_pos p,Finset.sum_apply] at hx; obtain ⟨T,-,g⟩:=exists_ne_zero_of_sum_ne_zero hx; exact shelterGem i T p w V g
lemma shelters.force {r:ℕ}(w:shelters r K):sheltersForce r (budgetR K):=by
 intro i V hx; apply w (lordD i) (extraD i) i.property.1 i.property.2 V; intro h; change ((_ :ℝ) • K (lordD i) (extraD i) V≠0) at hx; apply hx; rw [h,smul_zero]
end YM.CF.Vow

/- Adapt Rays.assertK. At the very same rate. -/
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
local notation "gΨ"=> degreePrice p.B θΓ wΨ
local notation "Upp"=> uk_b (rentΦ p γΓ dΓ) vδ θΓ gΨ
local notation "αΒ"=> p.supportExponent+1+1
include Ω Th
lemma shelter_chest (u:ℂ)(i:πχ)(F:VK)(pA:Billable p W B F m₁ m₂)(q:‖u‖=1): Vow.shelters (cipherK B) (Ω.chest i F u):=by
 obtain ⟨I,t,pL,q'⟩:=pA
 let op:opV I 1:= (Ω.honor Th (fun i j v=> (t i j v).merit.wage (zero_le_one.trans Ω.floor)) pL q').1
 have hv:0 ≤ ρL p:=by unfold ρL wΨ; linarith [p.exponent_pos]
 have hu:ρL p ≤ wu p:= by unfold ρL wu wΨ; linarith
 have hp:0 < wΨ:=by norm_num [wΨ]
 let P:= Th.transit
 have h:= Stax.rentK F I t (Ω.κm i u) Xp (Ω.kernel u i q).1 _ _ _ _ _ _ _ _ _ _ _ op hp hv (by unfold ρL wΨ wu; linarith) Ω.floor
 intro x D hh he V p; exact ((h.1 x D he).1.loaf V p).1
end Technique
end MatchW
end YM.CF.Sour
