import YM.CF.Milo.Table
import YM.CF.Milo.Sucre
import YM.CF.Milo.Leg
import YM.CF.Sour.Rate
import YM.CF.Sour.Millet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
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
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
namespace Glyph
variable {δ a b u e W:ℝ}{μ:Toll (Single n)}{S:Support (More n)}
variable (F:Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t: Suite (badge _) (bail n δ) (bail n δ) S μ F)
variable {H:Op (Single n)→FC (Dwell n)}{Z':Single n→ Single n→ FC (Dwell n)}{h:ℝ}(f: Glyph H Z' h)
variable (T:Scree.Hub n)(z:T.val.1∈ S)(x:S∈αW P.B (Bake.lagE T))
local notation "B"=> P.B
local notation "Y'"=> Bake.lagE T
local notation "Xv"=> Glyph.cure H p g F
variable (v: q+10≤ P.B)(r:P.threshold ≤ a) (A:Ids n)(V: Pane n)
open Ione Bake Nor Larch
local notation "Hz"=>Scree.Hub n
abbrev panel(P:BudgetPoint)(T:Scree.Hub n):Finset (Support (More n)) :=(αW P.B (lagE T)).filter fun S=> T.val.1∈ S
def picture (P:BudgetPoint)(H:Op (Single n)→FC (Dwell n))(T:Scree.Hub n) (U:InkD n):Prop:=∀ i:Orbit n,(U i.1).val=Sault.rind (coll_T P (lagE T) ∅ (Glyph.cure H p g F) i)
-- select full freeze on X.elector.Z no Toot. total.
def vote (P:BudgetPoint)(H:Op (Single n)→FC (Dwell n))(T:Scree.Hub n):InkD n:=if h:∃ U:InkD n, picture F p g P H T U then Classical.choose h else 0
lemma picture_I {U W:InkD n}(h:picture F p g P H T U)(e:picture F p g P H T W):U=W:=by funext i; exact Subtype.ext ((h (i,A₁)).trans (e (i,A₁)).symm) -- A₁ drop
where A₁:=Classical.arbitrary (Ids n)
variable (p0:HopeT δ b e P.order)(s:P.threshold ≤ e)(hQ:cipherK q≤5*P.B)(hB:3≤ P.B)(hx:1 ≤ h)
include v r t z x f p0 s hQ hB hx
local notation "K'"=> (vote F p g P H T)
lemma express : picture F p g P H T K'∧PressB P T K' h (Vow.fareX 1 P S * Glyph.vest P h μ):=by
 obtain ⟨V,H',W'⟩:= seeds F p g t f T z x v r p0 s hQ hB hx; have hu:∃ U: InkD n,picture F p g P H T U:=⟨V,H'⟩; unfold vote; rw [dif_pos hu,picture_I _ _ _ _ (Classical.choose_spec hu) (show picture F p g P H T V from H')]; exact ⟨H',W'⟩ -- tune K' z includes r
omit z x t
abbrev pay_η (Q:Support (More n)→Toll JS)(S:Support (More n)):ℝ:= (S.card:ℝ)⁻¹ * (fareX 1 P S * vest P h (Q S))
variable (Q:Support (More n)→Toll (Single n))(F':Support (More n)→ Raw (Openc (More n) δ) (Single n))(Qx:∀ S, Suite (badge _) (bail n δ) (bail n δ) S (Q S) (F' S))
-- equal Eval. Cost payload will later be billed. RG sum recovers birth. do not aggregate supports across.
def doveK(P:BudgetPoint)(H:Op JS→ FC (Dwell n))(T:Scree.Hub n):InkD n:= ∑ S∈panel P T,(S.card:ℝ)⁻¹ •vote (F' S) p g P H T
include Qx
lemma law : PressB P T (doveK p g F' P H T) h (∑ i∈panel P T,pay_η (h:=h) (P:=P) Q i):=by
 apply Larch.prop_sum; intro i l; obtain ⟨t',w⟩:=mem_filter.mp l; have hp:abs ((i.card:ℝ)⁻¹) = _:= (show |(i.card:ℝ)⁻¹|=(i.card:ℝ)⁻¹ from abs_of_nonneg (by positivity)); have he:=scale_E P ((express (F' i) p g (Qx i) f T w t' v r p0 s hQ hB hx).2) ((i.card:ℝ)⁻¹); rw [hp] at he; exact he
end Glyph
end YM.CF.Sour
