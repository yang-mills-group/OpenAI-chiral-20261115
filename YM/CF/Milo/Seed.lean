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
include v r g t p x
lemma clean₀ (i:Pane n)(h:pingS P.threshold T.val.2 i)(Z:Ids n): Agrees S (K ((i,Z):Orbit n)) i:=by
 have hx: Lattice.halo (q+10) S ⊆ (Y').val:= (mem_filter.mp x).2 ▸ Corona.halo_mono v le_rfl
 intro e w c; exact fern (X:=Y') p r S hx i (show i∈σX P (Bake.lagE T) ∅ from ⟨by rw [sdiff_empty]; exact h,empty_subset _⟩) _ w rfl Z -- fern Xν arg
-- saturation ready.H assign.Es Expr sum off stamp exactly. 
lemma nearby (V W:Orbit n)(a:V.1∈σX P Y' ∅)(e:W.1∈σX P Y' ∅)(l:Agrees S V.1 W.1): (Xv) V=(Xv) W:=by
 have hv:Agrees S (K V) V.1:=clean₀ F p g t T x v r V.1 (by have h:=a.1; rw [sdiff_empty] at h; exact h) _
 have ht:Agrees S (K W) W.1:=clean₀ F p g t T x v r W.1 (by have h:=e.1; rw [sdiff_empty] at h; exact h) _
 exact congrArg H (pact_p g p t V W fun i s k=> (hv _ s k).trans ((l _ s k).trans (ht _ s k).symm))
variable (p0:HopeT δ b e P.order)(s:P.threshold ≤ e)(hQ:cipherK q≤ 5*P.B)(hB:3 ≤ P.B)(hx:1 ≤ h)
local notation "Λ"=> (Glyph.sail_p f p g t r (show Lattice.halo (cipherK q) (∅:Support _)⊆ (Bake.lagE T).val by simp [Lattice.halo]) hQ hB (show Lattice.halo (q+10) S ⊆(Bake.lagE T).val from (mem_filter.mp x).2 ▸ (Corona.halo_mono v le_rfl)) (subset_refl (Bake.lagE T).val) p0 s)
include p0 s hQ hB hx z f
-- Atlas provide function.Funproj.T.Tag bound.Size.W.t2 for S.Anchor. Δ pressure birth estimate. 
lemma seeds: let U:= Sault.rind; ∃ V:InkD n,(∀ i:Orbit n,(V i.1).val= U (coll_T P Y' ∅ Xv i))∧PressB P T V h (Vow.fareX 1 P S * Glyph.vest P h μ):=by
 intro U; let G:=Λ; let F':Copy n:=G.toCrate.motion 1
 have he(i:Orbit n): (F' i).val=U (coll_T P Y' ∅ Xv i):=by change U (_* (1:FC (Dwell n)))= _; rw [mul_one]
 have hv:0≤vest P h μ:=mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun i _=>sum_nonneg fun j _=> t.nonn i j)) (sq_nonneg _); have ht:0 ≤ h:=zero_le_one.trans hx; have hs:=G.book (δ:=0) (F:=1) (show Fray P h 0 Y' ∅ (1:Copy n) 1 from ⟨Medal.oneT,fun _ _=>by simp [Lattice.halo]⟩) hB (subset_refl _) ht hv; rw [mul_one] at hs
 have hχ(i:Orbit n): Flour (camp S) (F' i).val:=by rw [he]; unfold U coll_T; split; exact Sault.light_e (stencil f p g t _); exact Sault.light_e (Sector.zero false) -- tune ambiguous
 let A:=Classical.arbitrary (Ids n); have hR(i: Orbit n):F' i=F' (i.1,A):=by
    apply Subtype.ext; rw [he,he]; congr 1; unfold coll_T; split; next p=>
       obtain ⟨u,th⟩:= (pillar (Bake.lagE T).val (open_l P.threshold (Bake.lagE T).val (∅:Support (More n)))).choose_spec.2 i.1; exact nearby F _ _ t T x v r (gloss P Y' ∅ i) (gloss P Y' ∅ (i.1,A)) (th p) (th p) fun _ _ _=>rfl
    rfl
 let V:= Burial F' A; have hF: Dual F' (Y').val S P:=by
    intro i j z vX e; have hu(T':Pane n)(h:pingS P.threshold (Y').val T'):T'∈ σX P Y' ∅:=⟨by rw [sdiff_empty]; exact h,empty_subset _⟩
    apply Subtype.ext; rw [he,he,G.toCrate.pointV i (hu _ z), G.toCrate.pointV j (hu _ vX)]; exact congrArg U (nearby F _ _ t T x v r i j (hu _ z) (hu _ vX) e)
 exact ⟨V,fun i=> (congrArg Subtype.val (hR i)).symm.trans (he i),Stax.lobe T S F' _ hs.merit z hF A hR hχ ht⟩ -- argument order
end Glyph
end YM.CF.Sour
