import YM.CF.Milo.Soul
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Milo.Hand
import YM.CF.Milo.Hue
import YM.CF.Milo.Table
import YM.CF.Milo.Foil
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
open Ione Bake Nor Larch Levier Salt
local notation "Hz"=>Scree.Hub n
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable (w:Sweep n)(M:Elm n κ δ e u)
local notation "R"=> Salt.actY w
local notation "W'"=> moveHub w
local notation "GZ"=> panel P
local notation "Λ"=> Ione.suit_Y w
local notation "Δ"=> sauce w.charge (detX w.s) (Sour.γS w)
variable (i:κ)
variable {e' a' b' :ℝ}(v:P.threshold ≤ a)(bq:q+10 ≤ P.B)(hk:cipherK q ≤ 5*P.B)(uB:3≤P.B)(p0:HopeT δ e' a' P.order)(t0:P.threshold ≤ a')(h0:1≤h)
local notation "Xq"=> fondC p g M H P i
local notation "A0"=> (fun A:Op JS=> Matrix.trace A • (1:FC (Dwell n)))
local notation "Lx"=> (Glyph.fondC p g M A0 P i)
open Haro
local notation "Xb"=> Glyph.fondC p g M (faceD true false) P i
local notation "Ck"=>Pastry.cane (Dwell n)
variable (Wκ:∀ S:Support (More n),S.card≠1→ M.W S=0)
include v p g bq hk uB p0 t0 h0
include Wκ
-- stack number exact on finite torus.no interpolation error.Any depth qual.
lemma rankF(V:Pane n)(u:1<coverNumber P.B T.val.2): Xb T V=0:=by
 unfold fondC doveK; rw [Finset.sum_apply]; apply sum_eq_zero; intro j z; let v':= cheapV p g T M i v bq hk uB p0 t0 h0 Wκ j z ((V,Classical.arbitrary _): Orbit n) u; rw [Pi.smul_apply,show vote _ p g P (faceD true false) T V=0 from v',smul_zero]
lemma sumH (P0: Finset (Scree.Hub n))(t:∀ T:Hz,coverNumber P.B T.val.2 ≤1→T∈P0)(F:Gem n κ)(Q:NearL M F)(W₁:Ids n): let x:Orbit n:=(1,W₁); Haro.StackL Xb P0= F i (roller g p x).val:=by
 intro x; unfold StackL; rw [Finset.sum_subset (subset_univ P0) ?g]; swap
 case g=>
    intro i u v'; rw [rankF p g i M _ v bq hk uB p0 t0 h0 Wκ 1 (lt_of_not_ge (mt (t i) v'))]; ext i j; rw [orbitPH,Matrix.of_apply,Prism.port_eq]; simp [crumb]
 rw [← Finset.sum_fiberwise_of_maps_to (t:= Finset.univ) (g:=Bake.lagE) (fun i _=>mem_univ _)]
 let X:=roller g p x; have hx(T): (∑ j∈web0 T, orbitPH (Xb j x.1))=∑ U∈αW P.B T,M.F U i X:= matrix_f p g M i v bq hk uB p0 t0 h0 T x (ping_f P _)
 rw [sum_congr rfl (fun T u=>hx T),Q _ _ _ (p.paid x) rfl,sum_sigma']; let H:=univ.filter fun S:Support (More n)=> S.Nonempty
 rw [←sum_subset (s₁:=H) (subset_univ H)]; swap; · intro j _ u; have hw:j=∅:=Finset.not_nonempty_iff_eq_empty.mp (fun x=>u (mem_filter.mpr ⟨mem_univ _,x⟩)); subst j; ext i' j'; apply norm_le_zero_iff.mp; have hv:=(M.coat ∅|>.1 i).expo i' j'|>.bounded X; rw [Wκ ∅ (by simp)] at hv; exact hv -- tune rw sum_subset matches
 refine sum_bij (fun i _=>i.2) ?_ ?_ ?_ (fun i _=>rfl)
 · rintro ⟨a,b⟩ t; obtain ⟨x,q⟩:= a.property; have hx:= (mem_filter.mp (mem_sigma.mp t).2).2; obtain ⟨i,l,w⟩:= halo_spec.mp (show x∈halo P.B b from (show a.val= _ from hx) ▸ q); exact mem_filter.mpr ⟨mem_univ _,i,l⟩
 · rintro ⟨a,b⟩ t ⟨l,d⟩ v rfl; rw [show a=l from Subtype.ext ((show a.val=halo P.B b from (mem_filter.mp (mem_sigma.mp t).2).2).trans ((show l.val=_ from (mem_filter.mp (mem_sigma.mp v).2).2).symm))]
 intro i u; have hx: (halo P.B i).Nonempty:= ((mem_filter.mp u).2).mono (halo_subset ..); exact ⟨⟨⟨halo _ i,hx⟩,i⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,rfl⟩
end Glyph
end YM.CF.Sour
