import YM.CF.Sour.Lumen
import YM.CF.Sour.Lead
import YM.CF.Sour.Park
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
-- sum actual stencils 
variable {δ a v u e:ℝ}{μ:Support (More n)→ Toll (Single n)}
variable (F:Support (More n)→Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t:∀ S, Suite (badge _) (bail n δ) (bail n δ) S (μ S) (F S))
variable (H:Op (Single n)→ FC (Dwell n))(Z:Single n→Single n→FC (Dwell n))(h:ℝ)(f: Glyph H Z h)
local notation "A0"=> actsF H F p g P.B
local notation "Ω"=> Openc (More n) δ
lemma Marque.tiltR{ι:Type*}(S:Finset ι)(Q:ι→ Firing n)(v:ι→ℝ)(hQ:∀ i∈S,Marque P X Y D (Q i) h (v i)):Marque P X Y D (∑ i∈S,Q i) h (∑ i∈S,v i):=by
 refine ⟨⟨(by rw [show (∑ i∈S,Q i)= fun V=> ∑ i∈S,Q i V from funext (fun i=>Finset.sum_apply ..)]; exact Finset.measurable_fun_sum _ (fun i g=> (hQ i g).cog)),fun i=> ?_,fun i j u w l n=> ?_,fun i t x=>?_ ⟩,(AuraOp.sumR h S Q v (fun i h=> ⟨(hQ i h).vet⟩)).pay⟩
 · rw [Finset.sum_apply]; exact Sector.sumS _ _ (fun j g=> (hQ j g).body i)
 · rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl fun j' g=> (hQ j' g).same _ _ u w l n
 rw [Finset.sum_apply, Finset.sum_apply, sauce, singT, win_sum, map_sum]; exact sum_congr rfl fun j u=> (hQ j u).gauge _ t x
include t f
lemma earned(p0:HopeT δ u v P.order)(s:P.threshold ≤ v)(r:P.threshold ≤ a)(w: q+10 ≤ P.B)(t0: cipherK q≤5*P.B)(tp:3≤P.B) :Bias (cipherK q) A0 P h (noteR (P:=P) h μ):=by
 refine ⟨fun i x=>?_,fun X=>?_,fun X Y D k l q=>?_⟩
 · unfold actsF; rw [Finset.sum_apply]; apply Sector.sumS; intro j s; refine lift_v (Glyph.stencil f p g (t j) x) ?_; rw [(mem_filter.mp s).2]; intro k t; exact mem_filter.mpr ⟨mem_univ _,halo_subset _ _ (mem_filter.mp t).2⟩
 · exact sum_nonneg fun j _=> mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun x _=>sum_nonneg fun y _=>(t j).nonn _ _)) (by positivity)
 exact Marque.tiltR h _ _ _ (fun i h=> by -- tune args included?
    apply Glyph.sail_p f p g (t i) r q t0 tp ?_ k p0 s; rw [(mem_filter.mp h).2]; exact Corona.halo_mono w le_rfl)
lemma lute(i:Orbit n):∑ Y: VX,A0 Y i = H (∑ S:SO,F S (roller g p i)):=by
 let M:= Glyph.cure H p g; let S:=univ.filter fun T:Support (More n)=>T.Nonempty
 have he:μ ∅=0:=by funext x y; by_contra h; exact notMem_empty _ ((t ∅).expo x y|>.triggered h).2.1
 have hp:F ∅ (roller g p i)=0:=by ext x y; exact norm_le_zero_iff.mp (le_trans (((t ∅).expo x y).bounded _) (by rw [he]; rfl)) -- tune goal
 have ht:∑ U:SO,F U (roller g p i)=∑ U∈S,F U (roller g p i):= (sum_subset (subset_univ S) (fun j w x=>by have hv:¬j.Nonempty:=fun v=>x (mem_filter.mpr ⟨w,v⟩); rw [not_nonempty_iff_eq_empty.mp hv]; exact hp)).symm -- replace
 rw [ht]; unfold actsF; simp_rw [Finset.sum_apply]
 trans ∑ x∈S,M (F x) i
 · rw [sum_sigma']; refine sum_bij (fun x _=>x.2) ?_ ?_ ?_ (fun _ _=>rfl)
   · intro j x; obtain ⟨-,g⟩:=mem_sigma.mp x; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; obtain ⟨a,w⟩:=j.1.property; rw [(mem_filter.mp g).2] at w; obtain ⟨y,g,p⟩:=halo_spec.mp w; exact ⟨_,g⟩
   · rintro ⟨x,y⟩ u ⟨Y,W⟩ w rfl; rw [show x=Y from Subtype.ext ((show x.val=halo P.B y from (mem_filter.mp (mem_sigma.mp u).2).2).trans ((show Y.val= _ from (mem_filter.mp (mem_sigma.mp w).2).2).symm))] -- tune
   intro x h; have ht: (halo P.B x).Nonempty:= ((mem_filter.mp h).2).mono (halo_subset ..); exact ⟨⟨⟨_,ht⟩,x⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,rfl⟩
 unfold M Glyph.cure; simp_rw [f.whirl,Matrix.sum_apply,sum_smul]; rw [sum_comm]; exact sum_congr rfl fun _ _=> sum_comm
end YM.CF.Sour
