import GaugeFieldConstruction.TorShow
import YM.SU5.FiniteGaugeData.Tower.Base
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}{p:BudgetPoint}{u h t:ℝ}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
lemma dotter (i:Wa n):‖dot_Q i‖≤1:=by
 rcases i with _|⟨b,i,j⟩; · exact norm_one.le
 have ht(j:Single n): ‖put j‖≤1:=by rw [← Fock.create_put]; exact (Flare.cost_pe false _).trans (show ‖basisKet j‖≤1 by simp [basisKet])
 have hf(j:Single n): ‖Fock.takeF j‖≤1:=by unfold Fock.takeF; rw [norm_star]; exact ht _
 cases b; exact (norm_mul_le ..).trans (mul_le_one₀ (hf _) (norm_nonneg _) (ht _)); exact (norm_mul_le ..).trans (mul_le_one₀ (ht _) (norm_nonneg _) (hf _))
lemma earnG {A:Paper n} {v:ℝ}(w:d+6<n.val)(i:jungle x d)(p':Micro p (knotX x d n) (A (hereV n i)) v) (Y:PairsC): ‖glorified (Pvi n x d A) i p.threshold Y‖ ≤ v:=by
 unfold glorified; split; swap
 · rw [norm_zero]; exact p'.1
 next h=>
    unfold Pvi; rw [norm_mul,feeV_n,one_mul]; let V:Pane n:= snake x Y.1; let F:= A (hereV n i)
    have hx:= (p'.2.2.2 V ((ping_view x d w Y.1).1 h)).value; unfold Function.comp Shield.solo at hx; rw [smul_zero,G07.at_zero_increment] at hx; exact hx -- tune increment
lemma qCost (w:d+6<n.val)(H:Paper n)(P:TrackD p (knotX x d n) h H t) (i:jungle x d): Coeff true (cartO x (d+4)) (glorified (Pvi n x d H) i p.threshold) :=by
 obtain ⟨V,Q,v⟩:= P; let f:= Pvi n x d H; let B:= hereV n i; have hp:= (Q B).1; have he:Measurable (glorified f i p.threshold):=by
    let g:= f i; let S:Set PairsC:= fun y=> pingV x d p.threshold y.1
    change Measurable (S.piecewise (fun x=>g x.1) (fun _=>0)); apply Measurable.piecewise ((ArtCart.ping_o x d|>.measurableSet).preimage measurable_fst) _ measurable_const -- tune
    exact measurable_const.mul (hp.2.1.meas.comp ((snake_c x|>.measurable).comp measurable_fst))
 have hx:LocalOn (cartO x d) (f i):= pvi_U H (by omega) (fun i=>(Q i).1.2.2.1) i
 refine ⟨nofun,⟨he,V B,earnG w i hp⟩,fun a b w₀ v₀=>?_⟩
 unfold glorified; refine if_congr (?_:pingV x d p.threshold a.1 ↔pingV x d p.threshold b.1)  (hx _ _ fun i p q=>w₀ i (cart_M (c:=d) p (by omega)) (cart_M (c:=d) q (by omega))) rfl; exact ⟨ping_D x d w₀,ping_D x d fun i p q=> (w₀ i p q).symm⟩
-- note d+4 perimeter
lemma philosophy (w:d+6<n.val)(H:Paper n)(P:TrackD p (knotX x d n) h H t)(K:Calibration) (p': Tuned H) :InTest K true (cartO x (d+4)) false (John (Pvi n x d H) K p.threshold):=by
 let F:= Pvi n x d H
 refine InTest.sum _ _ (fun i _=>?_); by_cases h:F i=0
 · rw [show scalar K _*_ = _ from (?_: scalar K (glorified F i p.threshold) * showroom K i=0)]; exact .zero
   funext m v; change (glorified F i _ _ • (1:FC (Single (K.c m))))*_=0; unfold glorified; simp only [h,Pi.zero_apply]; simp -- tune indent
 have he:= Tune_p H p' i h; refine InTest.mul (InTest.seed (qCost w H P i)) (?_: InTest K true _ false (showroom K i)) -- wrong
 rcases i with _|⟨b,i,j⟩; · exact .one
 obtain ⟨c,f,u⟩:=he; have hx(i:mort x d): nodeC i.1.val∈cartO x (d+4):=cart_M ((ridge_spec _).1 i.1.property) (by omega)
 cases b
 · exact InTest.mul (InTest.remover _ (fun t=>Bool.noConfusion (c.mpr t)) (hx i)) (InTest.creator _ (f.mp rfl) (hx j))
 exact InTest.mul (InTest.creator _ (c.mp rfl) (hx i)) (InTest.remover _ (fun t=>Bool.noConfusion (f.mpr t)) (hx j))
lemma cased (F:Psu x d)(K:Calibration)(i:jungle x d)(m:Side)(V:Fields (K.c m))(q:ℝ) : ‖(scalar K (glorified F i q)* showroom K i) m V‖ ≤ ‖glorified F i q (onC (K.c m) V.1,onC (K.c m) V.2)‖:=by
 rw [Pi.mul_apply,Pi.mul_apply,show_t]; apply (norm_mul_le ..).trans; unfold scalar; rw [norm_smul,norm_one,mul_one,norm_smul, feeV_n, one_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (dotter _)
lemma payable_k (w:d+6<n.val)(H:Paper n)(P:TrackD p (knotX x d n) h H t)(u:1≤ h)(K:Calibration): Afterglow.Tower.pay (John (Pvi n x d H) K p.threshold) t:=by
 obtain ⟨V,Q,E⟩:=P; let F:=Pvi n x d H
 intro T p'; unfold John; rw [Finset.sum_apply,Finset.sum_apply]; apply (norm_sum_le ..).trans; apply le_trans _ E; let S:= (univ:Finset (jungle x d)).image (hereV n); apply le_trans _ (sum_le_sum_of_subset_of_nonneg (subset_univ S) fun i _ _=>mul_nonneg (papW_v _) (Q i).1.1)
 unfold S; rw [sum_image ((hereI (x:=x) (d:=d) (by omega:d<n.val)).injOn)]; refine sum_le_sum fun i _=>(cased F K i T _ _).trans ((earnG w i (Q (hereV n i)).1 _).trans (le_mul_of_one_le_left (Q (hereV n i)).1.1 ?_)); cases hi:hereV n i with|none=>exact le_refl _|some a=> exact one_le_pow₀ u
-- orientation strong.Physical
lemma ShowSpin (s:Shape) (b:Bool) (F:Psu (Shape.motion s x) d)(G:Psu x d) (A:Pane n)(L:pR n G=Barber (Levier.ray b s) (pR n F)) (v:ℝ): let V:= Levier.ray b s; showTop G n v (flashA V A)= lotB b (Typer V) (launchZ V) (showTop F n v A):=by
 intro V; by_cases h: pingV (s.motion x) d v (onC n A); · have hp:= (ping_trans s b A).mp h; unfold showTop; rw [if_pos h,if_pos hp,L]; exact tilt_atom .. -- tune
 have hp:= mt ((ping_trans s b A).mpr) h; unfold showTop; rw [if_neg h,if_neg hp,map_zero]
end ArtCart
end MastTin
end YM.CF.XGarden
end
