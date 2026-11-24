import YM.CF.Forge.Pear
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
structure Duo (G:Gauge)(S:StepData c f)(M N:Monk G S)(X:Support c) : Prop extends Beat M N X where -- syntax
 cost(i:Cell f)(p:¬Disjoint (startPos S i) X):i∈ M.key.costs↔i∈ N.key.costs
 aisles(i:Bond c)(p:¬Disjoint (pinPos i) X): i∈ M.key.aisles↔i∈ N.key.aisles
 flags(i:Site c)(p:i∈ X): i∈M.key.flags↔i∈N.key.flags
lemma aroundBk{o:Site c}(X:Support c)(p:Beat.shadows (o:=o) X r){y:Site c}(h:separation o y+v≤r):Beat.shadows (o:=y) X v:=by
 intro i u; obtain ⟨z,k,u⟩:=halo_spec.mp u; rw [mem_singleton.mp k] at u; exact p (halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle o y i).trans (by omega)⟩)
namespace Duo
local notation "G"=> SU.group
variable {M N:Monk G S}(K L:Stores S){T:Tube G S}{X:Support c}(h:Duo G S M N X)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hz:shovel S.patch+10≤ radiusB x){l j:ℕ}
local notation "U"=> M.sent x T q d l β
local notation "V"=> N.sent x T q d l β
include h hr hp
lemma foot_t(i:Cell f)(p:Beat.shadows (o:=S.ratio.parent i.1) X ((l+63)*radiusB x)): faceValue U i= faceValue V i:=by
 apply travel_local; intro k u _; have hn:=Work.E04.parent_separation S.ratio i.1 k.1; have hv : separation i.1 k.1 ≤ 2:= Work.E01.sep_touched _ _ (show k.1∈touched i from List.mem_toFinset.mpr u); exact h.toBeat.backF hr hp k (aroundBk X p (by simp_rw [Nat.add_mul]; omega)) -- h.backF? field
include hz
lemma shadow(i:Bond c)(p:Beat.shadows (o:=i.1) X ((l+65)*radiusB x)): Agrees (sideP S i) U V:=by
 intro e u _; have hp':=PhysicalNext.JointLoad.Psalm.home_reaches u; exact h.toBeat.backF hr hp e (aroundBk X p (by unfold shovel gun at hz; unfold PhysicalNext.JointLoad.Psalm.stride at hp'; simp_rw [Nat.add_mul]; omega))
lemma turnI(i:Bond c)(a:ℝ)(p:Beat.shadows (o:=i.1) X ((l+68)*radiusB x)): (Inure M.key x q M.k a i U=Inure N.key x q N.k a i V) ∧ litB M.key x M.k U i=litB N.key x N.k V i:=by
 let z₁:=pinPos i; have hk:S.patch.Branches S.kernel G:=hr.rules
 have ht(j)(e:j∈ pinPos i):separation i.1 j≤1:=price_pin i (mem_insert_self ..) e
 have he: ∀ u∈pinPos i,u∈X:=fun u e=>h.toBeat.sees p ((ht u e).trans (by simp_rw [Nat.add_mul]; omega))
 have hL:Agrees (sideP S i) U V:=h.shadow hr hp hz i (aroundBk X p (by rw [separation_self]; simp_rw [Nat.add_mul]; omega))
 have hq:S.connector U M.k.1 i=S.connector V N.k.1 i:=Push.GridApprox.connector_dep S hk i _ _ (h.fr i.1 (he _ (mem_insert_self ..))) (h.fr _ (he _ (mem_insert_of_mem (mem_singleton_self _)))) (fun i p l=> hL i (Or.inl p) (Or.inl l)) (fun i p l=>hL i (Or.inr p) (Or.inr l)) -- tune
 have hu:=h.fe i (fun _=>he _); have hh:S.prediction U M.k i=S.prediction V N.k i:=by unfold StepData.prediction; rw [hu,hq]
 have hS:onS M.key x i ↔ onS N.key x i:= ⟨fun l k e=> h.toBeat.same p (l e) (by have hh:=ht k e; simp_rw [Nat.add_mul]; omega),fun l k e=> h.toBeat.sym.same p (l e) (by have hh:=ht k e; simp_rw [Nat.add_mul]; omega)⟩
 unfold litB Inure bond; rw [hu,hq,hS,hh]; split_ifs with g
 · exact ⟨rfl,rfl⟩
 unfold abortP; rw [hh]; refine ⟨?_,rfl⟩; apply congrArg (· • (SU.group.mat (S.prediction V N.k i))); unfold shutters; apply prod_congr rfl; intro j e; unfold Pressure.toll; rw [h.foot_t hr hp j (aroundBk X p ?_)]
 have h:=beam_up S i i.1 (mem_insert_self ..) j e _ (mem_image_of_mem _ (Work.E01.base_touched j)); simp_rw [Nat.add_mul]; omega
lemma frameR(i:Site c)(p:Beat.shadows (o:=i) X ((l+68)*radiusB x)):litF M.key x M.k U i=litF N.key x N.k V i:=by
 have hs:onF M.key x i ↔ onF N.key x i:=⟨fun u=> h.toBeat.same p (show i∈ M.key.dome _ from u) (by simp_rw [Nat.add_mul,separation_self]; omega),fun u=>h.toBeat.sym.same p (show i∈N.key.dome _ from u) (by simp_rw [Nat.add_mul,separation_self]; omega)⟩
 unfold litF; rw [hs]; split; next v=>
    let j:Bond c:=(i,0); have hL: Agrees (sideP S j) U V:=h.shadow hr hp hz j (aroundBk X p (by change separation i i+_≤_; simp_rw [separation_self,Nat.add_mul]; omega)); unfold AnalyticBridge.Annulus1AD.frame; rw [h.fr i (h.toBeat.sees p (by simp))]; exact (Push.GridApprox.site_dep S hr.rules i (fun i t v=>hL i (Or.inl t) (Or.inl v)) _).2
 rfl
lemma ebb_p(i:Bond c)(p:Beat.shadows (o:=i.1) X ((l+68)*radiusB x))(a:ℝ): tidal M.key x w a q U M.V M.k i=tidal N.key x w a q V N.V N.k i:=by
 have he:i.1∈ X:=h.toBeat.sees p (by simp); unfold tidal; simp only [h.aisles i (fun l=> disjoint_left.mp l (mem_insert_self ..) he), (h.turnI hr hp hz i a p).1,h.view i he (h.toBeat.sees p ((Work.E01.sep_step_le ..).trans (by simp_rw [Nat.add_mul]; omega)))] -- tune
omit hz in
lemma biri(i:Cell f)(p:Beat.shadows (o:=S.ratio.parent i.1) X ((l+63)*radiusB x)): tokenF M.key q x U i=tokenF N.key q x V i:=by
 let y:= S.ratio.parent i.1; have he:=h.cost i (fun k=> disjoint_left.mp k (mem_image_of_mem _ (Work.E01.base_touched i)) (h.toBeat.sees p (by simp))); unfold tokenF AnalyticBridge.Annulus1AD.profile Pressure.toll; simp only [h.foot_t hr hp i p,he]
end Duo
end YM.CF.Forge
