import YM.CF.Rill.Pyu
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
set_option synthInstance.maxSize 18000
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Atala
variable {n:Side}{α: Type}[MeasurableSpace α]
lemma fold_v (x:Site c)(p q:Forest S.ratio)(F G':Config G f)(h:∀ v:Site f,S.ratio.parent v=x → p.up v=q.up v)(v:∀ i:Bond f,i∈p.trunks→S.ratio.parent i.1=x→ F i=G' i)(i:Site f)(g:S.ratio.parent i=x): p.foldAt F i=q.foldAt G' i:=by
 induction i using Forest.hike.induct p with
 | case1 i z ih=>
    let Y:=p.up i; let k:=Y.used i; have hp:F k=G' k:=v _ ((p.trunk_mem_iff k).mpr ⟨i,z,rfl⟩) ((fee p z).trans g)
    have hx:(p.up i).read F i=(p.up i).read G' i:=by unfold Step.read; rw [hp] -- let k
    apply mul_right_cancel (b:=(p.up i).read G' i); -- tune binder
    calc p.foldAt F i *_ = p.foldAt F (i+(p.up i).vec):=by rw [←hx,p.fold_step _ z]
         _ = q.foldAt G' (i+(p.up i).vec):= ih ((p.stays i z).trans g)
         _ = _:=by rw [h i g, ←q.fold_step _ z]
 | case2 i h=> rw [show i=S.ratio.embed (S.ratio.parent i) from Classical.not_not.mp h,p.fold_root, q.fold_root]
open Cube Rush
variable {S:StepData (More c) (More f)} (K':Ratio c f) (p:S.ratio=ratio K')
local notation "R"=>S.ratio
lemma warmU (K:Forest S.ratio)(h:S.ratio=ratio K')(U:Pane f): let P:Forest (ratio K'):=h ▸ K; K.foldAt U=P.foldAt U:=by
 have hp:(∀ (X Y:Ratio (More c) (More f))(F:Forest X)(p:X=Y),let Y:Forest Y:=p ▸ F; F.foldAt U=Y.foldAt U):=by intro X Y F p; subst Y; rfl
 exact hp .. -- tune
include p
variable {E F:Support (More c)}
lemma seineR(A B: Forest S.ratio)(X Y:Pane f)(V W:Pane c)(d:ℝ)(i:Bond (More f))(h:S.ratio.parent i.1∈ E)(hl:halo 2 E ⊆ F)(hp:∀ i:Bond (More f),S.ratio.parent i.1∈ F→ X i=Y i)(hv:Agrees F V W)(g:∀ i,S.ratio.parent i∈F→ A.up i=B.up i):
 seine K' (p ▸ A) q d X V i = seine K' (p ▸ B) q d Y W i:=by
 let Z:=halo 2 E; let o:=S.ratio.parent i.1; have he:o∈F:=hl (halo_subset 2 E h) -- tune elabor
 have hw(x:Site (More f))(u:S.ratio.parent x∈F): A.foldAt X x=B.foldAt Y x:= fold_v (S:=S) (S.ratio.parent x) A B X Y (fun i p=> g i (p.symm ▸ u)) (fun i v p=>hp i (p.symm ▸ u)) _ rfl
 have hx:S.ratio.parent (i.1+step i.2)∈F:=hl (halo_spec.mpr ⟨_,h,(Work.E03.parent_step S i.1 i.2).trans (by decide)⟩)
 have hg:Precision.replica (ratio K') V i= Precision.replica (ratio K') W i:=by
    rw [←p]; unfold Precision.replica; split; rfl
    exact hv (o,i.2) he (hl (halo_spec.mpr ⟨_,h,(Work.E01.sep_step_le _ _).trans (by decide: 1 ≤ 2)⟩))
 unfold seine Lattice.gauge portU Lattice.gauge; simp only [←warmU K' A p X,←warmU K' B p Y,Pi.inv_apply,hw _ he,hw _ hx,hg,hp _ he]
omit p in
private lemma tinyW(P:Forest (ratio K'))(W:α→ Pane f)(Z:α→ Pane c)(q:Chi)(d:ℝ)(h:0<d)(t:2*d<firstRadius G)(v:Measurable W)(k:Measurable Z)(i:Bond (More f)): Measurable fun a=>seine K' P q d (W a) (Z a) i :=by
 let y(J:Bond (More f)):=J -- tune
 let F(x:α):=seine K' P q d (W x) (Z x) i; let Y(x:α):=Precision.replica (ratio K') (Z x) i; have hY:Measurable Y:=by unfold Y Precision.replica; split; exact measurable_const; exact (measurable_pi_apply _).comp k
 have he(a): Measurable (fun x=> P.foldAt (W x) a):= ((show Measurable (fun x:Pane f=>P.foldAt x a) from (P.folds _).measurable).comp v : Measurable ((fun U:Pane f=> P.foldAt U a)∘ W))
 let A(x:α):=Lattice.gauge (P.foldAt (W x)) (W x) i; have hp: Measurable A:= ((he i.1).mul ((measurable_pi_apply i).comp v)).mul (he _).inv
 let B(x:α):=knit q d (A x) (Y x); have hB:Measurable B:= ((SU.group.lieExp_cont.measurable.comp ((patched_continuous q h t).measurable.comp (hp.mul hY.inv))).mul hY)
 unfold seine Lattice.gauge; simp only [Pi.inv_apply]; exact (((he i.1).inv.mul hB).mul ((he _).inv.inv))
lemma spinW(A: Forest S.ratio)(X:α→ Pane f)(Y:α→ Pane c)(p':0<d)(ht:2*d< firstRadius G)(Y': Measurable Y)(hp:∀ i:Bond (More f),S.ratio.parent i.1∈ F→ Measurable fun y=>X y i)(i:Bond (More f))(w:S.ratio.parent i.1∈E)(hv:halo 2 E⊆ F): Measurable fun a=> seine K' (p ▸ A) q d (X a) (Y a) i:=by -- enough coarse meas Y all true since fill.V all meas global
 let W(a:α): Pane f:=fun j=> if S.ratio.parent j.1∈F then X a j else 1; have he: Measurable W:=measurable_pi_lambda _ fun i=>by unfold W; split; exact hp i ‹_›; exact measurable_const -- tune
 rw [show (fun a=>seine K' (p ▸ A) q d (X a) (Y a) i)=(fun a=>seine K' (p ▸ A) q d (W a) (Y a) i) from funext fun a=>seineR K' p A A _ _ _ _ _ i w hv (fun i p=>(if_pos p).symm) (fun _ _ _=>rfl) (fun _ _=>rfl)]
 exact tinyW K' (p ▸ A) W Y q d p' ht he Y' i
end YM.CF.Rill
