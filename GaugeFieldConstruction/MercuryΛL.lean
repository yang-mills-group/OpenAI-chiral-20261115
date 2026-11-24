import GaugeFieldConstruction.ArcBeforeΛL
/-!
 # Box determination can use local operator word products with arbitrary open U in real space.TIME. Every label & test lives on that box in use; *distributions*. Also arbitrary collar camps independently for each slot.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
open Complex
variable {n:ℕ}
variable {G:Gauge}{L:Register G}{S:Table L}{Y Z:Surface S}{D:∀ i,Blanket i}{F T:Waves S}{A:Y.Aurora D}{B:Z.Aurora D}
variable (e:A.FullBody F)(p:B.FullBody T)(V V':Fin n→ S.Union)(hA:Bid.cones Y)(hB:Bid.cones Z)
open Probe
lemma WrapUnitΛL (W:Set E4)(h:IsOpen W)(q:W.Nonempty): ∃ (f:Test4)(U:Set E4), HasCompactSupport ⇑f ∧ tsupport f⊆W ∧ IsOpen U ∧ U.Nonempty ∧ EqOn ⇑f 1 U :=by
 obtain ⟨x,u⟩:=q; obtain ⟨r,y,p⟩:= Metric.mem_nhds_iff.mp (h.mem_nhds u); let t:=r/3; have hp:0<t:=by dsimp [t]; positivity
 let J:=bud x t hp; let g:=tint J; have hx:tsupport ⇑g=Metric.closedBall x (t+t):= tint_support _
 refine ⟨g,Metric.ball x t,?_ ,?_,Metric.isOpen_ball,⟨x, Metric.mem_ball_self hp⟩,fun i p=>?_⟩
 · unfold HasCompactSupport; rw [hx]; exact isCompact_closedBall ..
 · rw[hx]; apply Set.Subset.trans _ p; apply Metric.closedBall_subset_ball; dsimp [t]; linarith
 unfold g; rw [tinted,J.one_of_mem_closedBall (Metric.ball_subset_closedBall p)]; simp
include e p hA hB
lemma ΨMinkΛL (W:Fin n→Set E4)(h:∀ i,IsOpen (W i))(q:∀ i,(W i).Nonempty)
    (t:∀ (f:Fin n→ Test4), (∀ i, tsupport (f i)⊆ W i ∧ HasCompactSupport ⇑(f i)) → Y.W n V (Joint.materialize n f)=Z.W n V' (Joint.materialize n f)): Y.W n V= Z.W n V':=by
 choose f U w z hU qU tU using fun i=> WrapUnitΛL (W i) (h i) (q i)
 let P := ⋂ i:Fin n,(fun x:Points n=> x i)⁻¹' U i
 have hp:P.Nonempty:=by choose x hx using qU; exact ⟨points x, mem_iInter.mpr fun i=> hx i⟩
 let J:=Joint.materialize n f; let X:= (Y.W n V-Z.W n V').comp (Probe.sew J); have hg: X=0:=by
    have he(g:Fin n→ Test4): sew J (Joint.materialize n g)=Joint.materialize n fun i=> sew (f i) (g i):=by
       ext1 x; simp only[sews,J,Joint.material_at,Finset.prod_mul_distrib]
    have ht: Submodule.span ℂ (range (Joint.materialize n)) ≤ (X.toLinearMap).ker:= by
       apply Submodule.span_le.mpr; rintro _ ⟨v,rfl⟩; change (Y.W n V-Z.W n V') (sew _ (Joint.materialize n _))=0; rw[he]
       have hq(i:Fin n):tsupport (sew (f i) (v i))⊆ tsupport (f i):= (shrinks ..).trans inter_subset_left
       exact sub_eq_zero.mpr (t _ (fun i=>⟨(hq i).trans (z i),(w i).of_isClosed_subset (isClosed_tsupport _) (hq i)⟩))
    ext1 i; exact Submodule.topologicalClosure_minimal _ ht X.isClosed_ker (Work.C25.answer n |>.symm ▸ (show i∈ (⊤:Submodule ℂ (Joint n)) from trivial))
 apply ΘDawnEarthΛL e p V V' hA hB P (isOpen_iInter_of_finite fun i=> (hU i).preimage (by fun_prop)) hp
 intro b hB _; have hyp:X b=0:=by rw[hg]; rfl
 have hy: sew J b=b:=by
    ext1 i; rw[sews]; by_cases e:i∈tsupport b
    · have he:J i=1:= by
         unfold J; rw [Joint.material_at]; exact Finset.prod_eq_one fun a _=> tU a (mem_iInter.mp (hB e) a)
      simp [he]
    rw [show b i=0 from image_eq_zero_of_notMem_tsupport e,mul_zero]
 change Y.W n V (sew J b)-Z.W n V' (sew J b)=0 at hyp; rw [hy] at hyp; exact sub_eq_zero.mp hyp
-- cov relations fixed local obs world.
variable (U:Set E4)(o:IsOpen U)(q:U.Nonempty)
abbrev ValueWordΛL (X:Surface S)(U:Set E4)(Y:Surface S):Prop:= ∀ b:Sentence S, (∀ s∈b, tsupport s.2 ⊆ U ∧ HasCompactSupport ⇑s.2)→ X.expect b= Y.expect b
include o q
lemma LocalDetermineΛL (h:ValueWordΛL Y U Z): Y=Z:=by
 apply WordsWillΛL; intro b; have he (n:ℕ)(x:Fin n→ S.Union): Y.W n x= Z.W n x:= ΨMinkΛL e p x x hA hB (fun _=>U) (fun _=>o) (fun _=>q) (fun f p=>by
    let v: Fin n→ Letter S:=fun i=>(x i,f i); have ht:= h (List.ofFn v) (fun _ p'=>by obtain ⟨j,rfl⟩:= List.mem_ofFn.mp p'; exact p j); rw [Work.C29.expectOfFn,Work.C29.expectOfFn] at ht; exact ht); change Y.W _ _ _=Z.W _ _ _; rw[he]
#print axioms LocalDetermineΛL
end YM.NSF.Boundary
end
