import YM.CF.DPress.Chess.Flow.Bough
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Transit.Bough
open Function Filter Lattice RG Precision Tree Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Cube
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
variable {n m:Side} (G:Ratio n m)
variable {X Y:Support n}{F T:Forest G}
abbrev annual [Nonempty (Forest G)]: FD.Vision n 0 (Forest G) where
 c:=cashT G
 set:=Counts G
 dim:=fun X Y h=> pair_t G X (Finset.disjoint_left.mpr (fun x a b=>by simpa using h x a x b))
 le X Y t i j v :=(holds ..).2 fun k h=> (holds ..|>.1 v) _ (t h)
lemma cor_V {x:Site m}(p:(Counts G X).r F T)(h:x∈twig G X):F.hike x=T.hike x:=by
 induction x using Forest.hike.induct F with
 | case1 i k ih=>
    have ht : F.up i=T.up i:=congrArg Prod.fst ((holds ..|>.1 p) _ ((twig_v ..).1 h)); rw [Forest.hike, Forest.hike.eq_1 T i,dif_pos k,dif_pos k,←ht]; congr 1; exact ih ((twig_v ..).2 (F.stays i k|>.symm ▸ ((twig_v ..).1 h))) -- tune
 | case2 i t=> rw [Forest.hike,Forest.hike.eq_1 T i,dif_neg t,dif_neg t]
lemma hikeP (F:Forest G)(i:Site m)(t:i∈twig G X)(z:Site m)(p:z∈visits i (F.hike i)) : z∈twig G X:=by
 induction i using Forest.hike.induct F with
 | case1 i k ih=>
    rw [Forest.hike,dif_pos k] at p; cases List.mem_cons.mp p with|inl h=> exact h.symm ▸ t|inr h=> exact ih ((twig_v G X).2 ((F.stays i k).symm ▸ (twig_v G X).1 t)) h
 | case2 i l=> rw [Forest.hike,dif_neg l, visits,List.mem_singleton] at p; exact p.symm ▸ t
lemma fold_v {K:Gauge}{V U:Config K m}(u: Agrees (twig G X) V U)(p:(Counts G X).r F T){i:Site m}(h:i∈twig G X): F.foldAt V i=T.foldAt U i:=by rw [Forest.foldAt,Forest.foldAt,cor_V G p h]; exact congrArg _ (travel_local _ _ _ _ (fun e p v=> u e (hikeP G T i h _ p) (hikeP G T i h _ v)))
lemma costume{K:Gauge}(p:Odd G.count.val){V U:Config K n}(h:Agrees X V U):Agrees (twig G X) (Precision.replica G V) (Precision.replica G U):=by
 intro e i j; have hu:=G.parents_hop p e.1 e.2; unfold Precision.replica; split; rfl; next v=> split at hu; exact h _ ((twig_v ..).1 i) (hu ▸ ((twig_v ..|>.1 j))); exact False.elim (v hu)
section
variable {G': Ratio n m} (q: Push.SectorMeasure.Chi)(u:ℝ)
open Rush Lat Tulip Peaks Skye
lemma seine_t {S:Support (More n)}{F T:Forest (ratio G')}(p:Odd G'.count.val){V U:Pane n}{U' V': Pane m}(h:Agrees S V U)(v:Agrees (twig (ratio G') S) V' U')(t:(Counts (ratio G') S).r F T): Agrees (twig (ratio G') S) (seine G' F q u V' V) (seine G' T q u U' U):=by
 let R:=ratio G'; have he:Set.EqOn (F.foldAt V') (T.foldAt U') (twig R S):= fun i h=>fold_v _ v t h; intro i x y; have hv:= costume R p h i x y; have hu:Agrees (twig R S) (Lattice.gauge (F.foldAt V') V') (Lattice.gauge (T.foldAt U') U'):= Skye.tied (twig R S) V' U' (F.foldAt V') (T.foldAt U') v he; have hp: portU G' F q u V' V i= portU G' T q u U' U i:= congrArg₂ (knit q u) (hu i x y) hv
 unfold seine Lattice.gauge; simp only [Pi.inv_apply, he x,he y]; exact congrArg (fun v=>_*v*_) hp
end
end YM.CF.DPress.Chess.Transit.Bough
