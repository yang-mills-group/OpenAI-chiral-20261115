import YM.CF.BPress.Spark.Sharp
import YM.CF.BPress.Spark.Mint
/-! actual Story choice. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger MeasureTheory SU Pastry Tulip Skye Girt Scree Cube Lat Fock Vesper Spin Spin.Paint Pine Lily -- tune names
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff Real ENNReal Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}[TopologicalSpace D](P:Form N D)(B:ℕ)
abbrev SX := Form.stage P
abbrev storyJ(i:WantJ N): Support (More N):= {node i.fst}
abbrev storyE(i: LocB N) := dorm B (earth i)
abbrev storyP(i:Force N):=dorm B (harbor i)
abbrev storyR {N:Side}: WantR N→Support (More N):= Sum.elim (fun i=>storyE B i.fst) (fun i=>storyP B i.fst)
def story {N: Side}: Heat N→ Support (More N):= Sum.elim storyJ (storyR B)
lemma story_focus (a b:Heat N)(r:(LensStory N).rule a b): ¬Disjoint (story B a) (story B b):=by
 rcases a with (a|(a|a))<;> rcases b with (b|(b|b)); all_goals first| (change False at r; exact r.elim) | skip
 · have he: a.1 = b.1:= Or.resolve_right (show a.1=b.1 ∨ False from r) id; intro t; exact disjoint_left.mp t (mem_singleton_self _) (mem_singleton.mpr (congrArg (Cube.node (N:=N)) he)) -- tune mem
 have h:¬Disjoint (harbor a.fst) (harbor b.fst):=by rcases (show a.1=b.1 ∨ OreS a.1 b.1 from r) with v|v; rw [v]; exact not_disjoint_iff.mpr ⟨_,b.fst.val.1.property,b.fst.val.1.property⟩; exact v
 exact fun x=> h (Disjoint.mono (dorm_sub ..) (dorm_sub ..) x)
lemma stem_paid (a:Heat N)(k: TripC (Single N))(p:k∈ (LensStory N).band a): Spin.home N (throat k)∈story B a:=by
 rcases a with (a|(a|a))
 · obtain ⟨u,v,rfl⟩:= List.mem_map.mp (show k∈ (jBand a).map leftS from p); have he:u∈a.2.val.val:=by simpa [jBand,Course.string] using v
   have h:= mem_powerset.mp a.2.val.property he; exact mem_singleton.mpr (congrArg node (show u.1.1=a.1 from (mem_filter.mp h).2)) -- tune typechecking k replaced
 · obtain ⟨u,v,rfl⟩:= List.mem_map.mp (show k∈ (DoughBag.letter a.2.val).map rightS from p); have he:u∈a.2.val:= (mem_sort _).mp v; have hb:u∈ redP a.1:=mem_powerset.mp ((mem_filter.mp (show _ ∈ Wheat _ from (DoughBag.nook a.2).property)).1) he; exact dorm_sub B _ (mem_filter.mp hb|>.2) -- tune mem_sort
 obtain ⟨u,v,rfl⟩:= List.mem_map.mp (show k∈ (DoughBag.letter a.2.val).map rightS from p); have he:u∈a.2.val:= (mem_sort _).mp v; have hb:u∈furnaceP a.1:=mem_powerset.mp ((mem_filter.mp (show _∈ Wheat _ from a.2.property)).1) he; exact dorm_sub B _ (mem_filter.mp hb|>.2)
lemma st_land (a:Heat N): Grove (field 4 (More N)) (story B a):= by rcases a with (a|(a|a)); exact .single _; exact dorm_hit _ _ ⟨_,post0_ok ..⟩; exact dorm_hit _ _ ⟨_,post1_ok ..⟩ -- tune
lemma st_f : (SX P).F= field 4 (More N):= rfl
-- if defeq
abbrev TheoryP:= crownP (Form.stage P)
def Saga : Story (Heat N) (TheoryP P):= {
 base:=story B
 word:=(LensStory N).band
 rule:=(LensStory N).rule
 landed:=fun i=> st_land B i
 paid:= fun i k h=> stem_paid B i k h
 focus:=story_focus B
 e:=(LensStory N).e
 n:=(LensStory N).n }
lemma born_st : Born (Saga P B):= ⟨rfl,rfl⟩
end YM.CF.BPress.Spark
