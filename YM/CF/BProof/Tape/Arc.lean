import YM.CF.BProof.Hearth.Tour
import YM.CF.BProof.Wick.Chain
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
/-! Arc data and prices. `true` first leg, `true` derivative. Store compact paths
with [-1,2] (plus collar) to permit any endpoint in HasDerivAt; comparison costs read
only [0,1]. (sup for variation on these arcs; cheaper than all arguments). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth -- tune
attribute [local instance] opCStarAlgebra
abbrev Beam:= ↥(Set.Icc (-1:ℝ) 2)
def visit (x:ℝ): Beam:=⟨max (-1) (min x 2),le_max_left ..,max_le (by norm_num) (min_le_right ..)⟩
@[fun_prop] lemma visit_cont:Continuous visit:= Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
@[simp] lemma visit_self {x:ℝ}(h:x∈Set.Icc (-1:ℝ) 2) : (visit x).val=x:=by simp [visit,h.2,h.1]
lemma walk_visit (x:Time): (visit x.val).val=x.val:=visit_self (Set.Icc_subset_Icc (by norm_num :(-1:ℝ)≤ 0) (by norm_num : (1:ℝ) ≤2) x.property)
abbrev Key := Bool×Bool
abbrev Thread := Key→ C(Beam, Stamp)
abbrev Throne (N:Side):= Site (More N)→Thread
def wage (x y: Thread)(i:Key):ℝ:= let M:= (⟨fun t:Time=>visit t.val,visit_cont.comp continuous_subtype_val⟩:C(Time,Beam)); ‖(x i).comp M-(y i).comp M‖
variable {N :Side}
def roam (b:Throne N)(k:Key)(x:ℝ): Quilt N:=fun i=> b i k (visit x)
def week (b:Throne N)(k:Key)(x:ℝ):= pair (roam b k x)
abbrev Beneath (T:Throne N)(a:ℝ):= ∀ i u (t:Time), ‖roam T u t.val i‖≤a
def sweepThread (g:Geometry N)(b:Throne N):Throne N:=fun i k=> ⟨fun x=> motion (g i) (b i k x), by unfold motion congrC; fun_prop⟩
lemma Beneath.moves {g:Geometry N}{b:Throne N}{a:ℝ}(p:Beneath b a): Beneath (sweepThread g b) a:=fun i u t=>(congr_norm ..).trans_le (p ..)
abbrev Skein (N:Side)(v:ℝ):=Subtype (fun t:Throne N=>Beneath t v)
namespace Skein
variable (k:Key)(j:Site (More N))(t:ℝ){a:ℝ}
def move (g:Geometry N)(b:Skein N a): Skein N a:=⟨sweepThread g b.val,b.property.moves⟩
def toll(j:Site (More N))(x y:Skein N a):=∑ i:Key,wage (x.val j) (y.val j) i
lemma toll_pos (x y:Skein N a) : 0 ≤ toll j x y:= sum_nonneg fun i _=> norm_nonneg _
lemma toll_le (x y:Skein N a)(u:Time) : ‖roam x.val k u.val j - roam y.val k u.val j‖ ≤ toll j x y:=by
 apply le_trans (b:=wage (x.val j) (y.val j) k) _ (single_le_sum (f:=fun i=>wage (x.val j) (y.val j) i) (fun i _=>norm_nonneg _) (mem_univ _)); let M:= (⟨fun t:Time=>visit t.val,visit_cont.comp continuous_subtype_val⟩:C(Time,Beam)); exact ContinuousMap.norm_coe_le_norm ((x.val j k).comp M - (y.val j k).comp M) u
lemma weekSpin (g:Geometry N)(x:Skein N a):week (move g x).val k t= congrC (tradew N g) (week x.val k t):= pair_spin g _ -- comp rfl
variable {D:Type}[TopologicalSpace D](b:Feet N D)
def hall (a:ℝ): Feet N (D×Skein N a):= b.double move toll (fun i x y=> toll_pos i x y)
def tune (b:Feet N D): Feet N (D×Time):= ⟨Ella b.st,b.town,b.index⟩
lemma Roam (k:Key) : Continuous (fun p:Skein N a × Time=>roam p.1.val k p.2.val) := by
 unfold roam; apply continuous_pi; intro i
 let L:=Skein N a; have hp:Continuous (fun x:L=> x.val i k):=((show Continuous (fun x:Thread=> x k) from continuous_apply k).comp (continuous_apply i (A:=fun i:Site (More N)=>Thread))).comp continuous_subtype_val; exact (hp.comp continuous_fst).eval (visit_cont.comp (continuous_subtype_val.comp continuous_snd)) -- tune
lemma earns {v:ℝ}(h:1≤v): ∃ p:Pay, ∀ {N:Side}{D:Type}[TopologicalSpace D](b:Feet N D)(k:Key), let H:= hall b v; Earn p (straw H.mark) (straw H.mark.reverseV) (fun x=>week x.1.2.val k x.2.val):=by
 obtain ⟨p,X⟩:= earnsTile v h; refine ⟨p,?_⟩; intro N D _ b k H; let W(x:(D× Skein N v)×Time) := roam x.1.2.val k x.2.val; apply X (tune H) (F:=W); · exact (Roam k).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
 · exact fun _ _=> rfl
 · exact fun i k=> i.1.2.property k .. -- tune
 rintro ⟨⟨x,y⟩,w⟩ ⟨⟨z,t⟩,r⟩ i; let o:=badgeOf i; change ‖roam _ k _ o - roam _ k _ o‖≤ v*((b.st.eval {o} x z+∑ q ∈ ({o}:Support (More N)),toll q y t)+ite (w=r) 0 2); rw [sum_singleton]; have hp:=b.st.pos {o} x z
 by_cases g:w=r; · subst r; rw [if_pos rfl,add_zero]; exact (toll_le k o y t w).trans ((le_add_of_nonneg_left hp).trans (le_mul_of_one_le_left (add_nonneg hp (toll_pos ..)) h))
 rw [if_neg g]; apply (norm_sub_le ..).trans; exact (add_le_add (y.property o k w) (t.property o k r)).trans (by nlinarith only [mul_nonneg (zero_le_one.trans h) (add_nonneg hp (toll_pos o y t))])
end Skein
end YM.CF.BProof.Tape
