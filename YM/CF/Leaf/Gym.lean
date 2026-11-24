import YM.CF.Cadre.Bezel
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology Lattice Finset Palot Cadre PowerSeries
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
abbrev αK (S T: Palot.leaf A):Palot.leaf A:=⟨S.val ∪ T.val,S.property.mono subset_union_left⟩
abbrev Ktw(G:Palot.leaf A→Palot.leaf A→ B)(S:Palot.leaf A):B:= ∑ X:Palot.leaf A,∑ Y∈Cadre.blaze X, if S=αK X Y then G X Y else 0
abbrev Kth(G:Palot.leaf A→Palot.leaf A→Palot.leaf A→ B)(S:Palot.leaf A):B:=∑ X:Palot.leaf A,∑ Y∈Cadre.blaze X,∑ Z∈Cadre.blaze X,if S=αK (αK X Y) Z then G X Y Z else 0
variable (o:A)(X Y: Palot.leaf A)(Q V F:Palot.leaf A→ℝ)
omit [Fintype A] in
lemma root_m(T X:Palot.leaf A): o∈ (αK T X).val↔o∈T.val∨o∈X.val:=mem_union
lemma blaze_p(X Y T: Palot.leaf A)(p:X∈Cadre.blaze Y):X∈Cadre.blaze (αK Y T):=by
 unfold blaze; apply mem_filter.mpr; exact ⟨mem_univ _,fun h=>(mem_filter.mp p).2 (Disjoint.mono_left subset_union_left h)⟩ -- tune orientation
lemma ask_R(Y: Palot.leaf A)(v:ℝ) : nook ((fun X:Palot.leaf A=>if X=Y then v else 0)*F) o=(if o∈Y.val then v*F Y else 0):=by
 by_cases p:Y∈spark o; · unfold nook; rw [sum_eq_single_of_mem Y p]; rw [Pi.mul_apply,if_pos rfl,if_pos ((mem_filter.mp p).2)]; intro i t g; rw [Pi.mul_apply,if_neg g,zero_mul]
 rw [if_neg (show o∉Y.val from fun h=>p (mem_filter.mpr ⟨mem_univ _,h⟩))]; refine sum_eq_zero fun i v'=>?_ ; rw [Pi.mul_apply,if_neg (fun (h:i=Y)=> p (h ▸ v')),zero_mul]
lemma core_X (G:Palot.leaf A→ℝ) (i:Palot.leaf A): (∑ j∈Cadre.blaze i, if o∈j.val then G j else 0)=∑ j∈Cadre.spark o ∩ Cadre.blaze i,G j:=by rw [←sum_filter]; congr 1; ext x; simp [Cadre.blaze,Cadre.spark]; tauto
variable (q:0 ≤ Q)(v:0≤V)(h:0≤F)(u:∀ X Y:Palot.leaf A, Y∈ Cadre.blaze X→ F (αK X Y) ≤ F X * F Y)
variable {a b c d:ℝ} (p:∀ i:A,nook (V*F) i ≤ a) (f:∀ i:A,nook (Q*F) i ≤ b)(w:∀ i:A,shelfR (Q*F) i ≤ c)
include h q v u p
lemma bud_V : nook (Ktw (fun X Y=>Q X * V Y) * F) o ≤ shelfR (Q*F) o*a + ∑ Y∈spark o, ((V*F) Y)* ∑ Z∈Cadre.blaze Y,((Q*F) Z):=by
 let W:= V*F; let N:=Q*F; have hv: 0 ≤ W:=fun i=>mul_nonneg (v i) (h i); have hx:0 ≤ N:=fun i=>mul_nonneg (q i) (h i)
 unfold Ktw nook; simp_rw [Pi.mul_apply,sum_mul]; rw [←canal, sum_comm]; conv_rhs=> lhs; unfold spark; rw [sum_filter]
 rw [←sum_add_distrib]; apply sum_le_sum; intro i _
 rw [sum_comm]
 have hu:=beam i W hv a (fun i _=>p i); let X:=blaze i
 let g(Y j:Palot.leaf A):= (if Y=αK i j then Q i*V j else 0)*F Y; change (∑ j∈ X, ∑ Y∈spark o,g Y j) ≤ (if o∈i.val then N i*i.val.card*a else 0)+ N i*(∑ Y∈Cadre.spark o∩ Cadre.blaze i,W Y)
 -- tune use ∑
 have hb(j:Palot.leaf A)(p:j∈X) : Q i*V j*F (αK i j) ≤ N i * W j:= by apply (mul_le_mul_of_nonneg_left (u i j p) (mul_nonneg (q i) (v j))).trans_eq; change _= Q i*F i*(V j*F j); ring
 by_cases s:o∈i.val
 · rw [if_pos s]; apply le_trans _ (le_add_of_nonneg_right (mul_nonneg (hx i) (sum_nonneg (fun i _=> hv i))))
   rw [mul_assoc]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hu (hx i)); rw [mul_sum]; refine sum_le_sum fun j t=>?_ ; rw [show (∑ x∈spark o,g x j)=_ from ask_R o F _ _, if_pos ((root_m o _ _).mpr (.inl s))]; exact hb j t
 rw [if_neg s,zero_add,←core_X, mul_sum]; apply sum_le_sum; intro j t; rw [show (∑ x∈spark o,g x j)=_ from ask_R o F _ _]; by_cases v:o∈j.val; · rw [if_pos v, if_pos ((root_m o _ _).mpr (.inr v))]; exact hb j t
 rw [if_neg v, if_neg (fun h=>v (((root_m o _ _).mp h).resolve_left s)),mul_zero]
-- quadratic legacy.Y can attach both. weighted bound.
omit q v h u p
abbrev HiΦ(Y:Palot.leaf A):ℝ:= ((Q*F) Y)* (Y.val.card:ℝ)
abbrev Hiκ (o:A) :ℝ:= ∑ i∈spark o, (HiΦ Q F i)*(i.val.card:ℝ)
variable (hb:0≤a)
include h q v u p hb
lemma trio_X : nook (Kth (fun X Y Z=>Q X * V Y * V Z)* F) o ≤ Hiκ Q F o * a *a + 2 * a *∑ Y∈spark o, (V*F) Y * ∑ Z∈ Cadre.blaze Y,HiΦ Q F Z:=by
 let W:= V*F; let N:=Q*F; have hv: 0 ≤ W:=fun i=>mul_nonneg (v i) (h i); have hx:0 ≤ N:=fun i=>mul_nonneg (q i) (h i)
 unfold Kth nook Hiκ; simp_rw [Pi.mul_apply,sum_mul]; rw [sum_comm,←canal _ _ o,mul_sum]; conv_rhs=> lhs; unfold spark; rw [sum_filter]
 rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [sum_comm]; simp_rw [sum_comm (s:=spark o)] -- innermost
 let X:= Cadre.blaze i; let g(j r l: Palot.leaf A):= (if l=αK (αK i j) r then Q i*V j*V r else 0)*F l; have hl(j r:Palot.leaf A)(v':j∈ X)(b:r∈ X): Q i*V j*V r* F (αK (αK i j) r) ≤ N i*W j*W r:=by
    have he:0 ≤ V r:=v r; refine (mul_le_mul_of_nonneg_left ((u _ _ (blaze_p _ _ _ b)).trans (mul_le_mul_of_nonneg_right (u _ _ v') (h _))) (mul_nonneg (mul_nonneg (q _) (v _)) he)).trans_eq ?_; change _= Q i*F i*(V j*F j)*(V r*F r); ring
 let l:ℝ:=i.val.card; have ht:=beam i W hv a (fun i _=>p _); let H:=Cadre.spark o∩ X
 change (∑ j∈ X,∑ r∈ X,∑ z∈spark o,g j r z) ≤ (if o∈ i.val then N i*l*l*a*a else 0) + 2*a * (N i*l* (∑ X∈ H,W X))
 let f(j r:Palot.leaf A):= N i*W j*W r
 have he(Y T:Finset (Palot.leaf A)): (∑ j∈Y, ∑ r∈T,f j r)= N i*(∑ j∈Y,W j)*(∑ r∈T,W r):=by unfold f; simp_rw [mul_sum, sum_mul]; rw [sum_comm]
 have hp:0≤ ∑ X∈ H,W X:=sum_nonneg fun i _=> hv i; have hu:0≤ l:=by unfold l; positivity
 by_cases s:o∈i.val
 · rw [if_pos s]; apply le_trans _ (le_add_of_nonneg_right (show 0 ≤ 2*a* (N i*l* (∑ X∈ H,W X)) from mul_nonneg (mul_nonneg (by norm_num) hb) (mul_nonneg (mul_nonneg (hx i) hu) hp))); apply le_trans (b:=∑ j∈X, ∑ k∈X,f j k)
   · apply sum_le_sum; intro j h'; apply sum_le_sum; intro k k'; rw [show (∑ x∈spark o,g j k x)=_ from ask_R o F (αK (αK i j) k) (Q i*V j*V k),if_pos ((root_m o (αK i j) k).mpr (.inl ((root_m o i j).mpr (.inl s))))]; exact hl j k h' k'
   rw [he]; exact (mul_le_mul (mul_le_mul_of_nonneg_left ht (hx i)) ht (sum_nonneg fun i _=> hv i) (mul_nonneg (hx i) (mul_nonneg hu hb))).trans_eq (by unfold l; ring)
 rw [if_neg s,zero_add]
 let FF(j k:Palot.leaf A):= (if j∈H then f j k else 0)+(if k∈H then f j k else 0)
 have hw:(∑ j∈X,∑ k∈X,FF j k)=(∑ j∈H,∑ k∈X,f j k)+(∑ j∈X,∑ k∈H,f j k):=by
    have he:X.filter (·∈H)=H:=by ext i; unfold H; rw [mem_filter,mem_inter,and_iff_right_of_imp]; exact fun h=> h.2
    unfold FF; simp_rw [sum_add_distrib]; congr 1; rw [sum_comm,sum_comm (s:=H) (t:=X)]; simp_rw [←sum_filter,he]; simp_rw [←sum_filter,he]
 apply le_trans (b:=∑ j∈X,∑ k∈X,FF j k)
 · apply sum_le_sum; intro j t; apply sum_le_sum; intro k v; rw [show (∑ x∈spark o,g j k x)=_ from ask_R o F (αK (αK i j) k) (Q i*V j*V k)]; split_ifs with c; swap; · unfold FF; have h': 0 ≤ f j k:=mul_nonneg (mul_nonneg (hx i) (hv j)) (hv k); split_ifs <;> positivity
   have h':0 ≤ f j k:=mul_nonneg (mul_nonneg (hx i) (hv j)) (hv k); refine (hl j k t v).trans ?_; unfold FF; obtain he|he:=(root_m o _ _).mp c; · rw [if_pos (show j∈H from mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,((root_m o _ _).mp he).resolve_left s⟩,t⟩)]; apply le_add_of_nonneg_right; split; exact h'; exact le_rfl
   rw [if_pos (show k∈H from mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,v⟩)]; apply le_add_of_nonneg_left; split; exact h'; exact le_rfl
 rw [hw,he,he]; exact (add_le_add (mul_le_mul_of_nonneg_left ht (mul_nonneg (hx i) hp)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (hx i)) hp)).trans_eq (by unfold l; ring)
end YM.CF.Leaf
