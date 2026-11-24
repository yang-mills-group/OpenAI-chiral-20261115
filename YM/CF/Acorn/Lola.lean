import YM.CF.Acorn.Fir
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D E:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]
structure Cop (X:Master D Y)(Z:Master E Y)(f:E→D):Prop where
 frame :X.frame=Z.frame
 k:X.k=Z.k
 cont:Continuous f
 reads S x y: Z.moves S x y→ X.moves S (f x) (f y)
 draw:∀(A:Type)[NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A](V:Set A), IsOpen V→∀ q:A→E,Z.draw.test A V q→X.draw.test A V (f ∘ q)
variable {X:Master D Y} {Z:Master E Y}{f g:E→ D}{O:n→Y}{S R:Seal Y}{a K c r h:ℝ}{A:D→ ℂ}
lemma Pro.cop (p: Pro X S A c)(t: Cop X Z f):Pro Z S (A ∘ f) c:=by refine ⟨p.pos,fun y=> t.frame ▸ p.travel y,p.cont.comp t.cont,fun i=>p.sumline _,fun x y v=>p.reads _ _ (t.reads S x y v),fun E _ _ _ Q e k h x hx=>?_⟩; exact t.k ▸ p.plot _ _ e _ (t.draw E Q e k h) x hx
lemma Pro.minusP(p:Pro X S A c):Pro X S (-A) c:=by have h:=p.sc (-1); simp at h; exact h -- tune
-- covers indexed differences with local charge
lemma rep_only (h: Grove Z.frame R)(p:Cop X Z f)(q:Cop X Z g)(t:∀ S,Disjoint R S→∀ x,X.moves S (f x) (g x))(Q: Pro X S A c):Pro Z (S ∪ R) (A ∘ f-A ∘ g) (if Disjoint R S then 0 else 2*c):=by
 split_ifs with hx
 · rw [show A ∘ f-A ∘ g=(fun _=>0) from funext fun x=> sub_eq_zero.mpr (Q.reads _ _ (t S hx x))]; have he:=Pro.nonzero (X:=Z) (c:=0) (S ∪ R) (fun k=>False.elim (k rfl)); simpa using he
 have hi: Pro Z S (A ∘ f-A ∘ g) (2*c):=by rw [sub_eq_add_neg,two_mul]; exact (Q.cop p).sum (Q.cop q).minusP
 refine hi.larger subset_union_left (fun u=>?_) le_rfl id
 obtain ⟨y,w,v⟩:= Finset.not_disjoint_iff.mp hx; exact (hi.travel u).unite h v w
lemma meet_cost (p:0≤a)(R S:Seal Y):cost a R (S∪ R) ≤ rent a S:=by unfold cost Branch.rent; gcongr; intro i h; simp at h; tauto
lemma Cash.off (S:Seal Y)(v:S.Nonempty)(u:Grove Z.frame S)(p:Cop X Z f)(q:Cop X Z g)(t:∀ R,Disjoint S R→∀ x,X.moves R (f x) (g x))(M:Seal Y→ D→ℂ)(C:Seal Y→ℝ)(r:∀ i,Pro X i (M i) (C i))(a':0≤a)(H:∀ i:Y, hitE a C i≤ K) (s:∀ x:D,A x=∑ i,M i x) : Cash Z S a (fun x=>A (f x)- A (g x)) (S.card*(2*K)):=by
 simp_rw [s,← Finset.sum_sub_distrib]; apply tab (J:=Seal Y) (R:=S) -- tune
    (fun i x=> (M i) (f x)-(M i) (g x)) (fun i=> if Disjoint S i then 0 else 2*C i) (fun i=>i∪S) (fun i=> ⟨rep_only u p q t (r i),fun _=>subset_union_right⟩)
 calc
   _ ≤ ∑ R:Seal Y, ∑ i∈S, if i∈R then rent a R*(2*C R) else 0:= by
      apply sum_le_sum; intro R _; have hc(u:Y):0 ≤ if u∈R then Branch.rent a R*(2*C R) else 0:=by split; apply mul_nonneg (rent_pos ..).le (mul_nonneg (by norm_num) (r R).pos); rfl
      split
      · rw [mul_zero]; exact sum_nonneg fun i _=> hc i
      next hx =>
         obtain ⟨i,t,h⟩:= Finset.not_disjoint_iff.mp hx; apply le_trans _ (single_le_sum (fun i _=> hc i) t); rw [if_pos h]; exact mul_le_mul_of_nonneg_right (meet_cost a' _ _) (mul_nonneg (by norm_num) (r _).pos)
   _ ≤ _:=by
      rw [sum_comm]; refine le_trans (sum_le_sum (g:=fun _=>2*K) (fun i hi=>?_)) ?_; swap; simp
      apply le_trans _ (mul_le_mul_of_nonneg_left (H i) (by norm_num)); unfold hitE hit0; rw [Finset.sum_filter,Finset.mul_sum]; refine le_of_eq (Finset.sum_congr rfl fun R _=>?_); by_cases h:i ∈ R <;> simp [h] <;> ring
structure Plum (X:Master D Y)(O:n→Y)(L:D→Op (I n))(a K:ℝ):Prop where
 hit : ∃ (F:Seal Y→ D→Op (I n)) (C: Seal Y → Toll (I n)),(∀ (S:Seal Y)(i j:I n), Pro X S (fun v=>F S v i j) (C S i j) ∧ (C S i j≠0→ O i.2∈S ∧ O j.2∈S)) ∧ Ledger a C K ∧ (∀ i:Y,hitE a (fun S=>ledgerV (C S)) i ≤ K)∧ (∀ x,L x=∑ S:Seal Y,F S x) -- F type
variable {M:D→Op (I n)}
lemma peal (v:Grove Z.frame S)(p:Cop X Z f)(q:Cop X Z g)(t:∀ R,Disjoint S R→∀ x,X.moves R (f x) (g x))(u:Plum X O M a K)(a':0≤a): PairX Z O S a (fun x=> mix (M (f x)-M (g x))) (S.card*(2*K)):=by
 obtain ⟨F,C,h,W,Q,l⟩:=u.hit; let T:= Seal Y× I n × I n; let v'(s:T)(x:D):= F s.1 x s.2.1 s.2.2
 refine ⟨T,inferInstance, (fun s=> s.1 ∪ S),(fun s=> s.2.1),(fun s=>s.2.2), (fun s=>v' s ∘ f - v' s ∘ g),_,fun i=> ⟨rep_only v p q t (h _ _ _).1,?_⟩,?_,fun x=>?_⟩
 · intro z; split at z; contradiction
   obtain ⟨g,v⟩:= (h _ _ _).2 (right_ne_zero_of_mul z); exact ⟨subset_union_right,subset_union_left g,subset_union_left v⟩
 · rw [Fintype.sum_prod_type]; calc
    _ ≤ ∑ R:Seal Y, ∑ i∈S, if i∈R then 2*(rent a R*ledgerV (C R)) else 0:=by
       apply sum_le_sum; intro R _; have hx:0≤ledgerV (C R):=sum_nonneg fun i _=>sum_nonneg fun j _=>(h R i j).1.pos
       have he(u:Y):0≤ if u∈R then 2*(Branch.rent a R*ledgerV (C R)) else 0:=by split; apply mul_nonneg (by norm_num) (mul_nonneg (rent_pos ..).le hx); rfl
       rw [Fintype.sum_prod_type]
       dsimp only
       split_ifs with q
       · simp only [mul_zero, sum_const_zero]; exact sum_nonneg fun i _=>he i
       obtain ⟨i,hi,t⟩:=Finset.not_disjoint_iff.mp q
       refine le_trans ?_ (single_le_sum (fun i _=>he i) hi)
       rw [if_pos t]; simp_rw [mul_left_comm _ (2:ℝ) _,←mul_sum]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (meet_cost a' S R) hx) (by norm_num)
    _ ≤ _ :=by
       rw [sum_comm]; refine le_trans (sum_le_sum (g:=fun _=> 2*K) ?_) ?_; swap; simp
       intro i h; apply le_trans _ (mul_le_mul_of_nonneg_left (Q i) (by norm_num)); unfold hitE hit0; rw [sum_filter,mul_sum]; simp [mul_ite]
 dsimp only; rw [mix,l,l]
 simp only [Matrix.sub_apply,Matrix.sum_apply,←sum_sub_distrib,sum_smul]
 let D(i j:I n)(S:Seal Y):=(F S (f x) i j - F S (g x) i j) • (pen i*pen j)
 change ∑ i:I n,∑ j:I n,∑ S,D i j S=∑ j:T,D j.2.1 j.2.2 j.1
 rw [Fintype.sum_prod_type (f:=fun i:T=> D i.2.1 i.2.2 i.1)] -- tune
 change ∑ i:I n,∑ j:I n,∑ S,D i j S=∑ S,∑ i:I n×I n,D i.1 i.2 S
 have H(i:I n): (∑ j:I n,∑ S,D i j S)=∑ S,∑ j:I n,D i j S:= Finset.sum_comm
 simp_rw [H]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [Fintype.sum_prod_type (f:=fun j:I n × I n=> D j.1 j.2 i)]
end YM.CF.Acorn
