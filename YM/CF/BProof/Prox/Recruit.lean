import YM.CF.BProof.Prox.Show

/- Group finite supported entries by support after multiplying. no data-dependent
choice on output support. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prox.Show
open Function Filter Finset MeasureTheory Matrix
open scoped Topology BigOperators Classical
variable {A X E I J K L: Type*}[Fintype A][Fintype I][Fintype J][Fintype K][MeasurableSpace X]
variable {B:Base A}{O: Atmos A X}{F:B.Index I}{G:B.Index J}{H:B.Index K}{a p q:ℝ}
private lemma nodes {L: Type*}[Fintype L](t:L→Finset A): ∀ {W:L→ℝ}{i:Finset A}, (∑ p:L with t p=i,W p) ≠0 → ∃ p:L,t p=i∧W p≠0 :=by
 intro W i h; by_contra! u; apply h; exact sum_eq_zero fun p h=> u p (mem_filter.mp h).2
/-- Recruitment also for trace price & balls. -/
lemma recruit [NormedAddCommGroup E][MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E][Fintype L]
    (D:I→J→L→Finset A)(W:I→J→L→ℝ)(u:I→J→L→X→E)(Y:Board X I J E)
    (v:∀ i j k,Rent O (D i j k) (u i j k) (W i j k))
    (t:∀ i j k,W i j k ≠ 0 → B.C (D i j k) ∧ F.port i∈ D i j k ∧ G.port j∈ D i j k)
    (eq:∀ i j,(fun x => Y x i j)=∑ k:L,u i j k)
    (r:∀ i,∑ j,∑ k,Real.exp (a*(D i j k).card)*W i j k ≤ p)
    (r':∀ j,∑ i,∑ k,Real.exp (a*(D i j k).card)*W i j k ≤ p) : Show O F G Y a p:=by
 let l(x:Finset A)(i:I)(j:J) := univ.filter (fun k=> D i j k=x)
 let T(x:Finset A):Matrix I J ℝ:= Matrix.of fun i j=> ∑ k∈ l x i j,W i j k
 let S(x:Finset A): Matrix I J (X→ E):= Matrix.of fun i j=> ∑ k∈ l x i j,u i j k
 constructor; have ht(i:I)(j:J): (∑ x,Real.exp (a*x.card)*T x i j)=∑ k,Real.exp (a*(D i j k).card)*W i j k:=by
    unfold T l; simp only [Matrix.of_apply,Finset.mul_sum]; simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro k hk; simp [@eq_comm _ (D i j k)]
 refine ⟨T,S,fun i x y=>?_,fun x i j h=>?_,fun i j=>?_,?_,?_⟩
 · apply Rent.sum (l i x y); intro k h; exact (mem_filter.mp h).2 ▸ v x y k
 · obtain ⟨k,u,h⟩:= nodes (D i j) h; exact u ▸ (t i j k h)
 · rw [eq]; exact (sum_fiberwise _ (D i j) (u i j)).symm
 · simp_rw [ht]; exact r
 simp_rw [ht]; exact r'

variable  [NormedRing E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E] {Y:Board X I J E}{Z:Board X J K E}
private lemma costs {W:Page A I J ℝ}{U:Page A J K ℝ}(h:∀ i x y,0≤W i x y)(v:∀ i x y,0≤U i x y)
    (k:∀ i,∑ j,∑ S:Finset A,Real.exp (a*S.card)*W S i j≤ p)(k':∀ j,∑ l,∑ S:Finset A,Real.exp (a*S.card)*U S j l≤ q)
    (ha:0≤a)(hq:0≤q) (i:I) : ∑ l:K,∑ j:J× Finset A × Finset A, Real.exp (a*(j.2.1∪ j.2.2).card)*(W j.2.1 i j.1*U j.2.2 j.1 l) ≤ p*q:=by
 let s (S:Finset A):= Real.exp (a*S.card); have he(S T:Finset A): s (S∪T) ≤ s S*s T:=by unfold s; rw [← Real.exp_add,← mul_add,← Nat.cast_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_union_le ..)) ha)
 simp_rw [Fintype.sum_prod_type]; let t(j:J):=∑ S:Finset A,s S*W S i j; let v'(j:J)(l:K):=∑ S:Finset A,s S*U S j l
 apply le_trans (b:=∑ l:K,∑ j:J,t j*v' j l)
 · refine sum_le_sum (fun l _=> sum_le_sum fun j _=>?_); unfold t v'; rw [sum_mul]; apply sum_le_sum; intro S _; rw [mul_sum]; apply sum_le_sum; intro T _; exact (mul_le_mul_of_nonneg_right (he S T) (mul_nonneg (h ..) (v ..))).trans_eq (by ring)
 rw [sum_comm]; simp_rw [← mul_sum]; apply le_trans _ (mul_le_mul_of_nonneg_right (k i) hq); rw [sum_mul]; apply sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (k' j) (sum_nonneg fun _ _=> mul_nonneg (Real.exp_pos _).le (h ..))

lemma multiply (u:Show O F G Y a p)(v:Show O G H Z a q)(p':0≤p)(q':0≤q)(ha:0≤a): Show O F H (fun x=>Y x*Z x) a (p*q):=by
 obtain ⟨W,F',t,g,k,l,r⟩:=u.presents; obtain ⟨W',G',t',g',k',l',r'⟩:=v.presents
 let U(i:I)(x:K)(y:J×Finset A×Finset A):= W y.2.1 i y.1 * W' y.2.2 y.1 x; let A'(i:I)(x:K)(y:J×Finset A×Finset A) := F' y.2.1 i y.1 * G' y.2.2 y.1 x
 have he(i x y) : Rent O (y.2.1 ∪ y.2.2) (A' i x y) (U i x y):=((t ..).go subset_union_left).mul ((t' ..).go subset_union_right) -- y implicit tune
 apply recruit (fun (_:I) (_:K) (y:J× Finset A× Finset A)=> y.2.1 ∪ y.2.2) U A' (fun x=>Y x*Z x) he
 · intro i j y hh; obtain ⟨l,p,u⟩:=g _ _ _ (left_ne_zero_of_mul hh); obtain ⟨r,w,v⟩:= g' _ _ _ (right_ne_zero_of_mul hh); exact ⟨B.rel _ l r u w,mem_union_left _ p,mem_union_right _ v⟩ -- order
 · intro i j; simp_rw [Fintype.sum_prod_type]; ext1 x; rw [Matrix.mul_apply]; simp only [Finset.sum_apply]; apply sum_congr rfl; intro l hl; rw [show Y x i l= (∑ S,F' S i l) x from congrFun (k i l) x,show Z x l j=(∑ S,G' S l j) x from congrFun (k' l j) x]; simp_rw [Finset.sum_apply,sum_mul,mul_sum,A',Pi.mul_apply]
 · exact costs (fun i x y=>(t i x y).price) (fun i x y=>(t' i x y).price) l l' ha q'
 intro j
 have he:=costs (I:=K) (K:=I) (W:=fun i=> (W' i).transpose) (U:=fun i=> (W i).transpose) (fun i x y=>(t' ..).price) (fun i x y=>(t ..).price) r' r ha p' j; rw [mul_comm q] at he
 apply le_trans _ he; apply sum_le_sum; intro i _; simp only [Matrix.transpose_apply]; simp_rw [Fintype.sum_prod_type]; apply le_of_eq; apply sum_congr rfl; intro y h; rw [sum_comm]; unfold U; dsimp only; apply sum_congr rfl; intro S hS; apply sum_congr rfl; intro T hT; rw [union_comm,mul_comm (W _ _ _)]
end YM.CF.BProof.Prox.Show
