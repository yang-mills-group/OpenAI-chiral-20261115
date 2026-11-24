import YM.CF.Petal.Merc
set_option linter.unusedSectionVars false

/-! Connected and supported envelope calculus on even commutative sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Filter Branch Finset NormedSpace
structure Bell (Y E : Type*) [NormedRing E] [NormedAlgebra ℝ E] where
  store : Seal Y → Subalgebra ℝ E
  stair {S T} : S⊆T→ store S ≤ store T
  wallL S : IsClosed (store S : Set E)
  fare : E → ℝ
  free : fare 0=0
  single : fare 1=1
  normF x : ‖x‖≤fare x
  plus x y : fare (x+y)≤fare x+fare y
  times x y : fare (x*y) ≤ fare x * fare y
  scale x (c:ℝ) : fare (c • x)= ‖c‖*fare x
  sound : Continuous fare
structure Lodge (Y E D G : Type*) [NormedRing E] [NormedAlgebra ℝ E] extends Bell Y E where
  zone : Seal Y→ D→D→ Prop
  grows {S T x y} : S⊆T→ zone T x y→ zone S x y
  pick : G→D→D
  rule : G→ E →ₐ[ℝ] E
  ct g : Continuous (rule g)
variable {Y E D G : Type*} [DecidableEq Y] [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E] [TopologicalSpace D]
-- unnecessary normOneClass in inner structure? include
structure Token (L : Lodge Y E D G) (S : Seal Y) (f : D→E) (c : ℝ) (p : Seal Y→Prop) : Prop where
  price : 0≤c
  shape : c≠0 → p S
  gram x : f x ∈ L.store S
  locality {x y} : L.zone S x y → f x=f y
  owns x : L.fare (f x)≤ c
  ct : Continuous f
  dress g x : L.rule g (f x)=f (L.pick g x)
variable {L : Lodge Y E D G} {S T : Seal Y} {f g : D→E} {a b c w : ℝ} {p q r : Seal Y→Prop}
lemma Bell.starL {B : Bell Y E} (x : E) : 0 ≤ B.fare x := (norm_nonneg _).trans (B.normF x)
lemma Bell.pile {B : Bell Y E} {J : Type*} (A : Finset J) (F : J→E) : B.fare (∑ i∈A,F i) ≤ ∑ i∈A,B.fare (F i) := by
  classical
  induction A using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty,B.free]
  | insert i A h ih=> rw [sum_insert h,sum_insert h]; exact (B.plus ..).trans (add_le_add_right ih _) -- tune
lemma Bell.aceL {B : Bell Y E} (f : ℕ→E) (g : ℕ→ℝ) (h : ∀ i,B.fare (f i)≤g i) (e : Summable g) : B.fare (∑' i,f i)≤ ∑' i,g i := by
  have he := (e.of_norm_bounded (f:=f) (fun i=>(B.normF _).trans (h i))).hasSum
  exact le_of_tendsto_of_tendsto' (B.sound.continuousAt.tendsto.comp he) e.hasSum (fun i=>(pile ..).trans (sum_le_sum (fun i _=> h i)))
namespace Token
lemma payT (h : Token L S f w p) (c : ℝ) : Token L S (fun x=>c • f x) (‖c‖*w) p := by
  refine ⟨mul_nonneg (norm_nonneg _) h.price,fun e=>h.shape (right_ne_zero_of_mul e),fun x=>Subalgebra.smul_mem (L.store S) (h.gram x) _, fun e=> congrArg _ (h.locality e),fun x=> ?_,continuous_const.smul h.ct,fun g x=>by rw [map_smul, h.dress]⟩
  rw [L.scale]; exact mul_le_mul_of_nonneg_left (h.owns x) (norm_nonneg _)
lemma plusT (h : Token L S f a p) (e : Token L S g b p) : Token L S (fun x=>f x+g x) (a+b) p := by
  refine ⟨add_nonneg h.price e.price,fun k=>?_,fun x=>Subalgebra.add_mem _ (h.gram x) (e.gram x), fun p=>congrArg₂ _ (h.locality p) (e.locality p),fun x=>(L.plus ..).trans (add_le_add (h.owns x) (e.owns x)),h.ct.add e.ct,fun i x=>by rw [map_add,h.dress,e.dress]⟩
  by_cases l:a=0
  · apply e.shape; rwa [l,zero_add] at k
  exact h.shape l
lemma together (h : Token L S f a p) (e : Token L T g b q) (j : p S→q T→ r (S∪T)) : Token L (S∪T) (fun x=>f x*g x) (a*b) r :=
  ⟨mul_nonneg h.price e.price,fun k=>j (h.shape (left_ne_zero_of_mul k)) (e.shape (right_ne_zero_of_mul k)),fun x=>Subalgebra.mul_mem _ (L.stair subset_union_left (h.gram x)) (L.stair subset_union_right (e.gram x)),fun k=> congrArg₂ _ (h.locality (L.grows subset_union_left k)) (e.locality (L.grows subset_union_right k)),fun x=>(L.times ..).trans (mul_le_mul (h.owns x) (e.owns x) (Bell.starL _) h.price),h.ct.mul e.ct,fun i x=>by rw [map_mul,h.dress,e.dress]⟩
lemma nought : Token L S (fun _=>0) 0 p := ⟨le_rfl,by simp,by simp,fun _=>rfl,fun _=>L.free.le,continuous_const,fun _ _=>map_zero _⟩
lemma sole (h : p ∅) : Token L ∅ (fun _=>1) 1 p := ⟨zero_le_one,fun _=>h,by simp,fun _=>rfl,fun _=>L.single.le,continuous_const,fun _ _=>map_one _⟩
lemma shift {r₀ : Seal Y→Prop} (h : Token L S f a r) (p : r S→ r₀ S) : Token L S f a r₀ := { h with shape := p ∘ h.shape }
lemma mass {I : Type*} (s : Finset I) (F : I→D→E) (c : I→ℝ) (h : ∀ i∈s,Token L S (F i) (c i) r) : Token L S (fun x=>∑ i∈s,F i x) (∑ i∈s,c i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact nought
  | insert i s u ih=> simp only [sum_insert u]; exact (h i (mem_insert_self ..)).plusT (ih (fun j e=>h j (mem_insert_of_mem e)))
lemma storeT (F : ℕ→D→E) (c : ℕ→ℝ) (h : ∀ i, Token L S (F i) (c i) r) (e : Summable c) : Token L S (fun x=>∑' i, F i x) (∑' i,c i) r := by
  have he i x : ‖F i x‖≤ c i := (L.normF _).trans ((h i).owns _)
  have hl x : Summable (fun i=>F i x) := e.of_norm_bounded (fun i=>he i x)
  refine ⟨tsum_nonneg (fun i=>(h i).price),fun k=>?_,fun x=>?_, fun g=> tsum_congr (fun i=>(h i).locality g), fun x=>Bell.aceL _ _ (fun i=>(h i).owns x) e, continuous_tsum (fun i=>(h i).ct) e he,fun g x=>?_⟩
  · by_contra q; apply k; have hz i : c i=0 := by by_contra l; exact q ((h i).shape l)
    simp [hz]
  · exact (L.wallL S).mem_of_tendsto (hl x).hasSum (Eventually.of_forall (fun i=>Subalgebra.sum_mem (L.store S) (fun i _=>(h i).gram x))) -- tune
  let P : E →L[ℝ] E := ⟨(L.rule g).toLinearMap,L.ct g⟩
  change P (∑' i,F i x)=_; rw [P.map_tsum (hl x)]; exact tsum_congr (fun i=>(h i).dress ..)
end Token
variable [Fintype Y]
def Pool (L : Lodge Y E D G) (a w : ℝ) (p : Seal Y→Prop) (f : D→E) := ∃ (F : Seal Y→D→E) (K : Seal Y→ℝ), (∀ S, Token L S (F S) (K S) p) ∧ (∑ S,rent a S*K S)≤w ∧ ∀ x,f x=∑ S,F S x
lemma wallcash {c : Seal Y→ℝ} (L : ∀ S,0≤c S) (h : ∑ S,rent a S*c S≤w) : 0≤w := (sum_nonneg (fun S _=>mul_nonneg (rent_pos ..).le (L S))).trans h
namespace Pool
lemma free : Pool L a 0 r (fun _=>0) := ⟨_,_,fun _=>Token.nought,by simp,by simp⟩
lemma within (h : Token L S f w r) : Pool L a (rent a S*w) r f := by
  let F (T:Seal Y) (x:D) := if T=S then f x else 0; let K (T:Seal Y):= if T=S then w else 0
  refine ⟨F,K,?_,by simp [K,mul_ite],by simp [F]⟩; intro T; by_cases l:T=S; simpa only [F,K,l,if_true] using h -- tune eq_self
  simp only [F,K,if_neg l]; exact Token.nought
lemma oneF (h : r ∅) : Pool L a 1 r (fun _=>1) := by simpa only [rent,card_empty,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using within (L:=L) (a:=a) (Token.sole h)
lemma cents (h : Pool L a b r f) : 0≤b := by obtain ⟨F,K,p,q,v⟩:=h; exact wallcash (fun S=>(p S).price) q
lemma costUp (h : Pool L a b r f) (g : b≤c) : Pool L a c r f := by obtain ⟨F,K,p,q,v⟩:=h; exact ⟨F,K,p,q.trans g,v⟩
lemma shift (h : Pool L a b r f) (k : ∀ S,r S→ q S) : Pool L a b q f := by obtain ⟨F,K,p,g,v⟩:=h; exact ⟨F,K,fun S=>(p S).shift (k S),g,v⟩
lemma price (h : Pool L a b r f) (g : 0≤a) (x:D) : L.fare (f x)≤b := by
  obtain ⟨F,K,p,q,v⟩:=h; rw [v]
  exact (Bell.pile ..).trans ((sum_le_sum (fun S _=> ((p S).owns x).trans (le_mul_of_one_le_left (p S).price (rent_one g _)))).trans q)
lemma scaleW (h : Pool L a b r f) (d : ℝ) : Pool L a (‖d‖*b) r (fun x=>d • f x) := by
  obtain ⟨F,K,p,q,v⟩:=h; refine ⟨_,_,fun S=>(p S).payT d,?_,fun x=>by dsimp only; rw [v,smul_sum]⟩; simp_rw [mul_left_comm _ ‖d‖,←mul_sum]; exact mul_le_mul_of_nonneg_left q (norm_nonneg d)
lemma sumUp (h : Pool L a b r f) (k : Pool L a c r g) : Pool L a (b+c) r (fun x=>f x+g x) := by
  obtain ⟨F,K,p,q,v⟩:=h; obtain ⟨J,U,h,e,u⟩:=k
  refine ⟨_,_,fun S=>(p S).plusT (h S),?_,fun x=>?_⟩
  · simp_rw [mul_add,sum_add_distrib]; exact add_le_add q e
  dsimp only; rw [v,u]; rw [sum_add_distrib]
lemma batch {I : Type*} (s : Finset I) (F : I→D→E) (c : I→ℝ) (h : ∀ i∈s,Pool L a (c i) r (F i)) : Pool L a (∑ i∈s,c i) r (fun x=>∑ i∈s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact free
  | insert i s v ih=> simp only [sum_insert v]; exact (h _ (mem_insert_self ..)).sumUp (ih (fun i p=>h i (mem_insert_of_mem p)))
lemma combine (h : Pool L a b p f) (e : Pool L a c q g) (v : 0≤a) (u : ∀ S T, p S→ q T→ r (S∪T)) : Pool L a (b*c) r (fun x=>f x*g x) := by
  have hp:=h.cents
  obtain ⟨F,K,p₁,w,V⟩:=h; obtain ⟨J,U,h,E',R⟩:=e
  let W (i:Seal Y×Seal Y):= i.1∪i.2; let D i := rent a (W i)*(K i.1*U i.2)
  let A i (x) := F (Prod.fst (i:Seal Y×Seal Y)) x * J i.2 x
  have he i : Pool L a (D i) r (A i) := within ((p₁ i.1).together (h i.2) (u i.1 i.2))
  have H : ∑ i, D i≤b*c := by
    refine le_trans ?_ (mul_le_mul w E' (sum_nonneg (fun S _=> mul_nonneg (rent_pos ..).le (h S).price)) hp)
    rw [sum_mul,Fintype.sum_prod_type]; apply sum_le_sum; intro S _; rw [mul_sum]; apply sum_le_sum; intro T _
    apply (mul_le_mul_of_nonneg_right (rent_join S T v) (mul_nonneg (p₁ S).price (h T).price)).trans; exact le_of_eq (by ring)
  have hr x : f x*g x=∑ i,A i x := by rw [V,R,Fintype.sum_prod_type, sum_mul]; simp_rw [mul_sum]; rfl
  simp_rw [hr]; exact (batch univ _ _ (fun i _=>he i)).costUp H
lemma ts (F : ℕ→D→E) (K : ℕ→ℝ) (h : ∀ i, Pool L a (K i) r (F i)) (e : Summable K) (v : 0≤a) : Pool L a (∑' i,K i) r (fun x=>∑' i,F i x) := by
  choose M B p q u using h
  have ht S : Summable (fun i=>B i S) := e.of_nonneg_of_le (fun i=>(p i S).price) (fun i=>(le_mul_of_one_le_left (p i S).price (rent_one v S)).trans ((single_le_sum (f:=fun S=>rent a S*B i S) (fun S _=>mul_nonneg (rent_pos ..).le (p i S).price) (mem_univ S)).trans (q i)))
  refine ⟨_,_,fun S=>Token.storeT _ _ (fun i=>p i S) (ht S),?_,fun x=>?_⟩
  · have hg S : Summable (fun i=>rent a S*B i S):= (ht S).mul_left _
    simp_rw [←tsum_mul_left,←Summable.tsum_finsetSum (f:=fun S i=>rent a S*B i S) (hf:=fun S _=>hg S)]; exact (summable_sum (fun S (_:S∈(univ:Finset (Seal Y)))=>hg S)).tsum_le_tsum q e
  dsimp only; simp_rw [u]; exact Summable.tsum_finsetSum (f:=fun S i=> M i S x) (fun S _=>(ht S).of_norm_bounded (fun i=> (L.normF _).trans ((p i S).owns x))) -- tune
end Pool
end YM.CF.Petal
