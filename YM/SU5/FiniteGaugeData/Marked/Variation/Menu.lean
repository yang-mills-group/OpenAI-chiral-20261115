import YM.SU5.FiniteGaugeData.Marked.Common
import YM.CF.Buffered.Discourse

/-!
# Optional stronger compactness. Menu calculus
`<finite list of Borel questions identifying X>` such that same list of answers
implies close function values -- simultaneously for possibly variable-sized outputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {X I J : Type*}[MeasurableSpace X]{T:I→Type*}{U:I→Type*}

abbrev Deck (X:Type*) := Finset (Set X)
namespace Deck
variable (P : Deck X)
def dark := ∀ i ∈ (P : Finset (Set X)), MeasurableSet i
def withZ (x y:X) := ∀ i ∈ (P : Finset (Set X)), x∈i ↔ y∈i
lemma join (Q : Deck X) (p:P.dark) (q:Q.dark): Deck.dark (show Deck X from ((P:Finset _)∪Q)):= fun i e=> (mem_union.1 e).elim (p i) (q i)
lemma grow {Q P:Deck X}(h:(P:Finset _)⊆Q)(x y:X)(p:Q.withZ x y):P.withZ x y:= fun i t=> p i (h t)
end Deck
section
variable [∀i,PseudoMetricSpace (T i)]
-- explicit finite

def Deal (f:(i:I) → X→ T i):Prop:=∀ ε:ℝ, 0<ε → ∃ P:Deck X, P.dark ∧ ∀ x y, P.withZ x y → ∀i, dist (f i x) (f i y)< ε
lemma deal_of_one {Y:Type*}[PseudoMetricSpace Y][MeasurableSpace Y][OpensMeasurableSpace Y]{f:X→Y}(h:Measurable f){A:Set Y}(p:IsCompact A)(z:∀x,f x ∈ A):Deal (I:=I) (T:=fun _=> Y) (fun _=> f):=by
 intro ε e
 obtain ⟨t,v,b,w⟩:= Metric.finite_approx_of_totallyBounded p.totallyBounded _ (show 0<ε/2 by linarith) -- type? search
 let B(y:Y):Set X:= f ⁻¹' ball y (ε/2)
 refine ⟨b.toFinset.image B, ?_,?_⟩
 · intro _ c; obtain ⟨a,u,rfl⟩:=mem_image.mp c; exact h isOpen_ball.measurableSet
 intro x y k _; have hw:=w (z x); simp only [Set.mem_iUnion] at hw; obtain ⟨a,v,q⟩:= hw
 have h': f y∈ ball a (ε/2):= (k _ (mem_image_of_mem B (b.mem_toFinset.mpr v))).mp (show f x∈ball _ _ from q)
 exact lt_of_le_of_lt (dist_triangle_right (f x) (f y) a) (by linarith [mem_ball.mp h',mem_ball.mp q])
namespace Deal
variable {f:(i:I)→X→T i}
protected lemma pure (f:∀ i,T i):Deal (X:=X) (fun i _=> f i):=by
 intro ε e; exact ⟨∅,fun _ h=>False.elim (Finset.notMem_empty _ h),fun x y _ i=>by simpa using e⟩ -- Deck not reducible EmptyCollection
protected lemma congr (h:Deal f){g:(i:I)→X→ T i}(q:∀i x,f i x=g i x):Deal g:=show _ from (funext fun i=>funext fun x=>q i x) ▸ h
protected lemma re {f:(i:I)→X→ T i}(h:Deal f)(a:J→I):Deal (T:=fun j=>T (a j)) (fun j x=>f (a j) x):=by
 intro ε e; obtain ⟨P,v,p⟩:=h ε e; exact ⟨P,v,fun x y z j=> p x y z (a j)⟩
protected lemma prod [∀i,PseudoMetricSpace (U i)] {g:(i:I)→X→U i}(h:Deal f)(t:Deal g):Deal (T:=fun i=> T i × U i) (fun i x=> (f i x,g i x)):=by
 intro ε e; obtain ⟨P,v,p⟩:=h ε e; obtain ⟨Q,u,q⟩:=t ε e
 refine ⟨(P:Finset _)∪ Q,P.join Q v u,fun x y z i=>?_⟩; rw [Prod.dist_eq]; exact max_lt (p _ _ (Deck.grow Finset.subset_union_left x y z) i) (q _ _ (Deck.grow Finset.subset_union_right x y z) i)
protected lemma cond {g:(i:I)→X→T i}(h:Deal f)(t:Deal g)(A:I→Prop):Deal (T:=T) (fun i=>if A i then f i else g i):=by
 intro ε e; obtain ⟨P,v,p⟩:=h ε e; obtain ⟨Q,u,q⟩:=t ε e
 refine ⟨(P:Finset _)∪Q,P.join Q v u,fun x y z i=>?_⟩; dsimp; split
 · exact p _ _ (Deck.grow Finset.subset_union_left x y z) i
 exact q _ _ (Deck.grow Finset.subset_union_right x y z) i
lemma assembly [Fintype J](g:J→ (i:I)→X→ T i)(h:∀j, Deal (g j))(a:I→J):Deal (T:=T) (fun i x=> g (a i) i x):=by
 intro ε e; choose P v p using fun j=> h j ε e
 let Q:Deck X:= univ.biUnion (fun j=>(P j:Finset _))
 refine ⟨Q,?_,?_⟩
 · intro i k; obtain ⟨j,u,g⟩:=mem_biUnion.1 k; exact v _ _ g
 intro x y t i; apply p (a i) x y _ i
 exact Deck.grow (fun _ v=> mem_biUnion.mpr ⟨_,mem_univ (a i),v⟩) x y t
protected lemma along [∀i,PseudoMetricSpace (U i)] (φ:(i:I)→T i→U i)(h:Deal f)(p:∀ε:ℝ,0<ε→∃δ:ℝ,0<δ∧∀i x y,dist (f i x) (f i y)<δ → dist (φ i (f i x)) (φ i (f i y)) < ε): Deal (T:=U) (fun i x=> φ i (f i x)):=by
 intro ε e; obtain ⟨δ,g,v⟩:=p ε e; obtain ⟨P,u,w⟩:=h δ g; exact ⟨P,u,fun x y t i=>v i x y (w x y t i)⟩
protected lemma clip {A B:Type*}[PseudoMetricSpace A][PseudoMetricSpace B]{f:I→X→A}(h:Deal f){Z:Set A}(z:IsCompact Z)(v:∀i x,f i x∈ Z){g:A→ B}(q:Continuous g):Deal (I:=I) (fun i x=> g (f i x)):=by
 apply Deal.along (U:=fun _=>B) (fun _=>g) h
 intro ε e
 obtain ⟨δ,u,w⟩:= Metric.uniformContinuousOn_iff.mp (z.uniformContinuousOn_of_continuous q.continuousOn) ε e
 exact ⟨δ,u,fun i x y=> w _ (v i x) _ (v i y)⟩
protected lemma post {A B:Type*}[PseudoMetricSpace A][CompactSpace A][PseudoMetricSpace B]{f:I→ X→A}(h:Deal f){g:A→B}(q:Continuous g):Deal (I:=I) (fun i x=>g (f i x)):=h.clip isCompact_univ (fun _ _=>Set.mem_univ _) q
end Deal
end
section
variable [∀i,NormedAddCommGroup (T i)]
structure Menu (f:(i:I)→X→T i) : Prop where
 deal : Deal f
 budget : ∃ l:ℝ,0≤l ∧ ∀i x, ‖f i x‖≤ l
namespace Menu
variable {f g:(i:I)→X→ T i}
protected theorem congr (h:Menu f){g}(v:∀i x,f i x=g i x):Menu g:=(funext fun i=>funext fun x=>v i x) ▸ h
protected theorem re (h:Menu f)(a:J→ I):Menu (T:=fun j=> T (a j)) (fun j x=> f (a j) x):=by
 obtain ⟨l,h₀,q⟩:=h.budget; exact ⟨h.deal.re a,l,h₀,fun j=>q _⟩
protected theorem cnst (f:∀i,T i){l:ℝ}(v:0≤l)(t:∀i,‖f i‖≤l):Menu (X:=X) (T:=T) (fun i _=> f i):=⟨Deal.pure _,l,v,fun i _=> t i⟩
protected theorem zero :Menu (I:=I) (X:=X) (T:=T) (fun i _=>0):=Menu.cnst _ le_rfl (by simp)
protected theorem cond (h:Menu f)(e:Menu g)(A:I→Prop):Menu (T:=T) (fun i=> if A i then f i else g i):=by
 obtain ⟨l,n,y⟩:=h.budget; obtain ⟨m,u,x⟩:=e.budget; refine ⟨h.deal.cond e.deal A,l+m,by linarith,fun i v=>?_⟩; split
 · exact (y i v).trans (by linarith)
 exact (x i v).trans (by linarith)
protected theorem add (h:Menu f)(e:Menu g): Menu (T:=T) (fun i x=> f i x+g i x):=by
 obtain ⟨l,n,y⟩:=h.budget; obtain ⟨m,u,x⟩:=e.budget; refine ⟨Deal.along (T:=fun i=>T i × T i) (fun i x=> x.1+x.2) (h.deal.prod e.deal) ?_,l+m,add_nonneg n u,fun i a=> (norm_add_le ..).trans (add_le_add (y ..) (x ..))⟩
 intro ε p; refine ⟨ε/2,by linarith,fun i x y' w=>?_⟩; rw [Prod.dist_eq,max_lt_iff] at w; obtain ⟨A,B⟩:= w
 exact lt_of_le_of_lt (dist_add_add_le ..) (by dsimp at A B ⊢; linarith)
protected theorem total (s:Finset J)(F:J→(i:I)→X→T i)(h:∀j∈s,Menu (F j)): Menu (T:=T) (fun i x=>∑ j∈s,F j i x):=by
 induction s using Finset.induction_on with
 | empty=> simpa only [sum_empty] using Menu.zero (I:=I) (T:=T) (X:=X)
 | insert a s v ih=> simp_rw [sum_insert v]; exact (h _ (mem_insert_self ..)).add (ih fun j k=>h j (mem_insert_of_mem k))
-- bound once via generic distributive binary estimate, no CStar assumption
lemma bil [∀i,NormedAddCommGroup (U i)] {V:I→Type*} [∀i,NormedAddCommGroup (V i)] {g:(i:I)→ X→U i}
 (F:(i:I)→ T i→U i→V i) (u:∀i x y, ‖F i x y‖≤ ‖x‖ * ‖y‖)(a:∀i x q y,F i (x-q) y=F i x y-F i q y)(b:∀i x y q,F i x (y-q)=F i x y-F i x q) (h:Menu f)(e:Menu g):Menu (T:=V) (fun i x=> F i (f i x) (g i x)):=by
 obtain ⟨l,n,r⟩:=h.budget; obtain ⟨m,w,s⟩:=e.budget
 refine ⟨Deal.along (fun i (z:T i × U i)=> F i z.1 z.2) (h.deal.prod e.deal) ?_,l*m,mul_nonneg n w,fun i x=> (u ..).trans (mul_le_mul (r ..) (s ..) (norm_nonneg _) n)⟩
 intro ε p; let δ:= ε/(l+m+1); have P:0<δ:=div_pos p (by linarith)
 refine ⟨δ,P,fun i x y v=>?_⟩; rw [Prod.dist_eq,max_lt_iff] at v; obtain ⟨v,g'⟩:= v; dsimp at v g' ⊢
 refine lt_of_le_of_lt (dist_triangle _ (F i (f i x) (g i y)) _) ?_
 rw [dist_eq_norm,dist_eq_norm,← b,← a]; rw [dist_eq_norm] at v g'; refine lt_of_le_of_lt (add_le_add (u ..|>.trans (mul_le_mul (r ..) g'.le (norm_nonneg _) n)) (u ..|>.trans (mul_le_mul v.le (s ..) (norm_nonneg _) P.le))) ?_
 have hx:δ*(l+m+1)=ε:=div_mul_cancel₀ _ (by linarith); nlinarith
end Menu
end
section
namespace Menu
protected theorem scale {R : Type*}[NormedField R][∀i,NormedAddCommGroup (T i)][∀i, NormedSpace R (T i)] {f:I→X→ R}{g:(i:I)→X→ T i}(h:Menu f)(e:Menu g):Menu (T:=T) (fun i x=> f i x • g i x):= bil (fun _ x y=> x • y) (fun _ x y=> (norm_smul x y).le) (fun _=>sub_smul) (fun _=>smul_sub) h e
protected theorem mul [∀i,NormedRing (T i)] {f g:(i:I)→ X→T i}(h:Menu f)(e:Menu g):Menu (T:=T) (fun i x=> f i x * g i x):= bil (fun _ x y=> x*y) (fun _=>norm_mul_le) (fun _=>sub_mul) (fun _=>mul_sub) h e
protected theorem clip {A B:Type*}[PseudoMetricSpace A][NormedAddCommGroup B]{f:I→X→ A}(h:Deal f){Z:Set A}(z:IsCompact Z)(v:∀i x,f i x∈ Z){g:A→ B}(q:Continuous g):Menu (I:=I) (fun i x=> g (f i x)):=by
 obtain ⟨k,w⟩:= (z.image q.norm).bddAbove; exact ⟨h.clip z v q,max k 0,le_max_right ..,fun i x=> (w ⟨_,v i x,rfl⟩).trans (le_max_left ..)⟩
protected theorem post {A B:Type*}[PseudoMetricSpace A][CompactSpace A][NormedAddCommGroup B]{f:I→ X→A}(h:Deal f){g:A→ B}(q:Continuous g):Menu (I:=I) (fun i x=>g (f i x)):=Menu.clip h isCompact_univ (fun _ _=>Set.mem_univ _) q
end Menu
end
end YM.CF.Buffered.Afterglow.Satin
