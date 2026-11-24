import YM.CF.Vp929.Paint.Ticket
set_option autoImplicit false
set_option maxHeartbeats 660000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Paint
open scoped Classical
variable {I J U V A B:Type*}[Fintype I][DecidableEq I]
namespace Ticket
def scaleM(p:Ticket I):ℤ:=∑i,p.bill i
def unif(I:Type*)[Fintype I][Nonempty I] : Ticket I:= ⟨fun _=>1, by simp, by simp [Fintype.card_pos]⟩
def apart(p:Ticket I)[Fintype J](q:Ticket J): Ticket (I×J):= ⟨fun a=> p.bill a.1 * q.bill a.2,fun a=>mul_nonneg (p.nn _) (q.nn _),by rw [Fintype.sum_prod_type]; simp_rw [← mul_sum,← sum_mul]; exact mul_pos p.pos q.pos⟩
theorem apairs[Fintype J][Fintype A][Fintype B][Fintype U][Fintype V](p:Ticket I)(q:Ticket J) {x:I→A}{y:I→B}{a:J→U}{b:J→V}(h:p.Indep x y)(t:q.Indep a b): (apart p q).Indep (Prod.map x a) (Prod.map y b):=by
 have H(f:I→ℤ)(g:J→ℤ):∑ w:I×J,(apart p q).bill w * (f w.1*g w.2)=(∑i:I,p.bill i*f i)*(∑i:J,q.bill i*g i):=by rw [Fintype.sum_prod_type,sum_mul]; refine sum_congr rfl fun i _=>?_; rw [mul_sum]; apply sum_congr rfl; intro j _; dsimp [apart]; ring
 have v: ∑ w:I×J,(apart p q).bill w=(∑i:I,p.bill i)*(∑j:J,q.bill j):=by simpa using H (fun _=>1) (fun _=>1)
 apply dirac; rintro ⟨u,v₁⟩ ⟨i,j⟩; have hu:=h (fun k=>Cr (k=u)) (fun k=>Cr (k=i)); have hv:=t (fun k=>Cr (k=v₁)) (fun k=>Cr (k=j)); unfold both Function.comp at *; simp_rw [Prod.map,Prod.mk.injEq,Cr_imp,mul_mul_mul_comm (Cr (x _=u)) (Cr (a _=v₁))]
 rw [H (fun k=>Cr (x k=u)*Cr (y k=i)) (fun k=>Cr (a k=v₁)*Cr (b k=j)),H (fun k=>Cr (x k=u)) (fun k=>Cr (a k=v₁)),H (fun k=>Cr (y k=i)) (fun k=>Cr (b k=j)),v,mul_mul_mul_comm (∑x:I,_) (∑j:J,_),hu,hv]; ring
variable {Ω X Y:I→Type*}[∀ i,Fintype (Ω i)][∀ i,Fintype (X i)][∀ i,Fintype (Y i)]
def together (p:∀ i,Ticket (Ω i)):Ticket (∀ i,Ω i):= ⟨fun x=> ∏i:I,(p i).bill (x i), fun i=>Finset.prod_nonneg fun _ _=>Ticket.nn .., by rw [← Fintype.prod_sum]; exact Finset.prod_pos fun i _=> (p i).pos⟩
abbrev dash (W:∀ i,Ω i→X i)(f:∀ i,Ω i)(i):= W i (f i)
lemma docks(p:∀ i,Ticket (Ω i))(W:∀ i,Ω i→X i)(H:∀ i,Ω i→ Y i)(h:∀i,(p i).Indep (W i) (H i)): (together p).Indep (dash W) (dash H):=by
 have v(f:∀ i,Ω i→ℤ):∑w:∀i,Ω i,(together p).bill w*∏i:I,f i (w i)=∏i:I,∑j:Ω i,(p i).bill j*f i j:=by unfold together; simp_rw [←prod_mul_distrib,Fintype.prod_sum]
 have T: (∑w:∀i,Ω i,(together p).bill w)=∏i:I,∑j:Ω i,(p i).bill j:=by simpa using v (fun _ _=>1)
 apply dirac; intro x y; unfold both; simp_rw [funext_iff, dash, Cr_prod, ← prod_mul_distrib]
 rw [v (fun i j=> Cr (W i j=x i)*Cr (H i j=y i)), v (fun i j=> Cr (W i j=x i)), v (fun i j=> Cr (H i j=y i)),T,←prod_mul_distrib,←prod_mul_distrib]; refine prod_congr rfl fun i _=>?_ ; exact h i (fun z=>Cr (z=x i)) (fun z=>Cr (z=y i))
end Ticket
abbrev Vision{Ω:Type*}(X:Finset I)(s:Ω→I→A)(v:Ω)(i:X):A:= s v i
lemma voyage_set[AddCommGroup I](x:I)(v:x≠0):∃ p:Ticket (I→Fin 4), p.bill= Paint.Voyage.budget x v∧∀ S T:Finset I, Disjoint S T→(∀ i∈S,i+x∉ T)→(∀ i∈T,i+x∉ S)→ p.Indep (Vision S id) (Vision T id):=by
 let W:=Paint.Voyage.budget x v; let t:Ticket (I→Fin 4):=⟨W,Paint.Voyage.nonn x v,Paint.Voyage.hearty x v⟩
 let M (S:Finset I)(g:S→Fin 4):Mask I :=fun i=> if p:i∈S then fun k=>Cr (k=g ⟨i,p⟩) else 1
 have Z(S:Finset I)(g:S→Fin 4)(i:I)(v:i∉S):clear (M S g) i:=dif_neg v
 have K(S:Finset I)(g:S→Fin 4)(p:I→Fin 4): Cr (Vision S id p=g)= ∏i:I, M S g i (p i):=by
    let Q(i):Prop:=∀ h : i ∈ S,p i=g ⟨i,h⟩; rw [show (Vision S id p=g)=(∀ i,Q i) from propext ⟨fun v i z=> congrFun v (⟨i,z⟩:S),fun v=> funext fun i=>v i i.property⟩,Cr_prod]; refine prod_congr rfl fun i _=>?_ ; by_cases h:i∈S; rw [show M S g i= _ from dif_pos h]; simp [Q,h]; simp [Z _ _ i h,Q,h]
 refine ⟨t,rfl,fun S T h u l=> Ticket.dirac t fun a b=>?_⟩; let f:=M S a; let g:= M T b
 have Q(i j:I)(q:i∈S→j∉T):clear f i∨clear g j:= (em (i∈S)).elim (fun p=> Or.inr (Z _ _ _ (q p))) (fun p=> Or.inl (Z _ _ _ p))
 obtain j:=Paint.Voyage.halves x v f g (fun i=> ⟨Q i i (fun v=> Finset.disjoint_left.mp h v),Q i i (fun v=> Finset.disjoint_left.mp h v)⟩) (fun i=> ⟨Q _ _ (u i), Q _ _ fun p z=> l i z p⟩)
 unfold Ticket.both; simp_rw [K,← prod_mul_distrib]; exact j

lemma ticket_set[Fintype A](F: Ticket A)(S T: Finset I)(h:Disjoint S T): (Ticket.together (fun _:I=> F)).Indep (Vision S id) (Vision T id):=by
 let M(S:Finset I)(i:I)(a:A):Option A:= if i∈S then some a else none; let t:=Ticket.together (fun _:I=> F); have P(S:Finset I)(i j:I→A) (v:Ticket.dash (M S) i=Ticket.dash (M S) j): Vision S id i=Vision S id j:=by funext a; rcases a with ⟨a,e⟩; have p:=congrFun v a; simpa [Vision,Ticket.dash,M,e] using p
 have H(i:I):F.Indep (M S i) (M T i):=by
    by_cases v:i∈S; · apply Ticket.ind_sym; simpa [M,Finset.disjoint_left.mp h v] using F.ind_const none (M S i)
    simpa [M,v] using F.ind_const none (M T i)
 exact t.less (fun i j _ _=> P S i j) (fun i j _ _=> P T i j) (Ticket.docks _ _ _ H)
end YM.CF.VolumeCape
