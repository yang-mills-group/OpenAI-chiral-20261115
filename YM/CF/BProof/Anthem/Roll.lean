import Mathlib.Data.Finset.NoncommProd
import Mathlib
/- distributive identity with exact sum (site expansions). Use heterogeneous types. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Anthem
open Filter Function Finset
open scoped BigOperators Classical
section
variable {I K V:Type}[Fintype I][DecidableEq I][Fintype K][DecidableEq K][AddCommMonoid V]
variable (x: I→K)(T:I→ Finset K)(S:Finset I)(i:I)
def roll := univ.filter fun f:I→ K=> ∀ i:I, ite (i∈ S) (f i∈ T i) (f i=x i)
lemma roll_s (f:I→ K): f∈ roll x T S ↔ ∀ i, ite (i∈ S) (f i∈ T i) (f i=x i):= by simp [roll]
lemma sum_roll (h:i∉ S)(F:(I→K)→ V) :
    ∑ w∈ roll x T (insert i S), F w = ∑ j∈ T i,∑ w∈ roll x T S,F (update w i j):=by
 let W:=roll x T (insert i S); let Z:=roll x T S; let V:= (T i)×ˢ Z; let g(p:K × (I→ K)):= update p.2 i p.1
 have hh(j:K)(w:I→K) : g (j,w) i=j:= update_self ..; have he(f)(hv:f∈ Z): f i=x i:=by have hp:=(roll_s ..).1 hv i; simpa [h] using hp
 have hP(p)(hp:p∈V): g p∈W:= by apply (roll_s ..).2; intro k; obtain ⟨j,w⟩:=p; obtain ⟨v,t⟩:= (mem_product.mp hp); by_cases e:k=i; subst k; rw [hh]; simp [v]; unfold g; simpa [e] using (roll_s ..|>.1 t k)
 have hx: Set.InjOn g (↑V):=by
   rintro ⟨j,w⟩ h₀ ⟨a,b⟩ h₁ e; apply Prod.ext; exact (hh j w).symm.trans ((congrFun e i).trans (hh a b)); ext k; by_cases y:k=i
   · subst k; exact (he w (mem_product.mp h₀ |>.2)).trans (he b (mem_product.mp h₁ |>.2)).symm
   simpa [g,y] using congrFun e k
 have hz:W= V.image g:=by
    ext w; refine ⟨fun u=>?_,?_⟩; swap
    · intro t; obtain ⟨v,h,rfl⟩:=mem_image.mp t; exact hP v h
    let A:=update w i (x i); have ht:= (roll_s ..).1 u
    refine mem_image.mpr ⟨(w i,A),mem_product.mpr ⟨?_,?_⟩,?_⟩; simpa using ht i
    · refine (roll_s ..).2 fun j=> ?_; by_cases g:i=j; rw [←g]; simp [A,h]; have h':=ht j; simpa [A,Ne.symm g] using h' -- .symm of ne proof tune
    simp [g,A]
 change ∑ w∈ W,_=_; rw [hz,sum_image, sum_product]; exact hx -- tune
end
variable {I K A:Type}[Fintype I][DecidableEq I][Fintype K][DecidableEq K][Semiring A]
def edgeP (f:I→ A)(c:Pairwise (Commute on f))(S:Finset I): A:= noncommProd S f (fun _ _ _ _ h=> c h)
@[simp] lemma edgeP_nil (f:I→ A)(c:Pairwise (Commute on f)) : edgeP f c ∅=1:= by simp [edgeP]
lemma edgeP_cons(f:I→A)(c:Pairwise (Commute on f))(S:Finset I)(i:I)(h:i∉S): edgeP f c (insert i S)=f i*edgeP f c S:= noncommProd_insert_of_notMem S i f _ h -- h missing
lemma noncomm_sumSet (x:I→K)(T:I→Finset K)(F:I→K→ A)(p:∀ f:I→ K, Pairwise (Commute on (fun i=>F i (f i))))(v: Pairwise (Commute on (fun i=>∑ j∈ T i,F i j))) (S:Finset I):
 edgeP (fun i=>∑ j∈ T i,F i j) v S=∑ w∈ roll x T S,edgeP (fun i=> F i (w i)) (p w) S:=by
 induction S using Finset.induction_on with
 | empty=> rw [show roll x T ∅={x} from ?_]; simp; ext w; rw [roll_s]; simp; exact funext_iff.symm -- tune
 | insert i S u ih=>
   rw [edgeP_cons _ _ S i u, ih,sum_mul]; simp_rw [mul_sum]; rw [sum_roll x T S i u]; refine sum_congr rfl (fun j hj=> sum_congr rfl fun t ht=>?_); rw [edgeP_cons _ _ S i u, update_self]; congr 1; exact noncommProd_congr rfl (fun k (hk:k∈S)=> by rw [update_of_ne (show k≠i from fun f=> u (f ▸ hk))]) _ -- tune
end YM.CF.BProof.Anthem
