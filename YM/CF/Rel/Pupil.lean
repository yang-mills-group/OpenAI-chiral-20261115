import YM.CF.Rel.Sept
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
-- combine displacement & valuations
variable{k i:Site n}{f g:SpaceX G n}{U: Salt n G}{s t j K d:ℕ}{B:ℝ}
lemma Travel.up (p:Travel k m j s r σ A f)(hp:A≤ C)(hx:l≤ j)(ht:s ≤ t)(hu:r ≤ d)(he:B≤ σ): Travel k m l t d B C f:=by
 obtain ⟨P,X,h1,h2,h3,h4,h⟩:=p.profit
 exact ⟨P,X,h1,h2.trans hp,fun i hi=>(h3 _ hi).trans hu,fun i=> ⟨((h4 i).1.under he ht le_rfl),((h4 i).2.1.under he ht le_rfl),fun u hu=> (h4 i).2.2 u (hu.trans_le hx)⟩,h⟩
lemma Travel.single (P:CakeF f 0 r m σ A)(p:cFoot j (satX f))(hp:separation 0 i≤ l)(h:l+r ≤ s) (hA:0≤ A): Travel k m j s s σ A (stroll k i f-f):=by
 let W:=Pi.single (M:=fun _=> SpaceX G n) i f; let X:= Pi.single (M:=fun _=>ℝ) i A; refine ⟨W,X,fun b=> ?_, ?_,fun b he=> ?_, fun b=> ?_,?_⟩
 · by_cases hh:b=i<;>simp [W,X, *,Pi.single_apply]
 · simp [X,Pi.single_apply]
 · unfold W at he; rw [Pi.single_apply] at he; split at he; next hx=>rw [hx]; omega
   exact False.elim (he rfl)
 · by_cases he:b=i
   · rw [he]; simp only [W,X,Pi.single_eq_same]; exact ⟨P.under le_rfl (by omega) le_rfl,strollX k i r s P (by omega),p⟩
   simp only [W,X,Pi.single_apply,he,↓reduceIte,zero_a]; exact ⟨CakeF.zeroP le_rfl,CakeF.zeroP le_rfl,hatZ⟩
 rw [Fintype.sum_eq_single i]; simp [W]; intro b hp; simp [W,Pi.single_apply,hp]
lemma Travel.sigma {α:Type}(p:Finset α)(F:α→SpaceX G n)(c:α→ℝ)(h:σ>0)(hp:j≤ m)(ht:∀ i∈p,Travel k m j r r σ (c i) (F i)):Travel k m j r r σ (∑ i∈p,c i) (∑ i∈p,F i):=by induction p using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact Travel.stilt le_rfl le_rfl
 | @insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (ht i (by simp)).plus (ih fun _ u=>ht _ (mem_insert_of_mem u)) h hp
open Jet
lemma Travel.cakeF(p:Travel k m j r t σ A f)(h:0<σ)(hp:j≤ m): CakeF f 0 r m σ (2*A) ∧ cFoot j (satX f):=by
 obtain ⟨X,Y,hY,hp',hc,ht,hx⟩:=p.profit; rw [hx]; have hw:= CakeF.sigmaH (P:=fun i=> stroll k i (X i)-X i) univ fun i _=> (ht i).2.1.less (ht i).1; have heZ:‖(0:InputZ G n)‖<σ:=by simpa using h
 refine ⟨hw.under le_rfl le_rfl (by rw [sum_add_distrib,two_mul]; exact add_le_add hp' hp'),?_⟩
 let V(i:Site n):Salt n G:= trim j (satX (X i)); have he(i):prism j (X i) (V i):=(argent (((ht i).1.ledger _ heZ).smooth.of_le (by exact_mod_cast hp))).mp (ht i).2.2
 exact (asideF ((hw.ledger _ heZ).smooth.of_le (by exact_mod_cast hp)) _ (prism.sumZ univ _ _ (fun i _=> prism.sub (prizeC k i (he i)) (he i)))).1
lemma sum_ride(k:Site n)(i:Site n)(p:Salt n G)(f:SpaceX G n)(x:Site n): stroll k x (stroll k i f)=stroll k (x+i) f:=by
 ext1 a; simp only [stroll,Sean,pulse_l,←mul_assoc]; congr 1; apply congr_arg f; ext1 p;
 unfold Lattice.translate; congr 2; change (p.1:Site n)+i+x=_; abel
end YM.CF.Rel
