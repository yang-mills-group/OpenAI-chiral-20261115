import WakeRoad.Alley
/-! # Full pigment agenda for n-even mixed Marks. Uses ofFn to keep the Fock-word order (do not use Finset.prod or mean at Hue stage). -/
set_option autoImplicit false
set_option maxHeartbeats 270000
noncomputable section
namespace YM.WakeRoad
open Function Filter Finset
open scoped Topology BigOperators Classical
section frame
variable {R X Y:Type*}[CommSemiring R][Semiring X] [Algebra R X] [Fintype Y]
variable {n:ℕ} (β:Fin n→X)
/-- Ordered product on this specified list of appointments. -/
def serve {X:Type*}[Monoid X]{n:ℕ}(x:Fin n→X): X:= (List.ofFn x).prod
lemma steam {X:Type*}[Monoid X](x:Fin (n+1)→X):serve x= x 0 * serve (x ∘ Fin.succ):=by unfold serve; rw [List.ofFn_succ,List.prod_cons]; rfl
lemma serve_map {Z I:Type*}[Monoid Z]{x:Fin n→I}(e:I→Z) : serve (e ∘ x)=(List.map e (List.ofFn x)).prod:=by rw [List.map_ofFn]; rfl
lemma sum_film {A X:Type*}[Fintype A][AddCommMonoid X](f:(Fin (n+1)→A)→X):
    (∑ t,f t)=∑ a, ∑ t:Fin n→A, f (Fin.cons a t):=by
 let u:= Fin.consEquiv (fun _:Fin (n+1)=>A)
 rw [← Equiv.sum_comp u f,show (∑ x:A × (Fin n→A), f (u x))=_ from Fintype.sum_prod_type (fun x:A× (Fin n→A)=> f (u x))]; rfl
lemma serve_expand (α:Fin n→ Y→R)(x:Fin n→Y→X): serve (fun i=> ∑ j:Y, α i j • x i j)=∑ t:Fin n→Y,(∏ i, α i (t i)) • serve (fun i=> x i (t i)):= by
 induction n with
 | zero=>
    let z:Fin 0→Y:=Fin.elim0
    rw [Fintype.sum_subsingleton _ z]; simp [serve]
 | succ n ih=>
    let a(i:Fin n)(j):=α i.succ j; let y(i:Fin n)(j):=x i.succ j
    rw [steam,sum_film]; change ((∑ j:Y, α 0 j • x 0 j)* serve (fun i=>∑ j:Y,a i j • y i j))= _
    rw [ih,sum_mul]; refine sum_congr rfl fun j _=>?_ ; rw [mul_sum]; refine sum_congr rfl fun q _=>?_
    rw [Fin.prod_univ_succ,steam,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; simp [a,y,Function.comp_def]
lemma serve_smul (r:Fin n→R)(x:Fin n→X) : serve (fun i=>r i • x i)=(∏ i,r i) • serve x:=by
 induction n with
 | zero=> simp [serve]
 | succ n ih=> rw [steam,steam,Fin.prod_univ_succ,show (fun i=>r i • x i)∘Fin.succ=fun i:Fin n=>r i.succ • x i.succ from rfl, ih (fun i:Fin n=> r i.succ) (fun i=>x i.succ), Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rfl 
end frame

section measurements
variable {Q:Type*}[NormedCommRing Q] [NormOneClass Q] {n:ℕ} {H d:ℝ}
lemma propCost(x:Fin n→ Q)(h:∀ i, ‖x i‖≤H)(p:0≤H): ‖∏ i:Fin n,x i‖≤ H^n:=by
 induction n with
 | zero=> simp
 | succ n ih=> rw [Fin.prod_univ_succ,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (h _) (ih _ (fun i=> h i.succ)) (norm_nonneg _) p)
lemma propCompare(x y:Fin n→ Q)(hx:∀ i, ‖x i‖≤H)(hy:∀ i, ‖y i‖≤H)(hc:∀ i,‖x i-y i‖ ≤ d)(p:0≤H)(e:0≤d):
    ‖(∏ i:Fin n,x i)-∏ i,y i‖≤n* d*H^(n-1):=by
 induction n with
 | zero=> simp
 | succ n ih=>
    let a:=x 0; let b:= y 0; let X:=∏ i:Fin n,x i.succ; let Y:=∏ i:Fin n,y i.succ
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]; change ‖a*X-b*Y‖≤ _; rw [show a*X-b*Y=(a-b)*X+b*(X-Y) by ring]; refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul (hc _) (propCost _ (fun i:Fin n=>hx i.succ) p) (norm_nonneg _) e)) ((norm_mul_le ..).trans (mul_le_mul (hy _) (ih _ _ (fun i=>hx i.succ) (fun i=>hy i.succ) (fun i=>hc i.succ)) (norm_nonneg _) p))).trans_eq ?_)
    obtain _|n:=n <;> simp only [Nat.add_sub_cancel,Nat.cast_succ,Nat.cast_zero,pow_zero] <;> try rw [pow_succ H n]
    all_goals ring
omit [NormOneClass Q] in
lemma finiteBound {I:Type*}[Fintype I](A:I→Q)(h:∀ i,‖A i‖≤H): ‖∑ i,A i‖ ≤ (Fintype.card I:ℝ)*H:= (norm_sum_le ..).trans ((sum_le_sum (fun i _=> h i)).trans_eq (by simp))
end measurements
#print axioms serve_expand
end YM.WakeRoad
