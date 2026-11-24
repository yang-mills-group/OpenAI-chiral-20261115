import YM.CF.Buffered.Streak
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice
open Fin.NatCast
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
section many
variable {I X : Type*}
def recur {n:ℕ}[NeZero n](f:Fin n→X)(i:ℕ): X:= f (↑i:Fin n)
lemma recur_of {n:ℕ}[NeZero n](f:Fin n→X)(i:Fin n): recur f i.val=f i :=by simp [recur,Fin.cast_val_eq_self]
lemma recur_zero {n:ℕ}[NeZero n](f:Fin n→X): recur f 0=f 0:=by simp [recur]
lemma recur_full {n:ℕ}[NeZero n](f:Fin n→X): recur f n=recur f 0:=by simp [recur]
lemma run_map_aux {X:Type*}[Nonempty X][Fintype X]{R:Type*}[Semiring R](F:ℕ→X→R) (n:ℕ)(x:X) : run (fun i=>∑ v,F i v) n=∑ v : Many n X, run (fun i=> if h:i < n then F i (v ⟨i,h⟩) else F i x) n:= by
 induction n with
 | zero=> simp [run]
 | succ n ih=>
    rw [run_succ,ih,Finset.mul_sum]; simp_rw [sum_mul]; let T : Equiv (X× Many n X) (Many (n+1) X):=  Fin.snocEquiv (fun _=>X) -- order unknown
    conv_rhs=> rw [← Equiv.sum_comp T]
    rw [Fintype.sum_prod_type]; refine sum_congr rfl fun v _=> sum_congr rfl fun u _=> ?_
    rw [run_succ,dif_pos (by omega)]; congr 1
    · apply run_congr; intro i h; rw [dif_pos h, dif_pos (by omega)]; change F _ _=F _ (Fin.snoc (α:=fun _=>X) u v (Fin.castSucc ⟨i,h⟩)); rw [Fin.snoc_castSucc]
    change F _ _=F _ (Fin.snoc (α:=fun _=>X) u v (Fin.last n)); rw [Fin.snoc_last]
lemma run_map {X:Type*}[Nonempty X][Fintype X]{R:Type*}[Semiring R](F:ℕ→X→R)(n:ℕ)[NeZero n] : run (fun i=>∑ v,F i v) n=∑ v : Many n X, run (fun i=>F i (recur v i)) n:= by
 rw [run_map_aux F n (Classical.arbitrary X)]; refine sum_congr rfl fun i _ => run_congr _ _ _ fun k h=> ?_; rw [dif_pos h,recur_of i (⟨k,h⟩:Fin n)]
def rota {n:ℕ} [NeZero n]: Equiv.Perm (Many n X) where
 toFun f x:= f (x+1)
 invFun f x:= f (x-1)
 left_inv u := funext fun i=> by dsimp only; rw [sub_add_cancel]
 right_inv u := funext fun i=> by dsimp only; rw [add_sub_cancel_right]
lemma rota_at {n:ℕ}[NeZero n](b : Many n X)(i:ℕ): recur (rota b) i=recur b (i+1):=by change b _= b _; rw [Nat.cast_add, Nat.cast_one]
end many
section wrap
variable {I B : Type*}[LinearOrder I][Fintype I]
-- F indeck G outdeck
variable (S:ℕ→Finset I) (f g:ℕ→ FC I) (p:ℕ→Bool)
private lemma belt0 (n:ℕ) : f 0 * run (fun i=> g i*f (i+1)) n=run (fun i=> f i*g i) n * f n :=by
 induction n with
 | zero=> simp [run]
 | succ n ih=> rw [run_succ, ←mul_assoc, ih,run_succ]; noncomm_ring
open Sector (grainB grain_self)
open Reflect (chord)
private lemma apart_wrap (A B C:FC I)(c k:Bool) (p:A*B=grainB c k • (B*A)) (q:A*C=grainB c k • (C*A)) : A*(B*C)=(B*C)*A:=by rw [←mul_assoc,p,Algebra.smul_mul_assoc,mul_assoc,q,Algebra.mul_smul_comm,smul_smul,grain_self,one_smul,mul_assoc]
-- convention coefficient associated to outgoing (conj phase law adapt)
def outer (n i:ℕ) (k:Bool) : ℂ := if i+1=n then star (chord k) else chord k
theorem belt (n:ℕ) (h:0 < n)(w:p 0=p (n+1)) (a : ∀ i≤n,Sector (S i) (p i) (f i)) (b:∀ i≤n,Sector (S i) (p (i+1)) (g i)) (v:f 0=f (n+1)) (t : f 0 * g 0= grainB (p 0) (p 1) • (g 0*f 0)) (k : lonely S (n+1)) :
 run (fun i=> outer (n+1) i (p (i+1)) • (g i*f (i+1))) (n+1)= run (fun i=> chord (p (i+1)) • (f i*g i)) (n+1) := by
 let V(i:ℕ):= g i * f (i+1); have hp := run_congr (fun i=> outer (n+1) i (p (i+1)) • V i) (fun i=> chord (p (i+1)) • V i) n (fun i h=>by dsimp only [outer]; rw [if_neg (by omega)])
 let c:= fun i=>chord (p (i+1)); let x:= run c n
 have he: outer (n+1) n (p (n+1)) • V n=c n • (f 0*g n):=by
    have he := k n (by omega) 0 h; unfold outer V c; rw [if_pos rfl,←v,(b n le_rfl).apart (a _ (Nat.zero_le n)) he,←w, smul_smul]; congr 1; cases p 0<;> simp [grainB, chord]
 have hr : f 0 * run V n=run V n * f 0:=by
    refine run_commutes _ _ _ fun i y=>apart_wrap _ _ _ _ (p (i+1)) ?_ ((a _ (Nat.zero_le _)).apart (a (i+1) y) (k (i+1) (by omega) 0 (by omega)).symm)
    cases i; exact t; exact (a _ (Nat.zero_le _)).apart (b _ y.le) (k _ (by omega) 0 (by omega)).symm
 rw [run_succ, hp, ←run_scale, run_succ, ←run_scale]; change (x • _)*(outer (n+1) n _ • V n)= _
 rw [he, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ←mul_assoc, ←hr]; apply congrArg; apply congrArg; rw [belt0 f g]; noncomm_ring
end wrap
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.belt
