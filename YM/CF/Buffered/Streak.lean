import YM.CF.Buffered.Channels
import YM.CF.Buffered.Inflate
import YM.CF.Buffered.Cycled

/-! Ordered CAR products of opposite-plane systems. Cocycle for cyclic product expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock Finset Filter MeasureTheory Lattice
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {F A : Type*}
section alg
variable [Monoid F]
def run (f : ℕ→ F) (n:ℕ) := ((List.range n).map f).prod
lemma run_zero (f:ℕ→F) : run f 0=1 := rfl
lemma run_succ (f:ℕ→F) (n:ℕ) : run f (n+1)=run f n * f n := by simp [run,List.range_succ]
lemma run_congr (f g:ℕ→F) (n:ℕ) (v:∀ i<n,f i=g i) : run f n=run g n := by
 induction n with
 | zero=> rfl
 | succ n ih=> rw [run_succ, run_succ, v n (by omega), ih fun i h=> v i (by omega)]
lemma run_one (n:ℕ) : run (fun _=> (1:F)) n=1 :=by induction n with| zero=> rfl | succ n ih=>rw [run_succ,ih,mul_one]
lemma run_commutes (f:ℕ→F) (y:F) (n:ℕ) (u:∀ i<n,y*f i=f i*y) : y* run f n=run f n*y:= Commute.list_prod_right _ _ (fun x h=>by obtain ⟨x,v,rfl⟩:= List.mem_map.mp h; exact u _ (List.mem_range.mp v))
end alg
lemma run_prod [CommMonoid F] (n:ℕ) (f : ℕ→ F) : run f n=∏ i:Fin n, f i.val := by
 induction n with
 | zero=> simp [run]
 | succ n ih=> rw [run_succ,ih,Fin.prod_univ_castSucc]; rfl
lemma run_range [CommMonoid F] (n:ℕ)(f:ℕ→F) : run f n=∏ j∈range n,f j := by rw [run_prod, Fin.prod_univ_eq_prod_range]

abbrev gap (P:ℕ→Bool) (i:ℕ) := (P i).xor (P (i+1))
section car
variable {I : Type*} [LinearOrder I][Fintype I] (S:ℕ→Finset I)
local notation "A"=> FC I
variable (F G : ℕ→ FC I) (n:ℕ)
variable (c d : ℕ→Bool)
def confined := ∀ i<n, Sector (S i) (gap c i) (F i)
def lonely := ∀ i<n,∀ j < i,Disjoint (S i) (S j)
private lemma wider {S T:Finset I}{b:Bool}{F:FC I}(h:S ⊆ T)(p:Sector S b F):Sector T b F:=by
 induction p with
 | one=>exact .one
 | zero=>exact .zero _
 | up i k=>exact .up i (h k)
 | down i k=>exact .down i (h k)
 | add _ _ p q=>exact p.add q
 | mul _ _ p q=>exact p.mul q
 | scale _ c p=>exact p.scale _
theorem run_sector (p : confined S F n c) : Sector ((range n).biUnion S) ((c 0).xor (c n)) (run F n) := by
 induction n with
 | zero=> rw [run_zero,Bool.xor_self]; exact .one
 | succ n ih=>
    let X:= (range (n+1)).biUnion S
    have hk(i:ℕ)(p:i<n+1): S i ⊆ X:= subset_biUnion_of_mem _ (mem_range.mpr p)
    rw [run_succ]; apply Eq.mp _ ((wider (show (range n).biUnion S ⊆ X from (fun i t=> let ⟨x,p,v⟩:=mem_biUnion.mp t; hk _ (by have e:=mem_range.mp p; omega) v)) (ih fun i u=> p _ (by omega))).mul (wider (hk n (by omega)) (p n (by omega))))
    congr 1; unfold gap; simp [← Bool.xor_assoc] -- orientation

lemma alone (p:lonely S (n+1)): Disjoint (S n) ((range n).biUnion S):= Finset.disjoint_left.mpr (fun i v h=> let ⟨j,u,t⟩:=mem_biUnion.mp h; Finset.disjoint_left.mp (p n (by omega) _ (mem_range.mp u)) v t)
lemma run_read (h:confined S F n c)(a:lonely S n) (t:Finset I): run F n t t= run (fun i=> F i t t) n := by
 induction n with
 | zero=> simp [run]
 | succ n ih=>
    let H:confined S F n c:= fun i t=>h i (by omega); rw [run_succ, run_succ, Sector.sliced (run_sector S F n c H) (h n (by omega)) (alone _ _ a).symm, ih H (fun i p=>a i (by omega))]
open Sector (grainB)
-- prefix multiplication; sugar for `Z₂`
lemma harvest (h:confined S F n c) (k:confined S G n d)(a:lonely S n) : run F n* run G n=
    grainB ((c 0).xor (c n)) (d 0) • run (fun i=>grainB (gap c i) (d i) • (F i*G i)) n:= by
 induction n with
 | zero=> simp [grainB,run]
 | succ n ih=>
    let g (i:ℕ):=grainB (gap c i) (d i) • (F i*G i); let U:=run g n
    have H:confined S F n c:=fun i t=> h i (by omega); have K:confined S G n d:=fun i t=> k i (by omega)
    have hg:= ih H K (fun i p=> a i (by omega)); have hk:= (h n (by omega)).apart (run_sector S G n d K) (alone S n a)
    change run F _*run G _= _ • run g _; rw [run_succ,run_succ,run_succ]; rw [←mul_assoc, mul_assoc (run F n), hk, Algebra.mul_smul_comm, ←mul_assoc (run F n),hg, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]; unfold g; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]; simp only [smul_smul,mul_assoc]; congr 1; unfold gap; cases (c 0) <;> cases (c n) <;> cases (c (n+1)) <;> cases (d 0)<;> cases (d n) <;> simp [grainB]
theorem run_mul (h:confined S F n c) (k:confined S G n d)(a:lonely S n)(v:c 0=c n) : run F n* run G n=run (fun i=>grainB (gap c i) (d i) • (F i*G i)) n:= by rw [harvest S F G n c d h k a,v,Bool.xor_self]; exact one_smul ..
lemma run_scale (f:ℕ→ℂ) : (run f n) • (run F n)=run (fun i=> f i • F i) n:= by
 induction n with
 | zero=> simp [run]
 | succ n ih=> rw [run_succ,run_succ,run_succ,←ih,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul]
end car
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.run_mul
