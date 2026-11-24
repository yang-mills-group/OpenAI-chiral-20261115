import YM.CF.Buffered.Spoke
/-! general cyclic stack table and Trotter power -/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice Reflect
open Sector (grainB)
open Fin.NatCast
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction
attribute [local instance] opCStarAlgebra
variable {B I J:Type*} [LinearOrder I][Fintype I] [LinearOrder J][Fintype J]
-- table of channel pairs for a slab. power multiplies with sign.
abbrev Board (I C:Type*) := C → C→ FC I
def bind (A:FC I) (p: B→Bool) (f g:B→FC I): Board I B:= fun i j=> A * (chord (p j) • (f i * g j))
lemma bind_cov {p:B→Bool} (U:UNI I) {A T:FC I} (h:T=theta U A) {f g r q : B→ FC I} (t:∀ i,r i=theta U (g i)) (u:∀ i,q i=theta U (f i)) (v:∀ i j,r i*q j=grainB (p i) (p j) • (q j*r i)) (x y : B) :
 theta U (bind A p f g x y)=star (chord ((p x).xor (p y))) • bind T p r q y x := by
  unfold bind; rw [theta_mul,theta_smul,theta_mul, ←u, ←t,←h,v,Algebra.mul_smul_comm,Algebra.mul_smul_comm,smul_smul, Algebra.mul_smul_comm,smul_smul]; congr 1; cases p x <;> cases p y <;> simp [grainB,chord]
lemma bind_local {p:B→Bool} {f g : B→ FC I} {A: FC I}{S : Finset I} (h:Sector S false A) (a x: B) (v: Sector S (p a) (f a)) (u:Sector S (p x) (g x)) : Sector S ((p a).xor (p x)) (bind A p f g a x) := by simpa [bind] using (h.mul ((v.mul u).scale (chord (p x))))
-- layer equality
section
variable [Nonempty B][Fintype B](n:ℕ) [NeZero n] (p:B→Bool)
def whole (F:ℕ→ Board I B) := ∑ t:Many n B, run (fun i=> F i (recur t i) (recur t (i+1))) n
theorem woven (u:2≤n)(f g : ℕ→B→FC I) (S : ℕ→Finset I) (A:ℕ→FC I) (h:lonely S n) (t:∀ i<n, Sector (S i) false (A i)) (v: f n=f 0) (a:∀ i<n,∀ x, Sector (S i) (p x) (f i x) ∧ Sector (S i) (p x) (g i x))
    (e:∀ x y,f 0 x*g 0 y=grainB (p x) (p y) • (g 0 y * f 0 x)) :
 run A n* run (fun i=>∑ x, outer n i (p x) • (g i x*f (i+1) x)) n = whole n (fun i=> bind (A i) p (f i) (g i)) := by
 rw [whole, run_map, ←Equiv.sum_comp rota,mul_sum] -- tune Binder
 rcases n with _ | n; · omega
 refine sum_congr rfl fun k _=> ?_
 simp_rw [rota_at]; let c(i:ℕ):=recur k i; let x(i):= f i (c i); let y(i):= g i (c (i+1)); let b:= p ∘ c; let G(i):=chord (b (i+1)) • (x i*y i); have he:c (n+1)=c 0:=recur_full ..
 have hz:∀ i≤n,Sector (S i) (b i) (x i):= fun i u=> (a i (by omega) _).1; have ht:∀ i≤n,Sector (S i) (b (i+1)) (y i):= fun i u=> (a i (by omega) _).2
 change run A (n+1)* run (fun i=>outer (n+1) i (b (i+1)) • (y i*x (i+1))) (n+1)= run (fun i=> A i * G i) _
 have hw: confined S A (n+1) (fun _=>false):= fun i h=> t i h
 rw [belt S x y b n (by omega) (by unfold b; simp [he]) hz ht (by unfold x; rw [he, v]) (e ..) h, run_mul S A G _ _ _ hw (show confined S G (n+1) b from fun i h=> ((hz i (by omega)).mul (ht i (by omega))).scale _) h rfl]
 simp [grainB,gap]
end
abbrev Tablet(C:Type*) (n:ℕ) := Many n C
def parity (p:B→Bool) (n:ℕ) : Tablet B n→ Bool := match n with
 | 0=> fun _=>false
 | n+1=>fun i=> (p (i 0)).xor (parity p n (Fin.tail i))
variable (p:B→Bool) (F:Board I B)
def issue (F:Board I B) (n:ℕ) : Board I (Tablet B n) := match n with
 | 0 => fun _ _=> 1
 | n+1=> fun i j=> grainB ((p (i 0)).xor (p (j 0))) (parity p n (Fin.tail i)) • (F (i 0) (j 0)* issue F n (Fin.tail i) (Fin.tail j))
lemma issue_here {S : Finset I} (p0:∀ i j, Sector S ((p i).xor (p j)) (F i j)) (n:ℕ)(x y:Tablet B n) : Sector S ((parity p n x).xor (parity p n y)) (issue p F n x y) := by
 induction n with
 | zero=> exact Sector.one
 | succ n ih=>
   rw [issue]; apply Eq.mp _ (((p0 (x 0) (y 0)).mul (ih (Fin.tail x) (Fin.tail y))).scale (grainB ((p (x 0)).xor (p (y 0))) (parity p n (Fin.tail x))))
   dsimp only; congr 1; simp only [parity]; cases p (y 0) <;> cases p (x 0) <;> simp
lemma prism (U:UNI I) {G:Board I B}(t:∀ i j, theta U (F i j) = star (chord ((p i).xor (p j))) • G j i) (n:ℕ)(x y:Tablet B n) : theta U (issue p F n x y)= star (chord ((parity p n x).xor (parity p n y))) • issue p G n y x := by
 induction n with
 | zero=> simp [issue,parity,chord,theta_one]
 | succ n ih=>
   rw [issue,issue,theta_smul,theta_mul,t,ih,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; simp only [smul_smul]; congr 1
   simp only [parity]; cases p (x 0) <;> cases p (y 0) <;> cases parity p n (Fin.tail x) <;> cases parity p n (Fin.tail y) <;> simp [grainB,chord]
section many
variable (n:ℕ)[NeZero n][Fintype B]
private def pairTable (k n:ℕ):Many n (Tablet B (k+1)) ≃ (Many n B × Many n (Tablet B k)) where
 toFun x := (fun i=> x i 0,fun i j=> x i j.succ)
 invFun x i:= Fin.cons (x.1 i) (x.2 i)
 left_inv x := funext fun i=> funext fun j=> by induction j using Fin.cases <;> simp
 right_inv x:= Prod.ext (by funext i; simp only; rw [Fin.cons_zero]) (by funext i j; simp)
variable (K:ℕ→Board I B)(S:ℕ→Finset I)(h: ∀ i<n,∀ x y,Sector (S i) ((p x).xor (p y)) (K i x y)) (g:lonely S n)
include h g
theorem whole_power (k:ℕ) : whole n K ^ k = whole n (fun i=> issue p (K i) k):= by
 induction k with
 | zero=> unfold whole; simp [pow_zero,issue,Stack.run_one]
 | succ k ih=>
   rw [pow_succ',ih,whole,whole,whole,←Equiv.sum_comp (pairTable (B:=B) k n).symm,Fintype.sum_prod_type, sum_mul]; refine sum_congr rfl fun a _=> ?_; rw [mul_sum]; refine sum_congr rfl fun b _=> ?_
   let A(i:ℕ):= K i (recur a i) (recur a (i+1)); let B'(i:ℕ):= issue p (K i) k (recur b i) (recur b (i+1))
   rw [run_mul S A B' n (p ∘ recur a) ((parity p k) ∘ recur b) (fun i v=> h i v _ _) (fun i v=> issue_here _ _ (h i v) _ _ _) g (congrArg p (recur_full a).symm)]
   refine run_congr _ _ _ fun i _=> ?_; unfold issue A B'; simp [pairTable,Fin.tail,recur,gap]

-- sandwich with mark at bra and pair term at END
lemma whole_mark (F G : ℕ→ FC I)(f:confined S F n (fun _=>false))(u:confined S G n (fun _=>false))(l: Finset I) :
  (run F n * whole n K * run G n) l l=
   ∑ a:Many n B, ∏ i:Fin n,(F i.val*K i.val (a i) (a (i+1))*G i.val) l l := by
 unfold whole; rw [mul_sum,sum_mul,Matrix.sum_apply]; refine sum_congr rfl fun i _=>?_ ; let t(j:ℕ) := K j (recur i j) (recur i (j+1)); let c := p ∘ recur i
 have hu : confined S t n c:=fun i u=>h i u _ _; let q(j:ℕ):= F j *t j; have hq:confined S q n c:= by intro i v; simpa [q,gap] using (f i v).mul (hu i v)
 have hx := congrArg p (recur_full i).symm; have he:run F n* run t n=run q n:=by rw [run_mul S F t n (fun _=>false) c f hu g rfl]; simp [grainB,q,gap]
 have hd:run q n* run G n=run (fun i=> q i*G i) n:=by rw [run_mul S q G n c _ hq u g hx]; simp only [grainB,Bool.and_false,Bool.false_eq_true, ↓reduceIte, one_smul]
 rw [he,hd,run_read S _ n c (fun i v=> by simpa [gap] using (hq i v).mul (u i v)) g,run_prod]; refine prod_congr rfl fun j _=>?_; unfold q t; rw [recur_of,recur,Nat.cast_add,Nat.cast_one,Fin.cast_val_eq_self] -- tune cast
end many
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.whole_mark
#print axioms YM.CF.Buffered.Stack.whole_power
