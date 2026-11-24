import YM.CF.BPress.Spin.Blank
import YM.CF.BPress.Bands
import Mathlib.Algebra.Order.Chebyshev
/-! Length of dark vacuum conditioning, temporal Poincare. Start at selected fermion node only. Witness budgets use D, *not* D_P (the marked length). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset NormedSpace Lattice Fock SU Lat Fir Cube Tenant Branch Tulip Scroll Dial Rush Nacre Pledge Quad Blank
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra

variable {N:Side}{B:BandWidth}
-- Eligible vacancy S does not include any node in marked bands.
structure Dark (Y:Bands (More N) B) (P:Support N) : Prop where
 out (x) (h:x∈P) (i:Y.Index): node x ∉ Y.band i
namespace Stride
variable (A:Bands (More N) B)
def fw (N:Side)(n:ℕ):Equiv.Perm (Site N):= Equiv.addRight (n • step 0)
lemma exit (e:1 ≤ B.marked.val) (u:Site N)(p:∀ i:A.Index,node u∉ A.band i): ∃ n:ℕ,n≤ B.D ∧ ∃ i:A.Index,node (fw N n u)∈A.band i:=by
 obtain ⟨i,v⟩:= A.cover (node u); obtain ⟨a,h,t⟩:=arc_cases _ _ _ (v.resolve_left (p i)); have he:node u 0=A.stop i+ ↑a:= congrFun t 0; let d:=B.D-a; let n:=(d+1)/2; have ht:d≤2*n:=by unfold n; omega
 have hl:a+d=B.D:=by unfold d; omega
 have hy:a+2*n≥B.D ∧ a+2*n≤B.D+B.marked.val:=by unfold n; omega
 let w:=a+2*n-B.D; have hh:w≤B.marked.val:=by unfold w; omega
 have hs (k:ℕ): node (fw N k u) 0=node u 0+ 2 * k:=by
    induction k with|zero=>simp [fw];|succ k ih=>rw [show fw N (k+1) u=fw N k u+step 0 from by simp [fw, add_smul, add_assoc],Cube.after]; simp only [Pi.add_apply, step_apply,ite_true,ih,Nat.cast_succ]; ring
 refine ⟨n, by unfold n; have h₁:= B.D_pos; omega,i+1,?_⟩; rw [Bands.band,arc_mem,hs n,he,show (A.stop i+↑a)+2*(n:Per (More N))=A.start (i+1)+w from ?_,depth_eq _ ((hh.trans_lt B.marked_lt).trans A.full_lt)]; exact hh
 rw [←A.stop_next i, add_assoc,add_assoc,←Nat.cast_add,←Nat.cast_ofNat (R:=Per (More N)) (n:=2), ← Nat.cast_mul,←Nat.cast_add]; rw [show a+2*n=B.D+w from (by unfold w; omega)] -- tune

-- modes
variable (N)
def punch(n:ℕ): Equiv.Perm (Single N):= Equiv.prodCongr (Equiv.prodCongr (fw N n) (Equiv.refl _)) (Equiv.refl _)
variable {N}
def sign(x:Single N):= Rush.wind x.1.1 Blank.isi
lemma punch_one (x y:Single N): Blank.advanceW N x y=if punch N 1 x=y then sign x else 0:=by
 rcases x with ⟨⟨x,i⟩,t⟩; rcases y with ⟨⟨y,j⟩,u⟩; unfold advanceW scalarP; simp only [Matrix.kroneckerMap_apply,wagon_app, Blank.isi,wrap_step]; by_cases h:x+step 0=y <;> by_cases hz:i=j<;> by_cases hs:t=u<;> simp [h,hz,hs,punch,fw,sign,Matrix.one_apply,Blank.isi]
lemma advance_pay (v:Ket (Single N))(x) : (acts (Blank.advanceW N) v).ofLp x= sign x*v.ofLp (punch N 1 x):=by rw [act_at,Matrix.mulVec,dotProduct]; simp [punch_one]
lemma punch_s (i:Single N)(n:ℕ): punch N n (punch N 1 i)= punch N (n+1) i:=by rcases i with ⟨⟨i,x⟩,b⟩; simp [punch,fw, add_smul,add_right_comm]; abel

-- telescoping; don't iterate Select, only need evaluation at final n
lemma bounds (v: Ket (Single N))(i:Single N)(n:ℕ) : let y:= acts (Blank.deltaX N) v; ‖v.ofLp i‖≤ ‖v.ofLp (punch N n i)‖+ ∑ j∈ range n, ‖y.ofLp (punch N j i)‖:=by
 intro y; induction n generalizing i with
 | zero=> simp [punch,fw]
 | succ n ih=>
   let x:=punch N 1 i; have he:= ih x; have hp : ‖v.ofLp i‖≤‖v.ofLp x‖+ ‖y.ofLp i‖:=by
      unfold y Blank.deltaX; rw [act_sub,act_one,WithLp.ofLp_sub,Pi.sub_apply,advance_pay]; apply (norm_le_norm_sub_add _ (sign i * v.ofLp (punch N 1 i))).trans_eq; rw [norm_mul, show ‖sign i‖=1 from fee_norm _,one_mul, add_comm]; -- tune
   apply le_trans hp ((add_le_add he le_rfl).trans_eq ?_); unfold x; rw [punch_s]; simp_rw [punch_s]; rw [sum_range_succ',add_assoc]; simp [punch,fw] -- tune range_succ'
variable {P:Support N}
def Locks (S:Support N)(u:Bool): Finset (Single N):= (tenureX N u).filter fun i=> i.1.1∈ S
def Lock (S:Support N)(u: Bool):=cutM (Locks S u)
lemma Δ_bound (h:Dark A P)(u:Bool)(v:Ket (Single N)): let x:= acts (Lock P u) v; let d:=B.D; ‖x‖^2 ≤ (d:ℝ)^2 * ‖acts (Blank.deltaX N) x‖^2:=by
 intro x d; let y:=acts (Blank.deltaX N) x; let f(n:ℕ)(i:Single N):= ‖y.ofLp (punch N n i)‖^2
 have he (i:Single N) : ‖x.ofLp i‖^2 ≤ (d:ℝ) * ∑ n∈range d, f n i:=by
    have hs(k:Single N) (t:k∉Locks P u):x.ofLp k=0:= by unfold x Lock; rw [cut_apply,if_neg t]
    by_cases l:i∈Locks P u; swap; · rw [hs i l,norm_zero,zero_pow (by decide)]; unfold f; positivity
    obtain ⟨n,hn,j,hj⟩:=exit A B.marked.property i.1.1 (h.out _ (mem_filter.mp l).2); have hv:(punch N n i)∉Locks P u:=fun k=> h.out _ (mem_filter.mp k).2 j hj
    have hx:=bounds x i n; dsimp only at hx; rw [hs _ hv,norm_zero,zero_add] at hx
    apply (pow_le_pow_left₀ (norm_nonneg _) (hx.trans (sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun _ _ _=>norm_nonneg _))) 2).trans; unfold f
    simpa only [card_range] using sq_sum_le_card_mul_sum_sq (s:=range d) (f:=fun j=> ‖y.ofLp (punch N j i)‖)
 calc
   _ = _:= EuclideanSpace.norm_sq_eq _
   _ ≤ _:= sum_le_sum (fun i _=> he i)
   _ = _:= by
    rw [←mul_sum,sum_comm]; have hg(n):∑ i:Single N,f n i=‖y‖^2:=by rw [EuclideanSpace.norm_sq_eq]; exact Equiv.sum_comp (punch N n) (fun i=> ‖y.ofLp i‖^2)
    simp_rw [hg]; rw [sum_const,nsmul_eq_mul,card_range]; unfold y; ring
end Stride
end YM.CF.BPress.Spin
