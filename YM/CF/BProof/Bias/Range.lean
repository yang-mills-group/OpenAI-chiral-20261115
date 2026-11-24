import YM.CF.BProof.Stint.Global
import YM.CF.BProof.Circle
/-! Temporal slices in B-bias exhaustion (finite tori, any admissible). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Stint Lattice Cube
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I][DecidableEq I](F:I→Per N){r t:ℕ}{A B:Op I}
-- reader for a temporal band projection
def timeR (S:Finset (Per N)): Op I:= cutM (univ.filter fun i=> F i∈S)
lemma timeR_proj(S):IsStarProjection (timeR F S):= cutM_idp _
@[simp] lemma timeR_cut(S):cc (timeR F S)=timeR F S:=by unfold timeR; exact by rw [cc,(cutM_idp _).isSelfAdjoint]; unfold cutM; simp
lemma timeL(S)(A:Op I)(i j): (timeR F S *A) i j = if F i∈S then A i j else 0:=by simp only [timeR,cutM,Matrix.diagonal_mul]; simp [ite_mul]
lemma timeS(S)(A:Op I)(i j): (A*timeR F S) i j= if F j∈S then A i j else 0:=by simp only [timeR,cutM,Matrix.mul_diagonal]; simp [mul_ite]
lemma time_cut(A:Finset (Per N))(S:Finset I):Commute (timeR F A) (cutM S):= by unfold timeR cutM Commute SemiconjBy; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext i; rw [mul_comm]
lemma time_sub {S T:Finset (Per N)}(h:S⊆T):timeR F T *timeR F S = timeR F S:=by ext i j; rw [timeL]; split; rfl; rename_i g; rw [← mul_one (timeR F S),timeL,if_neg (fun t=>g (h t))] -- tune
abbrev slice (k:Per N):= timeR F {k}

def Span (r:ℕ)(A:Op I): Prop:= ∀ i j, r<delta1 N (F i) (F j)→ A i j=0
variable {F}
lemma Span.up(h:Span F r A)(e:r≤t):Span F t A:= fun i j t=>h i j (e.trans_lt t)
lemma plusP(h:Span F r A)(p:Span F r B):Span F r (A+B):= by intro i j g; simp [h _ _ g,p _ _ g]
lemma subP(h:Span F r A)(p:Span F r B):Span F r (A-B):= by intro i j g; simp [h _ _ g,p _ _ g]
lemma span_star(h:Span F r A):Span F r (star A):= fun i j g=>by change star (A j i)=_; rw [h _ _ (by rwa [d_sym]),star_zero]
lemma span_mul(h: Span F r A)(p:Span F t B):Span F (r+t) (A*B):=by
 intro i j g; rw [Matrix.mul_apply]; apply sum_eq_zero; intro d _; by_cases s:r <delta1 N (F i) (F d); rw [h _ _ s,zero_mul]; exact mul_eq_zero_of_right _ (p _ _ (by grind [d_one_triangle (F i) (F d) (F j)])) -- tune
variable (F)
lemma span_one : Span F r 1:=by intro i j h; by_cases g:i=j; rw [g,d_id] at h; omega; exact Matrix.one_apply_ne g
lemma span_zero: Span F r 0:= by intro i j h; rfl
lemma span_cut(S:Finset I):Span F r (cutM S):=by intro i j h; by_cases g:i=j; rw [g,d_id] at h; omega; simp [cutM,g]
variable {F}
lemma Span.comm (h:Span F 0 A)(S):Commute (timeR F S) A:= by
 unfold Commute SemiconjBy; ext i j; rw [timeS,timeL]; by_cases g: F i=F j; rw [g]; rw [h _ _ (Nat.pos_of_ne_zero (fun t=> g (d_equal _ _ t)))]; simp
lemma Span.comm_iff (A:Op I) : Span F 0 A ↔ ∀ s:Per N, Commute (slice F s) A:=by
 refine ⟨fun h s=>h.comm _, fun g i j h=>?_⟩; have ht:= Matrix.ext_iff.mpr (g (F i)).eq i j; rw [timeL,timeS,if_pos (mem_singleton_self _)] at ht; exact ht.trans (if_neg (fun t=>by rw [mem_singleton.mp t,d_id] at h; omega))
variable (F)
def cent (x:Per N)(r:ℕ): Finset (Per N):= univ.filter fun i=> delta1 N i x ≤ r
@[simp] lemma cent_at(x y:Per N): x∈ cent y r ↔ delta1 N x y ≤ r:=by simp [cent]
variable {F}
lemma Span.atB(h:Span F r A)(s:Per N): timeR F (cent s r) * A * slice F s = A*slice F s:=by
 ext i j; rw [timeS,timeS,timeL]; split; next t=> rw [←mem_singleton.mp t]; split; rfl; rename_i g; exact (h i j (lt_of_not_ge fun q=>g ((cent_at ..).2 q))).symm
 rfl -- tune
end YM.CF.BProof.Bias
