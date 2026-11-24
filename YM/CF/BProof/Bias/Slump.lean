import YM.CF.BProof.Bias.Jump
import YM.CF.BProof.Hearth.Hoard
import YM.CF.BProof.Wick.Cliff
/-! Approximate splitting follows from small D_C close to the gap. Color amplification
 here works on ALL Spin slots (Δ not invertible). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (A B:Stamp){r:ℝ}{N:Side}{j:ℕ}
abbrev curtain(N:Side)(A:Stamp):= joint (N:=N) (fun _=>A)
abbrev drum(N:Side)(A:Stamp):= pair (N:=N) (fun _=>A)
lemma curtain_mul : curtain N A*curtain N B=curtain N (A*B):= joint_mul ..
lemma curtain_tile : Commute (curtain N A) (Spin.tile N):= (tile_joint ..).symm
lemma curtain_p (U: Finset (Per N))(u:Bool): Commute (curtain N A) (bandCut (rowsX U) u):=by
 ext i j; rw [bandCut,cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; unfold curtain joint; simp only [jump_apply]; by_cases h:i.1=j.1 <;> simp_all [mem_band]
lemma curtain_seat (U:Finset (Per N)): Commute (curtain N A) (Seat U):=by
 apply Commute.symm; apply Span.comm (F:=ht); intro k l g; have he:k.1≠l.1:= fun t=>by unfold ht fsite at g; rw [t,d_id] at g; omega
 simp [curtain,joint,jump_apply,he]
lemma pair_seat (S: Finset (Per N))(X:Quilt N) : Commute (Seat S) (pair X):=by
 apply (Span.comm (F:=ht)); intro i j h; rw [pair_local]; exact if_neg (fun k=> Nat.lt_irrefl 0 (show 0< 0 from (show delta1 N (ht i) (ht j)=0 from (show ht i=ht j from congrFun k 0) ▸ d_id _) ▸ h)) -- tune
lemma curtain_norm : ‖curtain N A‖≤‖A‖:= jump_bound _ _ (norm_nonneg _) (fun _=>le_rfl)
lemma curtain_sum (F:Slot→Stamp): ∑ i,curtain N (F i)=curtain N (∑ i,F i):=by ext i j; unfold curtain joint; by_cases h:i.1=j.1<;> simp [Matrix.sum_apply,jump_apply,h]
lemma curOne : curtain N 1=1:=jump_id -- tune
lemma curtain_relic (F: Globe N): Commute (curtain N A) (relic F):=by
 let T:= spinJ; unfold curtain joint; rw [jump_replicate]; unfold Commute SemiconjBy relic liftA; rw [op_kron_mul,op_kron_mul,mul_one,mul_one,one_mul,one_mul]
-- produces amplifier K
lemma affair (h:A≠0):∃ s:ℝ, 0<s ∧ ∀ {N:Side} {P:Op (Single N)}, (∀ U:Stamp, Commute (curtain N U) P) → ‖P‖≤ s* ‖P*drum N A‖:= by
 obtain ⟨i,l,H⟩:∃ i l,A i l≠0:= by by_contra! v; apply h; ext i j; exact v ..
 let U(x:Slot): Stamp:= Matrix.single x i 1; let Z(x:Slot):Stamp:= Matrix.single l x (A i l)⁻¹; have he:∑ x:Slot,U x*A*Z x= 1:=by
    unfold U Z; simp_rw [Matrix.single_mul_mul_single,one_mul,mul_inv_cancel₀ H]; ext t u; by_cases h:t=u<;>simp [Matrix.sum_apply,Matrix.single,Matrix.one_apply,h]
 let s:=∑ i:Slot, ‖U i‖*‖Z i‖; refine ⟨s+1, (by unfold s; positivity),?_⟩; intro N P p; let V:UNI (Single N):=⟨Spin.tile N,tile_unit N⟩; let x:=(P*drum N A); let W:=curtain N
 rw [← CStarRing.norm_mul_coe_unitary P V]; rw [show P*V.val=∑ i:Slot,W (U i)*x*W (Z i) from ?_]; swap
 · have h1(i): W (U i)*x*W (Z i)= (P*V.val)*W (U i*A*Z i):=by unfold x drum pair; change W (U i) * (P*(V.val*W A))*W (Z i)=_; rw [←mul_assoc _ P,(p ..).eq,mul_assoc P,←mul_assoc _ V.val, (curtain_tile ..).eq]; simp_rw [mul_assoc, show W=curtain N from rfl]; -- tune
                                                                              rw [curtain_mul,curtain_mul]
   simp_rw [h1]; rw [←Matrix.mul_sum]; unfold W; rw [curtain_sum,he,curOne,mul_one]
 apply (norm_sum_le ..).trans (le_trans (b:=∑ i:Slot,(‖U i‖*‖Z i‖)*‖x‖) (sum_le_sum fun i _=>?_) ?_); · rw [←sum_mul,add_mul,one_mul]; exact le_add_of_nonneg_right (norm_nonneg _)
 rw [mul_right_comm]; exact le_trans (norm_mul_le ..) (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (curtain_norm _) (norm_nonneg _))) (curtain_norm _) (norm_nonneg _) (by positivity))
end YM.CF.BProof.Bias
