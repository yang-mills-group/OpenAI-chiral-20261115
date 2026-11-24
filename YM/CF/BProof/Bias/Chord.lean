import YM.CF.BProof.Bias.Recur
import YM.CF.BProof.Bias.Wing
/-! Avoid interpolating Laurent polynomials in Lean via modulation continuity.
In dimension one this proves the desired obstruction for the whole window of
cross-entry tests in place of the pointwise jump proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{N:Side}(w:ℂ)
abbrev pitch (x:Per N):= w^x.val
variable (h:w^N.val=1)(g:‖w‖=1)
include h
lemma pitched (n:ℕ): pitch w (n:Per N)=w^n:=by
 unfold pitch; rw [ZMod.val_natCast]; nth_rw 2 [← Nat.mod_add_div n N.val]; rw [pow_add,pow_mul,h,one_pow,mul_one]
lemma pitched_add (p q:Per N):pitch w (p+q)=pitch w p*pitch w q:=by
 conv_lhs => rw [← ZMod.natCast_zmod_val p,← ZMod.natCast_zmod_val q,← Nat.cast_add]; -- may nested rw
 rw [pitched w h,pow_add]
omit h
include g
lemma pitch_n (p:Per N): ‖pitch w p‖=1:=by simp [pitch,g]
lemma pitch_paid(n:ℕ) : ‖w^n-1‖ ≤ n*‖w-1‖:=by
 induction n with
 | zero=>simp
 | succ n ih=>
   push_cast; rw [show w^(n+1)-1=(w^n-1)*w+(w-1) from (by rw [pow_succ]; ring)]; apply (norm_add_le ..).trans; rw [norm_mul,g,mul_one,add_mul,one_mul]; gcongr
include h
lemma pitch_bill{r:ℕ}(p:Per N)(k:p∈cent 0 r): ‖pitch w p-1‖ ≤ r * ‖w-1‖:=by
 let n:=p.valMinAbs; have hv : n.natAbs≤r:=by have ht:=(cent_at ..).mp k; simpa only [delta1,sub_zero] using ht
 apply (le_trans (b:=(n.natAbs:ℝ)*‖w-1‖) ?_ (by gcongr)); have hp:=ZMod.coe_valMinAbs p
 by_cases f:0≤ n
 · rw [show p=((n.natAbs:ℕ): Per N) from (by rw [← Int.cast_natCast,Int.natAbs_of_nonneg f,hp]),pitched w h]; exact pitch_paid w g _ -- tune
 have he:pitch w (-p)*pitch w p=1:=by rw [← pitched_add w h]; simp [pitch]
 have hz:pitch w p-1=(1-pitch w (-p))*pitch w p:=by rw [sub_mul,one_mul,he]
 rw [hz,norm_mul,pitch_n w g,mul_one,norm_sub_rev]; rw [show -p=((n.natAbs:ℕ):Per N) from ?_,pitched w h]; exact pitch_paid w g _
 rw [← Int.cast_natCast,show (n.natAbs:ℤ)= -n from by omega,Int.cast_neg,hp] -- tune
omit h
variable (F:I→Per N)
def twang : UNI I:=⟨(Matrix.diagonal fun x=> pitch w (F x)),by
  let A(x):=pitch w (F x); constructor; all_goals rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]; congr 1; ext i; first | exact (mul_comm _ _).trans (scale_unit_self (pitch_n w g _)) | exact scale_unit_self (pitch_n w g _)
  ⟩ -- name
include h
lemma sway (A:Op I)(k:Per N): swipe F k A * (twang w g F).val=pitch w k • ((twang w g F).val *swipe F k A):=by
 ext i j; simp only [twang,Matrix.smul_apply,Matrix.mul_diagonal, Matrix.diagonal_mul,swiped]; split; next v=> rw [show pitch w (F j)=pitch w k * pitch w (F i) from (by rw [← pitched_add w h,k |> (fun _=> v),sub_add_cancel])]; rw [smul_eq_mul]; ring
 simp
abbrev wiggle (U:UNI I)(A:Op I) := A*U.val-U.val*A
lemma rigidity {A:Op I}{r:ℕ}(u: Span F r A): ‖wiggle (twang w g F) A‖ ≤ revCost r * (r * ‖w-1‖ * ‖A‖):=by
 let U:=twang w g F; let K:=revCost r; let V:= (cent (0:Per N) r); change ‖wiggle U A‖ ≤_; rw [show wiggle U A=∑ k∈V, wiggle U (swipe F k A) from (by unfold wiggle; rw [sum_sub_distrib,←Matrix.sum_mul,←Matrix.mul_sum,u.swipe])]; apply slice_limit (wiggle U) subset_rfl (by positivity); intro i e; let Y:=swipe F i A; rw [wiggle,sway w h g F A i,show _-_=(pitch w i -1) • (U.val*Y) from (by rw [sub_smul,one_smul])]; rw [norm_smul,CStarRing.norm_coe_unitary_mul]; exact mul_le_mul (pitch_bill w h g i e) (swipe_bill ..) (norm_nonneg _) (by positivity)
lemma near_w {d v:ℝ}{A:Op I}{r:ℕ}(x: Near F r d A)(he:‖A‖≤v): ‖wiggle (twang w g F) A‖ ≤ 2*d+revCost r*(r*‖w-1‖*(v+d)):=by
 obtain ⟨B,u,hB⟩:=x; let U:=twang w g F; let t(C:Op I):= wiggle U C; rw [show wiggle U A=t (A-B)+t B from (by unfold t wiggle; noncomm_ring)]; apply le_trans (norm_add_le ..) (add_le_add ?_ ?_)
 · unfold t wiggle; apply (norm_sub_le ..).trans; rw [CStarRing.norm_coe_unitary_mul,CStarRing.norm_mul_coe_unitary,two_mul]; exact add_le_add hB hB
 apply (rigidity w h g F u).trans; have he': ‖B‖≤ v+d:=by apply (norm_le_norm_sub_add B A).trans; rw [add_comm,norm_sub_rev]; exact add_le_add he hB
 unfold revCost; gcongr
end YM.CF.BProof.Bias
