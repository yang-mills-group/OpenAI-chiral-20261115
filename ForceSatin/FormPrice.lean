import ForceSatin.HighFood
import ForceSatin.AffineFlow
/-! estimate with possibility of already selecting polynomial for each copy (off-Pose)
    with errors in that same global frame. Pure matter will use none. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Matrix Thera Verses Credential
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {I : Type}[LinearOrder I][Fintype I][Nonempty I]
variable {J : Type*}
-- C includes appropriate |z_i| and polynomial costs etc. signed means not required individually small.
def stack (m:ℕ)(D C W B:ℝ):ℝ:= (W*C*normalCost B m)^2 + C*(2*m*D*B^m)

omit [Nonempty I] in
lemma realResid (q x:Wave I) (A:FC I) :
    (inner ℂ x (acts A x)).re = (resid q x A).re+(reading q q A).re*‖x‖^2 := by
  change (inner ℂ x _).re=(inner ℂ x (acts A x) - inner ℂ x x * reading q q A).re + _
  rw [inner_self_eq_norm_sq_to_K,Complex.sub_re]; simp [Complex.mul_re,Complex.mul_im, sq]; ring

lemma single_form {q P} (V K:Shaft I)(p:IsStarProjection (P:Op I))(v:Sea P q)
    {C D B d:ℝ} (u:fiber V B)(e:fiber K B)(h:1≤B)(d0:0≤D)(hd:∀ i, ‖highLeg V i-highLeg K i‖≤ D)
    (m:ℕ)(S:Finset I) (A F:FC I) (ht:Credential S m C F) (hk:‖A-V.glow F‖≤d)
    (x:Wave I): (inner ℂ x (acts A x)).re ≤
     C*feedBill m B D (food S K P x) x+((reading q q (V.glow F)).re+d)*‖x‖^2 := by
  rw [← sub_add_cancel A (V.glow F),act_add, inner_add_right, Complex.add_re,realResid q (A:=V.glow F)] -- keep x?
  have hg:(resid q x (V.glow F)).re ≤ _:= (Complex.re_le_norm _).trans (feed q x ht p v u e h d0 hd)
  have hx:(inner ℂ x (acts (A-V.glow F) x)).re ≤ d*‖x‖^2:=by
    have hv:= read_price x x (A-V.glow F); rw [←sq] at hv
    exact (Complex.re_le_norm _).trans (le_trans hv (mul_le_mul_of_nonneg_right hk (sq_nonneg _)))
  linarith

theorem layout_form {q P} (V K:Shaft I)(p:IsStarProjection (P:Op I))(v:Sea P q)
    {C D B G W:ℝ} (u:fiber V B)(e:fiber K B)(h:1≤B)(d0:0≤D)(hd:∀ i, ‖highLeg V i-highLeg K i‖≤ D)
    (m:ℕ)(L:Finset J)(S:J→Finset I)(g:Set.PairwiseDisjoint (L:Set J) S)
    (A F:J→FC I)(d:J→ℝ)(hx:∀ i∈L, Credential (S i) m C (F i) ∧ ‖A i - V.glow (F i)‖ ≤ d i)
    (ht :(∑ i∈L, ((reading q q (V.glow (F i))).re+d i)) ≤ G)
    (_c0:0≤C)(w:‖K.sell‖≤W)(r:‖K.buy‖≤W)
    (x:Wave I) :
    ∑ i∈L,(inner ℂ x (acts (A i) x)).re ≤ active P x + (L.card*stack m D C W B+G)*‖x‖^2:=by
  let X(i:J):= food (S i) K P x; let b:= normalCost B m
  let n:ℝ:=L.card; let a:=active P x
  let Y(i):=(reading q q (V.glow (F i))).re+d i
  let T:=∑ i∈L,X i; let M:= (W*C*b)^2*n*‖x‖^2
  have hm: C*b*T*‖x‖ ≤ a+M := by
    have ht:= food_product K P p x W w r L S g
    change T^2≤ n*(4*W^2*a) at ht; let Z:= C*b*T*‖x‖
    have hf: Z^2 ≤ 4*M*a:=by
      have he:= mul_le_mul_of_nonneg_left ht (show 0≤ (C*b*‖x‖)^2 from sq_nonneg _); unfold Z M; nlinarith only [he]
    have h1:0≤M:=mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
    have hp:0≤ a:=active_pay p _; change Z≤a+M; nlinarith only [h1,hp,sq_nonneg (M-a),hf]
  let Z:= 2*m*D*B^m
  apply le_trans (sum_le_sum (s:=L) fun i hi=> single_form V K p v u e h d0 hd m (S i) _ _ (hx i hi).1 (hx i hi).2 x)
  simp_rw [feedBill,mul_add,sum_add_distrib]; rw [←mul_sum,←Finset.sum_mul,←Finset.mul_sum,sum_const,nsmul_eq_mul,←Finset.sum_mul]
  have hf:=mul_le_mul_of_nonneg_right ht (sq_nonneg ‖x‖)
  change C*(b*T*‖x‖)+ n*(C*(Z*‖x‖^2)) + (∑ i∈ L,Y i)*‖x‖^2 ≤ a + (n*_+_)*_
  change (∑ i∈ L,Y i)*_ ≤ G*‖x‖^2 at hf
  unfold stack; unfold Z; unfold M b at *; linarith

/-- Call from the checker layout (one scalar shift-test). Permit choosing for each `t`
    even new polynomials. Occupation purchases on *any* state, at these parameters. -/
structure Inspection [DecidableEq J] (P:Op I) (m:ℕ)(B D C W G:ℝ) (L:List J) (A:J→FC I) : Prop where
  existsBooks : ∃ (S:J→Finset I)(V K:Shaft I)(F:J→FC I)(d:J→ℝ)(q:Wave I),
      Sea P q ∧ Set.PairwiseDisjoint (L.toFinset:Set J) S ∧ fiber V B ∧ fiber K B ∧
      ‖K.sell‖ ≤ W ∧ ‖K.buy‖ ≤ W ∧ (∀ i, ‖highLeg V i-highLeg K i‖≤ D) ∧
      (∀ i∈L, Credential (S i) m C (F i) ∧ ‖A i - V.glow (F i)‖≤d i) ∧
      ∑ i∈L.toFinset, ((reading q q (V.glow (F i))).re+d i) ≤ G

theorem occupied_layout [DecidableEq J] {P:Op I}(T:Shaft I)(p:IsStarProjection P)(Φ:J→FC I)(L:List J)(v:L.Nodup)
    (w:∀ i∈L,∀ j∈L,Commute (Φ i) (Φ j))(m:ℕ) (B D C W G C':ℝ)
    (h:1≤B)(d0:0≤D)(hc:0≤C)(u:C'≤1/2)
    (H:∀ t∈Set.Icc (0:ℝ) 1, let K:=(tilt P t).foldC T;
      (∀ i∈L,‖K.glow (Φ i)‖ ≤ C') ∧ Inspection P m B D C W G L (fun i=> K.glow (Φ i)))
    (x:Wave I) :
    ‖acts (quant T.sell) (acts (affineProd Φ L 1) x)‖ ≤
          Real.exp ((L.length*stack m D C W B+G) + 2*C'^2*L.length)*‖advent P T 0 x‖:=by
  apply full_growth T p Φ L v w _ _ u _
  intro t hz K
  obtain ⟨z,⟨S,V,k,F,d,q,q0,hi,V',k',w,r,g,hm,he⟩⟩:= H t hz
  refine ⟨z,fun x=>?_⟩
  rw [←List.toFinset_card_of_nodup v]; exact layout_form V k p q0 V' k' h d0 g m _ S hi (fun i=> K.glow (Φ i)) F d (fun i a=>hm i (List.mem_toFinset.mp a)) he hc w r x

end YM.CF.Papyrus.Franc.SatinForce
