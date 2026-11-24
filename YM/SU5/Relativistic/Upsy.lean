import YM.SU5.Relativistic.Ebull
import YM.SU5.Relativistic.Elast
/-! # reflection on tilted fixture. Particle-hole. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Finset Thera BProof.Align BProof.Wick BProof.Garden Pea
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I] (U V:UNI I) (Q:Shaft I){A:Pea I}
namespace Pea
variable (A)
def face:Pea I where
 fill:=twist U A.pour
 pour:=twist U A.fill
 leg:=by rw [←map_mul,A.lic,map_zero]
 home:=⟨(by unfold IsIdempotentElem; rw [←map_mul,A.water.isIdempotentElem.eq]),(by unfold IsSelfAdjoint; rw [←map_star,A.water.isSelfAdjoint])⟩
 water:=⟨(by unfold IsIdempotentElem; rw [←map_mul,A.home.isIdempotentElem.eq]),(by unfold IsSelfAdjoint; rw [←map_star,A.home.isSelfAdjoint])⟩
lemma face_robe : twist U A.robe=(A.face U).robe:=by unfold Pea.face Pea.robe; rw [map_add,add_comm]
lemma face_step : (A.face U).face (star U)=A:= by
 cases A; unfold face; congr 1; apply twist_inv; apply twist_inv
lemma posture (P:Op I) : (A.face U).leak (1-twist U P)= A.leak P:=by
 unfold leak frost face; simp only [sub_sub_cancel]; rw [←map_one (twist U),←map_sub, ←map_mul,←map_mul,←map_add, trace_twist, add_comm,map_one]
private abbrev gr (z:ℂ)(F:FC I) := F+ z • (1-F)
local notation "z"=> (2⁻¹:ℂ)
-- prove turning of grab via singleton and merge
private lemma gr_piece(s r t v:Finset I) (h:Disjoint s r)(k:Disjoint t v): grab (s∪r) (t∪v) z=grab s t z*grab r v z:=by
 unfold grab; rw [Matrix.diagonal_mul_diagonal]; apply congrArg; funext i
 have he{S T:Finset I}(h:Disjoint S T): (i∩(S∪T)).card=(i∩S).card+(i∩T).card:=by rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint (Disjoint.mono inter_subset_right inter_subset_right h)] -- name
 rw [he h,he k,Finset.card_union_of_disjoint h]; rw [←pow_add]; congr 1; have hh:=(card_le_card (show i∩s⊆s from inter_subset_right)); have ht:=card_le_card (show i∩r⊆r from inter_subset_right); omega
private lemma gr_up(i:I): grab {i} ∅ z=gr z (put i*takeF i):=by
 rw [←capOne i]; unfold gr grab cabin cutM; ext a b; by_cases p:a=b; subst b; by_cases h:i∈a <;> simp [*,inter_eq_right.mpr]; simp [p] -- tuner
private lemma gr_down(i:I): grab ∅ {i} z=gr z (takeF i*put i):=by
 rw [←capZero i]; unfold gr grab cabin cutM; ext a b; by_cases p:a=b; subst b; by_cases h:i∈a <;> simp [*,inter_eq_right.mpr]; simp [p]
-- turned momentum literal through quaternion
private lemma theta_token (s t:Finset I) : theta U (twist (quantU V) (grab s t z))=twist (quantU (U*V)) (grab t s z):=by
 let L:=twist (quantU V); let R:=twist (quantU (U*V)); have hp(i:FC I):theta U (L (gr z i))=gr z (theta U (L i)):=by unfold L gr; simp only [map_add,map_sub,twist_scalar,map_one,theta_add,theta_smul,theta_sub, theta_one]; norm_num
 have hu(i:FC I): R (gr z i)=gr z (R i):=by unfold R gr; rw [map_add,twist_scalar,map_sub,map_one]
 have hl(i:I):theta U (L (put i*takeF i))=R (takeF i*put i):=by
    unfold L R; rw [map_mul,map_mul,theta_mul,←create_put, ←remove_take, twist_create,twist_create,twist_remove,twist_remove,theta_upV,theta_downV, ←act_mul]; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul]; simp
 have hm(i:I): theta U (L (takeF i*put i))=R (put i*takeF i):=by
    have he:= mixed i i; rw [if_pos rfl] at he; rw [eq_sub_of_add_eq he]; change theta U (L (1-_)) = _; rw [map_sub,map_one,theta_sub,theta_one,hl]; nth_rw 1 [←map_one R]; rw [←map_sub, ←he]; abel -- tune
 induction s using Finset.induction_on with
 | empty =>
   induction t using Finset.induction_on with
   | empty=> rw [show grab (∅:Finset I) ∅ z=1 from (by unfold grab; simp)]; rw [map_one,map_one,theta_one]
   | insert i t p ih=>
     rw [←singleton_union]; nth_rw 1 [← empty_union (∅:Finset I)]; rw [gr_piece _ _ _ _ (by simp) (by simpa),map_mul,theta_mul]; nth_rw 3 [← empty_union (∅: Finset I)] -- tune
     rw [ih,gr_piece _ _ _ _ (by simpa) (by simp),map_mul,gr_up,gr_down, hp, hm,←hu] -- tune
 | insert i s p ih=>
   rw [←singleton_union]; nth_rw 1 [← empty_union t]; rw [gr_piece _ _ _ _ (by simpa) (by simp),map_mul,theta_mul, ih]; nth_rw 2 [← empty_union t]
   rw [gr_piece _ _ _ _ (by simp) (by simpa),map_mul,gr_up,gr_down,hp,hl,←hu]
lemma theta_hat : theta U A.hat=(A.face U).hat:=by
 obtain ⟨V,s,t,p,q,h⟩:=A.laid
 rw [A.own _ _ _ p q h,theta_token]; symm; exact (A.face U).own _ _ _ (by unfold face; dsimp only; rw [q,twin]) (by unfold face; dsimp only; rw [p,twin]) h.symm
end Pea
-- charge glow crosses θ for sectors
variable {C:FC I}{a:Bool}
lemma glow_theta (V: Shaft I){s: Finset I}(p: twist U Q.sell=star V.buy)(h: Sector s a C): theta U (Q.glow C)=V.glow (theta U C):=by
 have hx:twist U (star Q.buy)= V.sell:=by
    have he:twist U Q.buy=star V.sell:=by
       have h:(star V.buy)*twist U Q.buy=1:=by rw [←p,←map_mul,Q.payment,map_one]
       have hh:star V.sell * (star V.buy)=1:=by rw [←star_mul,V.pay,star_one]
       nth_rw 1 [←one_mul (twist U Q.buy)]; rw [←hh,mul_assoc,h,mul_one]
    rw [map_star,he,star_star]
 induction h with
 | zero=>rw [Q.glow_zero,theta_zero,V.glow_zero]
 | one=>rw [Q.glow_nil,theta_one,V.glow_nil]
 | up i h=>rw [←create_put,Q.glow_up,theta_upV,theta_upV,V.glow_free, V.glow_down,←p,←act_mul,←act_mul,twist_product]
 | down i h=>rw [←remove_take,Q.glow_down,theta_downV,theta_downV,V.glow_free,V.glow_up,←hx,←act_mul,←act_mul,twist_product]
 | add _ _ ih it=> rw [Q.glow_sum,theta_add, ih,it, theta_add, V.glow_sum]
 | scale _ c ih=> rw [Q.glow_free,theta_smul,ih,theta_smul, V.glow_free]
 | mul _ _ ih it=> rw [Q.glow_mult,theta_mul, ih,it, theta_mul,V.glow_mult]
variable {T:Pea I}
lemma glow_weight (a b:ℝ): twist U (T.Φ a b)= (T.face U).Φ b a:=by unfold Pea.Φ; rw [map_add,map_add,map_one,map_smul,map_smul]; unfold Pea.face; dsimp only; abel
lemma glow_fits : twist U T.mint.sell=star (T.face U).mint.buy:=by change twist U _=star ((T.face U).Φ 1 (-(1/2:ℝ))); rw [(T.face U|>.tale _ _ : IsSelfAdjoint (T.face U).mint.buy).star_eq]; exact glow_weight U .. -- tune args
lemma mounted(U: UNI I){P Q B:Op I} (p:IsStarProjection P)(h:IsStarProjection Q)(b:IsStarProjection B)(hx:twist U P= 1-Q)(t:twist U B=1-B)(k:ℕ) : twist U (Saber (B:=B) p k).sell = star (Saber (B:=B) h k).buy:=by
 change twist U (1+star (Comb B P k))=_; rw [map_add,map_one,map_star,←je_twist,t,hx,comb_cross h b]; unfold Saber; simp [sub_eq_add_neg]
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.Pea.theta_hat
