import YM.SU5.Selected.Chene.Pad
/-! Price identity. Given Schur handoff on the FULL coarse operator (not modulo gradients!), and a chosen matching harmonic chart. Linear algebra for the untruncated precision matrices of that strong-budget step. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Chene.Pad
open Function Finset Matrix
open scoped Matrix BigOperators
variable {I J K R T X:Type*} [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype K][DecidableEq K][Fintype R][DecidableEq R]

-- first export symmetric loops in general scalar matrix.
def stance (P:Matrix I K T)(Q:Matrix J K T): Matrix (I⊕J) K T:= Matrix.of fun x i=> Sum.elim (fun j=>P j i) (fun j=>Q j i) x
def seat (P:Matrix K I T)(Q:Matrix K J T): Matrix K (I⊕J) T:= Matrix.of fun x i=> Sum.elim (fun j=>P x j) (fun j=>Q x j) i
@[simp] theorem stance_a(P:Matrix I K T)(Q:Matrix J K T) (x:I)(i:K): stance P Q (.inl x) i=P x i:=rfl
@[simp] theorem stance_b(P:Matrix I K T)(Q:Matrix J K T) (x:J)(i:K): stance P Q (.inr x) i=Q x i:=rfl
@[simp] theorem seat_a(P:Matrix K I T)(Q:Matrix K J T) (x:K)(i:I): seat P Q x (.inl i)=P x i:=rfl
@[simp] theorem seat_b(P:Matrix K I T)(Q:Matrix K J T) (x:K)(i:J): seat P Q x (.inr i)=Q x i:=rfl
lemma seat_turn(P: Matrix K I T)(Q: Matrix K J T) : (seat P Q)ᵀ=stance Pᵀ Qᵀ:=rfl
@[simp] lemma stance_zero [Zero T] : stance (0:Matrix I K T) (0:Matrix J K T)=0:=by ext (i|i) <;> rfl
section
variable [Semiring T]
lemma stand (A:Matrix I I T)(B:Matrix I J T)(C:Matrix J I T)(D:Matrix J J T) (P:Matrix I K T)(Q:Matrix J K T): Matrix.fromBlocks A B C D*stance P Q=stance (A*P+B*Q) (C*P+D*Q):=by
 ext (i|i)<;> simp [Matrix.mul_apply,Fintype.sum_sum_type]
lemma stances(P:Matrix I R T)(Q:Matrix J R T)(X:Matrix R I T)(Y:Matrix R J T): stance P Q*seat X Y=Matrix.fromBlocks (P*X) (P*Y) (Q*X) (Q*Y):=by ext (i|i) (j|j)<;>simp [Matrix.mul_apply]
lemma stake(P:Matrix R I T)(Q:Matrix R J T)(X:Matrix I K T)(Y:Matrix J K T) : seat P Q * stance X Y=P*X+Q*Y:=by ext; simp [Matrix.mul_apply,Fintype.sum_sum_type]
end

def leftHill (S:Finset I)(T:Finset J)(i:forestFree S):forestFree (S.disjSum T):= ⟨.inl i.val,fun h=>i.property (inl_mem_disjSum.mp h)⟩
def rightHill (S:Finset I)(T:Finset J)(i:forestFree T):forestFree (S.disjSum T):=⟨.inr i.val,fun h=>i.property (inr_mem_disjSum.mp h)⟩
def hills (S:Finset I)(T:Finset J): (forestFree S ⊕ forestFree T)≃forestFree (S.disjSum T) where
 toFun:= Sum.elim (leftHill S T) (rightHill S T)
 invFun
 | ⟨.inl a,q⟩=> .inl ⟨a,fun x=>q (inl_mem_disjSum.mpr x)⟩
 | ⟨.inr a,q⟩=> .inr ⟨a,fun x=>q (inr_mem_disjSum.mpr x)⟩
 right_inv:=fun ⟨x,q⟩=>by cases x<;> rfl
 left_inv:=fun x=>by obtain ⟨a,q⟩|⟨b,p⟩:= x<;> rfl
@[simp] lemma hills_l (S:Finset I)(T:Finset J)(i:forestFree S) : hills S T (.inl i)=leftHill S T i:=rfl
@[simp] lemma hills_r (S:Finset I)(T:Finset J)(i:forestFree T) : hills S T (.inr i)=rightHill S T i:=rfl
def wrote (S:Finset I) : Matrix (forestFree S) I ℝ := walk Subtype.val
lemma drape (S:Finset I) : wrote S * (wrote S)ᵀ=1:=pulse_cost _ Subtype.val_injective
lemma mercy (S:Finset I)(T:Finset J)(A:Matrix I I ℝ)(B:Matrix I J ℝ)(C:Matrix J I ℝ)(D:Matrix J J ℝ):
    let U:=wrote S; let V:= wrote T; let H:= hills S T; (principal (Matrix.fromBlocks A B C D) (S.disjSum T)).submatrix H H= fromBlocks (U*A*Uᵀ) (U*B*Vᵀ) (V*C*Uᵀ) (V*D*Vᵀ):=by
 intro U V H; change _= fromBlocks (_*(wrote S)ᵀ) (_*(wrote T)ᵀ) (_*(wrote S)ᵀ) (_*(wrote T)ᵀ); unfold U V; unfold wrote; simp_rw [pull_cost,pull_pay]; ext (i|i) (j|j)<;> rfl
lemma merit (S:Finset I)(T:Finset J)(A:Matrix I I ℝ)(B:Matrix I J ℝ)(C:Matrix J I ℝ)(D:Matrix J J ℝ):
    let U:=wrote S; let V:=wrote T; (principal (fromBlocks A B C D) (S.disjSum T)).det=(fromBlocks (U*A*Uᵀ) (U*B*Vᵀ) (V*C*Uᵀ) (V*D*Vᵀ)).det:=by
     intro U V; rw [←det_submatrix_equiv_self (hills S T),mercy ..]
lemma chosen (A:Matrix I I ℝ)(S:Finset I): principal A S= wrote S*A*(wrote S)ᵀ:=Eq.symm (pulse_min A _ _)

def rose (r:ℝ)(A:Matrix I I ℝ)(P:Matrix J I ℝ):= A+r • (Pᵀ*P)
def bolt (A:Matrix I I ℝ)(P:Matrix J I ℝ)(r:ℝ): Matrix (I⊕J) (I⊕J) ℝ:=fromBlocks (rose r A P) ((-r) • Pᵀ) ((-r) • P) (r • 1)

variable (P:Matrix J I ℝ)(p:ℝ)(A:Matrix I I ℝ)(B:Matrix J J ℝ)(L:Matrix R I ℝ)(R':Matrix R J ℝ)
lemma pinned(A:Matrix I I ℝ)(g:Aᵀ=A): (A+Lᵀ*L)ᵀ=A+Lᵀ*L:=by rw [transpose_add,transpose_mul,transpose_transpose,g]
lemma bolt_symm(g:Aᵀ=A) : (bolt A P p)ᵀ=bolt A P p:=by
 unfold bolt rose; simp [fromBlocks_transpose,g]
lemma reach(W:Matrix I K ℝ)(Z:Matrix J K ℝ) (h:A*W=0)(u:P*W=Z) : bolt A P p *stance W Z=0:=by
 unfold bolt rose; rw [stand]; simp only [Matrix.add_mul,h,Matrix.smul_mul, Matrix.mul_assoc,u,Matrix.one_mul,zero_add,neg_smul,Matrix.neg_mul,add_neg_cancel,neg_add_cancel,stance_zero]
lemma latticeFieldEstimates (S:Finset I)(r:ℝ) (hr:r≠0):
     (principal (bolt (A+Lᵀ*L) P r) (S.disjSum ∅)).det= r^Fintype.card J*(principal (A+Lᵀ*L) S).det:=by
 let M:=A+Lᵀ*L; let U:= wrote S; let X:= rose r M P; let V:=wrote (∅:Finset J)
 let G:=r • (1:Matrix (forestFree (∅:Finset J)) (forestFree (∅:Finset J)) ℝ); let Q : forestFree (∅:Finset J)≃ J:= ⟨Subtype.val,fun j=>⟨j,by simp⟩,fun ⟨_,_⟩=>rfl,fun _=>rfl⟩
 have hv:Vᵀ*V=1:=by -- det orth by coordinate
    calc
    _ = Matrix.submatrix (1:Matrix J J ℝ) id Q * (1:Matrix J J ℝ).submatrix Q id := by unfold V wrote walk; ext i j; simp [Matrix.mul_apply,Q,Matrix.one_apply,eq_comm]; -- tune
    _ = _ := by rw [submatrix_mul_equiv,Matrix.one_mul]; rfl
 have hg:V*(r • (1:Matrix J J ℝ))*Vᵀ=G:=by rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,drape]
 have hx:r⁻¹ • G=1:=by unfold G; rw [smul_smul,inv_mul_cancel₀ hr,one_smul]

 letI : Invertible G:=⟨(r⁻¹ • 1:Matrix _ _ ℝ),by rw [Matrix.smul_mul,Matrix.one_mul,hx],by rw [Matrix.mul_smul,Matrix.mul_one,hx]⟩
 change (principal (bolt M P _) _).det=_; unfold bolt; rw [merit,hg, Matrix.det_fromBlocks₂₂]; rw [show G.det=r^Fintype.card J from by unfold G; rw [det_smul,det_one,Fintype.card_congr Q,_root_.mul_one]]; congr 1
 -- show Schur
 change (U*X*Uᵀ-U*((-r)• Pᵀ)*Vᵀ*(r⁻¹ • (1:Matrix _ _ ℝ))*(V*((-r) • P)*Uᵀ)).det = (principal M S).det; congr 1; rw [chosen]; unfold X rose; simp only [Matrix.mul_add,Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]; -- simplify
 suffices U*(Pᵀ*P)*Uᵀ=(U*Pᵀ)*Vᵀ*(V*P*Uᵀ) by
    rw [Matrix.mul_one, smul_smul,smul_smul,show (-r)*r⁻¹ * -r=r from ?_, this]; swap; · field_simp
    abel
 symm; calc _= U*(Pᵀ*(Vᵀ*V)*P)*Uᵀ:= by simp only [Matrix.mul_assoc]
             _= _:= by rw [hv,Matrix.mul_one] -- tune
lemma pinned_bolt_l : bolt (A+Lᵀ*L) P p= bolt A P p+(seat L (0:Matrix R J ℝ))ᵀ*(seat L (0:Matrix R J ℝ)):=by
 rw [seat_turn,stances,transpose_zero]; unfold bolt rose; simp only [fromBlocks_add, Matrix.mul_zero, Matrix.zero_mul,add_zero]; rw [add_right_comm]
lemma pinned_bolt_r (X:Matrix J J ℝ) (x: X=B+R'ᵀ*R') (S:Finset I) (T:Finset J) (u:IsUnit (principal (rose p A P) S).det)
    (h: p • 1- (((-p)• P)*(wrote S)ᵀ)*(principal (rose p A P) S)⁻¹*(wrote S*((-p)• Pᵀ))=B) :
    (principal (bolt A P p+(seat (0:Matrix R I ℝ) R')ᵀ*(seat (0:Matrix R I ℝ) R')) (S.disjSum T)).det = (principal (rose p A P) S).det*(principal X T).det:=by
 rw [seat_turn,stances,transpose_zero]; unfold bolt; simp only [Matrix.zero_mul, Matrix.mul_zero, fromBlocks_add,add_zero]; rw [merit,←chosen]; letI:= ((isUnit_iff_isUnit_det _).mpr u).invertible
 rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]; congr 2
 rw [chosen X,x,←h]; let U:=wrote T; let L:=((-p) • P)*(wrote S)ᵀ; let Z: Matrix J J ℝ:= p • (1:Matrix J J ℝ); simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]; abel

lemma plateau (X:Matrix (I⊕J) K ℤ) (S:Finset I) (F:Finset I) (T:Finset J) (x:Arbor X (S.disjSum ∅))(y:Arbor X (F.disjSum T))
    (s : Aᵀ=A)(hp:p ≠ 0)(q:bolt A P p*realM X=0)
    (H:seat L (0:Matrix R J ℝ)*realM X=0)(H':seat (0:Matrix R I ℝ) R'*realM X=0)
    (W:Matrix I R ℝ)(Hw:A*W=0)(pv:L*W=1)(py:R'*(P*W)=1)
    (h0:IsUnit (principal (rose p A P) F).det)
    (h:p • 1-(((-p) • P)*(wrote F)ᵀ)*(principal (rose p A P) F)⁻¹*(wrote F*((-p)• Pᵀ))=B):
    p^Fintype.card J*(principal (A+Lᵀ*L) S).det=(principal (rose p A P) F).det*(principal (B+R'ᵀ*R') T).det :=by
 let Ω:=bolt A P p; let Θ:=seat L (0:Matrix R J ℝ); let Θ':=seat (0:Matrix R I ℝ) R'; let V:=stance W (P*W); let Z:= realM X
 let X':= S.disjSum (∅:Finset J); let Y:= F.disjSum T
 have kv:Θ*V=1:= by rw [stake]; rw [pv,Matrix.zero_mul,add_zero]
 have kv':Θ'*V=1:= by rw [stake]; rw [Matrix.zero_mul,py,zero_add]
 have η: Ω*V=0:= reach _ _ _ _ _ Hw rfl
 have hs:Ωᵀ=Ω:=bolt_symm _ _ _ s
 have he(φ:Matrix R (I⊕J) ℝ)(p:φ*Z=0) : (Ω+φᵀ*φ)*Z=0:=by rw [Matrix.add_mul, Matrix.mul_assoc,p, Matrix.mul_zero, q,add_zero]; -- q defeq?
 let Q:= selector Y y.idJ; let B':= Ω+Qᵀ*Q; let Z':=Q*Z; let v:= (Z')⁻¹*(Q*V); let M:= V-Z*v
 have hp':Z'*Z'⁻¹=1:=Matrix.mul_nonsing_inv _ (y.trust _)
 have hM: Q*M=0:=by rw [show M= _ from (rfl:M=V-Z*v),Matrix.mul_sub,← Matrix.mul_assoc Q Z]; change Q*V-Z'*v=0; rw [show v= _ from rfl,← Matrix.mul_assoc,hp',Matrix.one_mul,sub_self] -- tune
 have hB:B'*M=0:=by unfold B'; rw [Matrix.add_mul, Matrix.mul_assoc,hM, Matrix.mul_zero,add_zero]; unfold M; rw [Matrix.mul_sub,← Matrix.mul_assoc Ω Z,q,η,Matrix.zero_mul,sub_zero] -- tune
 have ht: Θ*M=1:=by unfold M; rw [Matrix.mul_sub, kv, ← Matrix.mul_assoc, H,Matrix.zero_mul,sub_zero]
 have hu: Θ'* M=1:=by unfold M; rw [Matrix.mul_sub, kv',← Matrix.mul_assoc,H',Matrix.zero_mul,sub_zero]
 rw [←latticeFieldEstimates, pinned_bolt_l]
 · change (principal (Ω+Θᵀ*Θ) X').det=_
   rw [x.signed _ (pinned _ _ hs) (he Θ H) y, ← pinned_bolt_r P p A B R' (B+R'ᵀ*R') rfl F T h0 h,← y.basis_paid (Ω+Θᵀ*Θ) (pinned _ _ hs) (he Θ H) y.idJ,← y.basis_paid (Ω+Θ'ᵀ*Θ') (pinned _ _ hs) (he Θ' H') y.idJ]; -- tune inference
   change (Ω+Θᵀ*Θ+Qᵀ*Q).det=(Ω+Θ'ᵀ*Θ'+Qᵀ*Q).det; rw [add_right_comm,add_right_comm Ω (Θ'ᵀ*Θ')]; change (B'+Θᵀ*Θ).det=(B'+Θ'ᵀ*Θ').det; rw [det_exchange _ _ (pinned _ _ hs) Θ' Θ hB (by rw [hu]; simp),ht,hu]; simp; rfl
   -- subgoals of pinned bolt
 · exact hp
end YM.Chene.Pad
#print axioms YM.Chene.Pad.plateau
