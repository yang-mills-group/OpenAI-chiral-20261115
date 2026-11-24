import YM.CF.BProof.Align.Order

/-! Orthogonal projector to image of occupied space after stretching. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[DecidableEq I][Fintype I] {P S T:Op I}
def entered (P S:Op I):= star S*S+(1-P)
def send (P S:Op I):= (entered P S)⁻¹*star S
def land (P S:Op I):= S*send P S
structure Fit (P S:Op I) : Prop where
 proj: IsStarProjection P
 crop: S*P=S
 active : IsUnit (entered P S)
lemma shiftOn {A B C:Op I}(h:IsUnit A)(g:IsUnit B)(p:A*C=C*B) : A⁻¹*C=C*B⁻¹:= by
 calc
    _ = A⁻¹*(C*B)*B⁻¹:=by rw [mul_assoc, mul_assoc, (live g).1]; simp
    _ = _:=by rw [←p,←mul_assoc,(live h).2,one_mul]
namespace Fit
variable (h:Fit P S)
include h
lemma leftS : P*star S=star S:=by rw [← show star P=P from h.proj.isSelfAdjoint,← star_mul,h.crop]
lemma frameS : IsSelfAdjoint (entered P S):=(IsSelfAdjoint.star_mul_self _).add h.proj.one_sub.isSelfAdjoint
lemma frameI : IsSelfAdjoint (entered P S)⁻¹:=by
 rw [isSelfAdjoint_iff]; rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_nonsing_inv,show (entered P S)ᴴ=entered P S from h.frameS.star_eq] -- tune
lemma room_left : P*entered P S= star S*S := by rw [entered,mul_add,←mul_assoc,Porth h.proj,h.leftS,add_zero]
lemma room_right : entered P S*P=star S*S:=by rw [entered,add_mul,mul_assoc,h.crop,sub_mul,one_mul, h.proj.isIdempotentElem]; simp
lemma commI : Commute P (entered P S)⁻¹:=Commute.symm (shiftOn h.active h.active (by rw [h.room_left,h.room_right])) -- tune eq
lemma pulls : P*send P S=send P S:=by rw [send,← mul_assoc,h.commI.eq,mul_assoc,h.leftS]
lemma lays : send P S*S=P:=by rw [send, mul_assoc,← h.room_right,←mul_assoc,(live h.active).2,one_mul]
lemma keeps : land P S * S=S:= by rw [land,mul_assoc,h.lays,h.crop]
lemma landed : IsStarProjection (land P S):=by
 refine ⟨?_,?_⟩; · change land P S*(S*_)=_; rw [←mul_assoc,h.keeps]; rfl
 rw [isSelfAdjoint_iff, land,send,star_mul,star_mul,h.frameI,star_star,mul_assoc]
lemma trace : (land P S).trace=P.trace:=by rw [land, Matrix.trace_mul_comm,h.lays]
theorem range (x:Ket I) : acts (land P S) x=x ↔ ∃ y:Ket I, acts P y=y ∧ x=acts S y:=by
 constructor; · intro p; refine ⟨acts (send P S) x,?_,?_⟩; rw [←act_mul,h.pulls]; rw [←act_mul]; exact p.symm
 rintro ⟨y,p,rfl⟩; rw [←act_mul,h.keeps]
end Fit
end YM.CF.BProof.Align
