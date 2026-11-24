import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Real.Basic
/-! Tree slices for real Gaussian price. Work toward improving signed pressure
via PPP (periodic, massive price in the harmonic slots), NO deletion of those
slots from any of the actual steps.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Chene.Pad
open Function Finset Matrix
open scoped Matrix BigOperators
variable {I J R T : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (D : Matrix I J ℤ) (A : Matrix I I ℝ)
abbrev realM (D:Matrix I J ℤ):= D.map (Int.castRingHom ℝ)
def Arbor (S:Finset I) := Function.Bijective ((D.submatrix (Subtype.val:↥S→I) id).mulVec)
namespace Arbor
variable {D} {S:Finset I}
lemma card (p: Arbor D S) : Fintype.card J= S.card:=by
 let f:=(D.submatrix (Subtype.val:↥S→I) id).mulVecLin
 let e:=LinearEquiv.ofBijective f p
 simpa only [Fintype.card_coe] using card_eq_of_linearEquiv ℤ e
lemma squarish (p: Arbor D S) (d:J≃↥S): IsUnit (D.submatrix (Subtype.val ∘ d) id).det:=by
 let B:=D.submatrix (Subtype.val∘d) id
 apply (Matrix.isUnit_iff_isUnit_det _).1; apply Matrix.mulVec_surjective_iff_isUnit.mp
 intro v; obtain ⟨x,h⟩:=p.2 (v∘d.symm); refine ⟨x,funext fun i=>?_⟩; exact (show (B*ᵥx) i=(v∘d.symm) (d i) from congrFun h (d i)).trans (by simp)
end Arbor
variable [Fintype R] [DecidableEq R]

def walk (f:J→I): Matrix J I ℝ:= (1:Matrix I I ℝ).submatrix f id
lemma pull_cost (X:Matrix I T ℝ)(f:J→I) : walk f * X=X.submatrix f id:=by ext i j; exact Matrix.ext_iff.mpr (Matrix.one_mul X) (f i) j
lemma pull_pay (X:Matrix T I ℝ)(f:J→I) : X*(walk f)ᵀ=X.submatrix id f:=by
 have he:= congrArg Matrix.transpose (pull_cost Xᵀ f); simpa only [transpose_mul,transpose_transpose, transpose_submatrix] using he
lemma pulse_min (A:Matrix I I ℝ)(f:J→I)(g:R→I): walk f*A*(walk g)ᵀ=A.submatrix f g:=by rw [pull_cost,pull_pay]; rfl
lemma pulse_cost(f:J→I) (p:Injective f): walk f * (walk f)ᵀ=1:=by
 nth_rw 1 [←Matrix.mul_one (walk f)]; rw [pulse_min,submatrix_one _ p]
lemma pulse_zero (f:J→I)(g:R→I)(p:∀ i j,f i ≠ g j): walk f*(walk g)ᵀ=0:=by
 rw [← Matrix.mul_one (walk f), pulse_min]; ext i j; exact Matrix.one_apply_ne (p i j)

section steer
variable (G:Matrix I J ℝ) {S:Finset I} (f:J→I)(g:R→I)
lemma det_exchange (h:Aᵀ=A)(C B:Matrix J I ℝ)(hp:A*G=0)(x:IsUnit (C*G).det):
    (A+Bᵀ*B).det=((C*G).det⁻¹*(B*G).det)^2*(A+Cᵀ*C).det :=by
 let X:=C*G; let Y:=X⁻¹
 let K:=Y * (B-C); let W:=G*K; let H:= (1:Matrix I I ℝ)+W
 have hx:X*Y=1:= mul_nonsing_inv _ x; have hy:Y*X=1:= nonsing_inv_mul _ x
 have ht:C*H=B:=by unfold H W K; simp only [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,show C*G*Y=1 from hx, Matrix.one_mul, add_sub_cancel] -- hx expanded? fix later
 have hb:A*H=A:=by unfold H W; simp only [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,hp,Matrix.zero_mul,add_zero]
 have hr:Hᵀ*A=A:=by have he:= congrArg Matrix.transpose hb; rw [Matrix.transpose_mul,h] at he; exact he
 have hi:H.det=X.det⁻¹*(B*G).det:=by
    rw [show H=1+G*K from rfl, det_one_add_mul_comm, show K*G=Y*(B*G)-1 from ?_, add_sub_cancel]; rw [det_mul]; unfold Y; rw [det_nonsing_inv]; exact (by rw [Ring.inverse_eq_inv]) -- tune lemma
    unfold K; rw [Matrix.mul_assoc,Matrix.sub_mul,Matrix.mul_sub,show C*G=X from rfl,hy]
 have he:Hᵀ*(A+Cᵀ*C)*H=A+Bᵀ*B:=by rw [Matrix.mul_assoc,Matrix.add_mul,hb,Matrix.mul_assoc,ht, Matrix.mul_add,hr, ←Matrix.mul_assoc Hᵀ, ←transpose_mul, ht]
 rw [←he,det_mul,det_mul,det_transpose,hi]; unfold X; ring
lemma det_principal (f_:R→I)(e:J⊕R ≃ I)(h₁:∀ i,e (.inl i)=f i)(h₂:∀ i,e (.inr i)=f_ i)(X:Matrix I I ℝ)(p:walk f*G=1)(hp:X*G=0)(s:Xᵀ=X): (X+(walk f)ᵀ*walk f).det=(X.submatrix f_ f_).det:=by
 let U:=walk f; let V:=walk f_; let H:= X+Uᵀ*U
 have hz : U*Vᵀ=0:= pulse_zero _ _ fun i j=>by rw [←h₁,←h₂]; intro p; have hp:= e.injective p; contradiction
 have hx : U*Uᵀ=1:=pulse_cost _ (fun i j p=> Sum.inl_injective (e.injective ((h₁ i).trans (p.trans (h₁ j).symm)))) -- binder i implicit? tune
 let W:= (1:Matrix I I ℝ)+(G-Uᵀ)*U
 have ha:U*(G-Uᵀ)=0:=by rw [Matrix.mul_sub,hx,p,sub_self]
 have hw:W.det=1:=by unfold W; rw [det_one_add_mul_comm,ha,add_zero,det_one]
 have he: W*Vᵀ=Vᵀ:=by unfold W; rw [Matrix.add_mul,Matrix.one_mul, Matrix.mul_assoc,hz,Matrix.mul_zero,add_zero]
 have hb: W*Uᵀ=G:=by unfold W; rw [Matrix.add_mul,Matrix.one_mul, Matrix.mul_assoc,hx,Matrix.mul_one, add_sub_cancel] -- tune syntax
 let K:=Wᵀ*H*W
 have hu: Hᵀ=H:=by unfold H; rw [transpose_add,transpose_mul,transpose_transpose,s]
 have hK:Kᵀ=K:= by unfold K; rw [transpose_mul,transpose_mul,transpose_transpose,hu, Matrix.mul_assoc]
 have hg: H*G=Uᵀ:=by unfold H; rw [Matrix.add_mul,hp, Matrix.mul_assoc,p, Matrix.mul_one,zero_add]
 have hA:K.submatrix f f=1:=by
    rw [← pulse_min (R:=J)]; change U*K*Uᵀ=1; unfold K; simp only [Matrix.mul_assoc, hb,hg]; rw [← Matrix.mul_assoc, show U*Wᵀ=Gᵀ by simpa only [transpose_mul,transpose_transpose] using congrArg Matrix.transpose hb, ←transpose_mul, p,transpose_one]
 have hv: V*Wᵀ=V:= by simpa only [transpose_mul,transpose_transpose] using congrArg Matrix.transpose he
 have hB: K.submatrix f_ f=0:=by
    rw [← pulse_min]; change V*K*Uᵀ=0; unfold K; simp only [Matrix.mul_assoc,hb,hg]; rw [← Matrix.mul_assoc,hv]; simpa only [transpose_mul,transpose_transpose,transpose_zero] using congrArg Matrix.transpose hz
 have hD: K.submatrix f_ f_ = X.submatrix f_ f_:=by
    rw [← pulse_min,← pulse_min]; change V*K*Vᵀ=_; unfold K; simp only [Matrix.mul_assoc,he]; rw [← Matrix.mul_assoc,hv]; unfold H; rw [Matrix.add_mul, Matrix.mul_assoc,hz,Matrix.mul_zero,add_zero]
 have he': K.submatrix e e= Matrix.fromBlocks 1 (K.submatrix f f_) 0 (X.submatrix f_ f_):=by
    ext (i|i) (j|j)<;>first | change K (e _) (e _) = _
    · rw [h₁,h₁]; exact Matrix.ext_iff.mpr hA i j
    · rw [h₁,h₂]; rfl
    · rw [h₂,h₁]; exact Matrix.ext_iff.mpr hB i j
    rw [h₂,h₂]; exact Matrix.ext_iff.mpr hD i j
 have ht:H.det=K.det:=by unfold K; rw [det_mul,det_mul,det_transpose,hw,_root_.one_mul,_root_.mul_one]
 exact ht.trans ((det_submatrix_equiv_self e K).symm.trans (by rw [he',det_fromBlocks_zero₂₁,det_one,_root_.one_mul]))
end steer
abbrev selection (S:Finset I) := {a : I // a∈S}
abbrev forestFree (S: Finset I):= {a : I // ¬a∈S}
noncomputable def principal (A: Matrix I I ℝ)(S:Finset I): Matrix (forestFree S) (forestFree S) ℝ:= A.submatrix Subtype.val Subtype.val
noncomputable def selector (S:Finset I)(d:J≃ ↥S):= walk (Subtype.val ∘ d)
namespace Arbor
variable {D} {S:Finset I} (p: Arbor D S)
noncomputable def idJ : J≃ ↥S:= Fintype.equivOfCardEq (p.card.trans (Fintype.card_coe _).symm) -- card argument proof used
include p
lemma unitJ (d:J≃ ↥S): (selector S d* realM D).det^2=1 :=by
 let X:= D.submatrix (Subtype.val∘d) id
 rw [selector,pull_cost]; change (X.map (Int.castRingHom ℝ)).det ^2 = _; rw [←RingHom.mapMatrix_apply (Int.castRingHom ℝ),← RingHom.map_det]; obtain g | g:=Int.isUnit_iff.mp (p.squarish d); rw [show X.det=1 from g,_root_.map_one,one_pow]; rw [show X.det= -1 from g,_root_.map_neg,_root_.map_one]; ring
lemma trust (d:J≃ ↥S): IsUnit (selector S d*realM D).det := IsUnit.mk0 _ (fun x=> (by have he:= p.unitJ d; rw [x] at he; norm_num at he))
lemma basis_paid (s:Aᵀ=A)(h:A*realM D=0)(d:J≃ ↥S): let U:=selector S d; (A+ Uᵀ*U).det=(principal A S).det:=by
 intro X; let D':=realM D; let F:= (X*D')⁻¹; let Q:=D'*F; let Y:= (Equiv.sumCongr d (Equiv.refl (forestFree S))).trans (Equiv.sumCompl _); exact det_principal Q (Subtype.val∘d) Subtype.val Y (fun i=>rfl) (fun i=>rfl) A (by rw [show walk _*Q= X*Q from rfl]; unfold Q; rw [←Matrix.mul_assoc]; exact Matrix.mul_nonsing_inv _ (p.trust d)) (by unfold Q; rw [←Matrix.mul_assoc,h,Matrix.zero_mul]) s -- add s later; G A? #check
#check det_principal
lemma signed (s:Aᵀ=A)(h:A*realM D=0){T: Finset I} (t: Arbor D T) : (principal A S).det=(principal A T).det:=by
 rw [← p.basis_paid A s h p.idJ,←t.basis_paid A s h t.idJ]; -- dot? add s
 let Y:=selector T t.idJ; let X:=selector S p.idJ; let U:=realM D
 change (A+Xᵀ*X).det=_; rw [det_exchange _ _ s Y X h (t.trust _),mul_pow, inv_pow,t.unitJ,p.unitJ, inv_one, _root_.one_mul,_root_.one_mul]
end Arbor
end YM.Chene.Pad
#print axioms YM.Chene.Pad.Arbor.signed
