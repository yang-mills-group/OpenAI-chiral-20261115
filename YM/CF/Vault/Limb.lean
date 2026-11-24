import YM.CF.Vault.Ermine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
section rings
variable {n:Type*}[Fintype n][DecidableEq n][Nonempty n] (A:Op n)(p:IsStarProjection A) (V:Op n)(v:IsUnit V)(W Y:Op n)
def fort (A V:Op n):= V⁻¹*A+star V*(1-A)
include p v in
lemma fort_r (h:Commute A V) : Commute A (fort A V)∧ star (fort (1-A) V)*fort A V=1:=by
 have hp:A*A=A:=p.1; have hg:star A=A:=p.2; let P:=1-A; have hc': Commute A (1-A):=(Commute.one_right _).sub_right (Commute.refl _); have hm:A*P=0:= Porth p; have hx:P*A=0:=hc'.eq ▸ hm
 have hK:P*P=P:=p.one_sub.1
 have h1: V*V⁻¹=1:=(Fock.live v).1; have h2: V⁻¹*V=1:=(Fock.live v).2; have hs:star V⁻¹*star V=1:=by rw [←star_mul,h1,star_one]
 have h':Commute A V⁻¹:= Dial.poleM v h; have ht :Commute A (star V):= Dial.brimM p.isSelfAdjoint h; unfold fort
 refine ⟨(Commute.mul_right h' (Commute.refl _)).add_right (Commute.mul_right ht hc'),?_⟩
 rw [sub_sub_cancel]; change star (V⁻¹*P+star V*A)*_= _
 have he:star P=P:= p.one_sub.2
 rw [star_add,star_mul,star_mul,he,hg,star_star,add_mul,mul_add,mul_add];
 rw [show P * star V⁻¹ * (V⁻¹*A)=0 by rw [←h'.eq,←mul_assoc,mul_assoc _ (star V⁻¹), ← (Dial.brimM p.isSelfAdjoint h'.eq),← mul_assoc,hx,zero_mul,zero_mul],show A*V*(star V*(1-A))=0 by rw [h.eq,mul_assoc,←mul_assoc A,ht.eq,mul_assoc (star V),hm,mul_zero,mul_zero],show A*V*(V⁻¹*A)=A by rw [←mul_assoc,mul_assoc _ V,h1,mul_one,hp],show P*star V⁻¹*(star V*(1-A))=P by rw [←mul_assoc,mul_assoc _ (star V⁻¹),hs,mul_one]; exact hK]; unfold P; abel
lemma steam (T:UNI n)(A B C:Op n)(h:IsUnit B)(p:twist T A=C)(v:twist T B=B): twist T (fort A B)=fort C B:=by
 unfold fort; rw [map_add,map_mul,map_mul,map_sub,map_one,p,map_star,v,show twist T B⁻¹=(twist T B)⁻¹ from singsUnit false _ _ h, v]
lemma revZen (T C D:UNI n)(A:Op n)(p: congrC T C.val=C.val)(q:congrC T D.val=D.val)(h: twist T A=A)(u:TickZ): twist T (ment u A C D)=ment u A C D:=by
 have hr (C:UNI n)(h:congrC T C.val=C.val): T.val*C.val=C.val*(cc T.val):=by
    rw [congr_form] at h; have hp:=congr_arg (fun i:Op n=>i*(ccU T).val) h; change T.val*C.val*_*_= _ at hp; rw [mul_assoc _ (star (ccU T).val), (ccU T).property.1,mul_one] at hp; exact hp
 have hv:=hr C p; have hg:=hr D q
 have hc: twist (ccU T) (cc A)=cc A:=by rw [←cc_twist,h]
 have hw:= twist_product (ccU T) (cc A); rw [hc] at hw; change cc A * cc T.val=cc T.val * cc A at hw
 have hy: cc T.val * star D.val=star D.val*T.val := by apply (live_of D.property.2).mul_left_cancel; rw [←mul_assoc,←hg,mul_assoc,D.property.2,mul_one,←mul_assoc,D.property.2,one_mul]
 rw [ment,map_add,twist_scalar,map_sub,h]; rw [show twist T (revY A C D)=revY A C D from ?_]; apply Mir.twist_comm; unfold revY; rw [←mul_assoc T.val,←mul_assoc, hv,mul_assoc _ (cc T.val),← hw]; simp only [mul_assoc]; rw [hy]
lemma jetKee (T:UNI n)(P:Op n): T.val*cc P=P*T.val ↔ sings true T P=P:=by constructor; exact fun h=> Mir.twist_comm T (cc P) P h; intro h; exact ( (twist_product T (cc P)).symm.trans (congrArg (fun x:Op n=> x*T.val) h))
lemma ort_Y (T:UNI n)(P:Op n)(p:IsSelfAdjoint P)(h:T.val*cc P=P*T.val): star T.val*P=cc P*star T.val:=by
 have he:=congr_arg star h; rw [star_mul,star_mul,p,← cc_star,p] at he; exact he.symm
lemma revSpin (A X:Op n)(a:IsSelfAdjoint A)(C D: UNI n)(hC:C.val*cc A=A*C.val)(hD:D.val*cc A=A*D.val)(p:Commute A X)(t:TickZ): Commute A (ment t X C D):=by
 unfold ment; apply p.add_right; apply Commute.smul_right; apply Commute.sub_right _ p; unfold Commute SemiconjBy revY; rw [←mul_assoc A,←mul_assoc, ←hC,mul_assoc C.val,← cc_mul,p.eq,cc_mul, ←mul_assoc, mul_assoc _ (cc A), ← ort_Y D A a hD, ←mul_assoc]
lemma starry (T U:UNI n)(A:Op n)(p:T.val*cc A=A*U.val): U.val*cc (star A)=star A*T.val :=by
 have ht:=congr_arg star p; rw [star_mul,star_mul,←cc_star] at ht; calc
  _ = (U.val * (cc (star A)*star T.val))*T.val:=by rw [mul_assoc,mul_assoc _ (star T.val),T.property.1,mul_one]
  _ = _:=by rw [ht,←mul_assoc,U.property.2,one_mul]
lemma invert_the (C D:UNI n) (P:Op n)(A:Op n)(v:IsUnit A)(p: revY A C D=A)(h:C.val*cc P=P*C.val)(q:D.val*cc P=P*D.val): D.val*cc (fort P A)=fort P A*C.val:=by
 have ht:C.val*cc A=A*D.val:=by
    have he:= congr_arg (fun t:Op n=>t*D.val) p; change (C.val*cc A)* star D.val*_= _ at he; rwa [mul_assoc _ (star D.val),D.property.1,mul_one] at he
 have hv:D.val*cc A⁻¹=A⁻¹*C.val:=by apply v.mul_left_cancel; rw [←mul_assoc,←ht,mul_assoc,← cc_mul,(Fock.live v).1,cc_one,mul_one, ← mul_assoc,(Fock.live v).1,one_mul]
 unfold fort; rw [cc_add,mul_add, cc_mul,←mul_assoc, hv,mul_assoc,h,←mul_assoc,add_mul]; congr 1
 rw [cc_mul,←mul_assoc,starry C D A ht, mul_assoc, cc_sub,cc_one,mul_sub,mul_one,h]; -- tune
 noncomm_ring
end rings
end YM.CF.Vault
