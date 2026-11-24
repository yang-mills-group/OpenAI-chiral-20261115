import YM.CF.BPress.Pf.Bore
/-! eq:B-modPf. Normalized? no: relationship relative to ket norm. `pivot` for Pf quotient phase/hum. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P C: Op I} {ε:ℝ}
namespace Bore
lemma abid {s:Finset I}(h:Bore (cutM s) C ε) : ‖pf C s‖ ^4= ‖(1-lost (cutM s) C).det‖:=by
 let P:=cutM s; let A:=cutC P C; let D:=1-P; have ht: padded s C=A+D:=by unfold padded A cutC; rw [show cc P=P from cut_real _]
 have hp:A*P=A:=by unfold A P; have he:=h.bump.1; rwa [cut_real] at he
 have hf :=h.p; have hd:A*D=0:=by unfold D; rw [mul_sub, mul_one,hp,sub_self]
 have hb:D*star A=0:=by have hx:= congrArg star hd; rwa [star_mul,hf.one_sub.isSelfAdjoint, star_zero] at hx
 have hg:(A+D)*star (A+D)= 1-lost P C:=by rw [star_add,hf.one_sub.isSelfAdjoint,mul_add,add_mul,add_mul,hb,hd,hf.one_sub.isIdempotentElem.eq,h.gram_eq]; unfold P; abel
 have he:(pf C s)^2=(A+D).det:= (pf_square _ _ h.sk).trans ((Fock.principal ..).trans (congrArg Matrix.det ht))
 rw [show ‖pf C s‖^4=‖(pf C s)^2‖^2 by rw [norm_pow]; ring,he,←hg,Matrix.det_mul,norm_mul]; rw [Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose]; simp [pow_two]
variable (h:Bore P C ε)
include h
lemma ratio (U:UNI I)(s:Finset I)(p:P=twist U (cutM s)): ‖inner ℂ (wedge U.val s) (pairWave C)‖^4= ‖(1-lost P C).det‖:=by
 change ‖stratum U s C‖^4=_; rw [stratum_pf]
 have ht:= h.turned (star U); nth_rw 1 [p, twist_inv] at ht; rw [abid ht];
 have hp := h.lot (star U); nth_rw 1 [p] at hp; rw [twist_inv] at hp; rw [hp,show 1-twist (star U) _=twist (star U) (1-lost P C) from by rw [map_sub,map_one], det_twist]
lemma modA {u:Wave I}(p:Top P u): ‖inner ℂ (pairWave C) u‖^4= ‖u‖^4*‖(1-lost P C).det‖:=by
 obtain ⟨V,s,c,g,e,rfl⟩:= p.usable; rw [norm_smul,wedge_norm, mul_one,inner_smul_right,norm_mul,mul_pow,norm_inner_symm,h.ratio V s g] -- norm swap
lemma cleanDet : (1-lost P C).det≠0:= isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h.realG)
lemma cleanA {u:Wave I}(p:Top P u): inner ℂ (pairWave C) u≠0:= by
 have hm:= h.modA p; intro E; have hg:=mul_pos (pow_pos (norm_pos_iff.mpr p.live) 4) (norm_pos_iff.mpr h.cleanDet); rw [←hm,E] at hg; simp at hg
lemma pivot : ‖filled P C‖^4= ‖(1-lost P C).det‖:=by obtain ⟨U,s,p⟩:=spot_projection P h.p; conv_lhs=> rw [p,placed]; rw [norm_smul,wedge_norm,mul_one]; exact h.ratio U s p
lemma cleanF: filled P C≠0:=by intro E; have he:=norm_pos_iff.mpr h.cleanDet; rw [←h.pivot,E] at he; simp at he
end Bore
end YM.CF.BPress.Pf
