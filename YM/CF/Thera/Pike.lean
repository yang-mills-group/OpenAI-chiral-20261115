import YM.CF.Thera.Palm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Spire Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{P B W Z K D O C:Op n} (h:Clad P B W Z K)(t:Clad (1-P) (1-B) Z W O)
private lemma twistStar {A C: Op n}(u:IsStarProjection B)(p:star A*B=star A):B*A=A:=by nth_rw 1 [←u.isSelfAdjoint]; nth_rw 1 [←star_star A]; rw [←star_mul,p,star_star]
include h t
lemma inverseH: laneP (1-B) Z O= -star (laneP B W K):=by
 let Y:= laneP B W K; let F:=laneP (1-B) Z O
 have hg : F=(1-(1-B))*Z*O:=rfl; rw [sub_sub_cancel] at hg; have ht:B*F=F:=by rw [hg]; simp only [←mul_assoc,h.helm.isIdempotentElem.eq]
 have hx:star K *(1-P)=0:=by rw [← (IsStarProjection.one_sub h.proj).isSelfAdjoint,←star_mul,sub_mul,one_mul,h.tray,sub_self,star_zero]
 -- orthogonality direct star K W† Z O =0. W K=B+Y
 have hp:W*K=B+Y:=by unfold Y laneP; rw [sub_mul,sub_mul,one_mul,h.quotaW]; abel
 have hZ:Z*O=1-B+F:=by unfold F laneP; rw [sub_mul,sub_mul,one_mul,t.quotaW]; abel
 have hQ:star (W*K)*(Z*O)=0:=by rw [star_mul, mul_assoc,←mul_assoc (star W),h.rain,one_mul]; nth_rw 1 [← t.tray]; rw [←mul_assoc,hx,zero_mul]
 have hw:star Y*B=0:=by rw [←show star B=B from h.helm.isSelfAdjoint,←star_mul,show B*Y=0 from h.bare,star_zero]
 have hx:star Y * F=0:=by nth_rw 1 [←ht]; rw [←mul_assoc,hw,zero_mul]
 rw [hp,hZ,star_add,h.helm.isSelfAdjoint, add_mul,mul_add,mul_add,Porth h.helm,ht,hx,add_zero,zero_add,mul_sub,mul_one,hw,sub_zero] at hQ; exact eq_neg_of_add_eq_zero_left hQ
lemma reflectL (p:TagG P C)(g:IsUnit (1+bentT K B W C))(w:IsUnit (1+bentT O (1-B) Z (-star C))): traitP (1-B) O Z (-star C)= -star (traitP B K W C):=by
 have hp:=rideK h p g; have hx:=rideK t (p.strap h.proj.isSelfAdjoint) w; rw [←sub_eq_add_neg,star_neg,star_star,sub_neg_eq_add] at hx; have he:= inverseH hp hx; unfold traitP; rw [←sub_eq_add_neg]; exact he
lemma xover (p:TagG P C): star (bentT O (1-B) Z (-star C))= C*K*B*W*(1-P):=by
 -- from V W†=1: (1-B)V(P)* (P W† B)+(1-B)V(1-P)*W†B=0 ⇒ need V-+ uses W times? correct matrices index input vs Q output dual multiply V*W†=1
 let S:=1-P; let T:=1-B; have ht:O*(T*Z*P)= -(S*star W*B*star K):=by
   let M:= B*W*P
   have he:star M=P*star W*B:=by unfold M; rw [star_mul,star_mul,h.proj.isSelfAdjoint,h.helm.isSelfAdjoint,mul_assoc]
   have hp: O*T=O:=t.stem; have hc: O*B=0:=by rw [show B=1-T from (sub_sub_cancel _ _).symm,mul_sub,hp,mul_one,sub_self]
   have hx:O*Z*P*star W*B= -(O*Z*S*star W*B):=by
      unfold S; rw [mul_sub,mul_one,sub_mul,sub_mul,mul_assoc O Z (star W), show Z * star W=1 from mul_eq_one_comm.mp h.rain,mul_one,hc,zero_sub,neg_neg]
   have hy:star M * star K=P:=by rw [←star_mul,h.left,h.proj.isSelfAdjoint] -- tune M h.left
   change O*_= _; simp only [←mul_assoc]; rw [hp]
   rw [show O*Z*S=S from ?_] at hx
   · calc
       _ = O*Z*(P*P):=by rw [h.proj.isIdempotentElem.eq]
       _ = O*Z*P*star M*star K:=by rw [←mul_assoc,mul_assoc (O*Z*P), hy] -- tune
       _ = _:=by rw [he]; simp only [←mul_assoc]; rw [mul_assoc (O*Z) P P,h.proj.isIdempotentElem.eq,hx]; rw [neg_mul] -- tune neg mul
   rw [←hp, mul_assoc O T, mul_assoc O (T*Z)]; exact t.left
 unfold bentT; change star (O*(T*Z)* -star C)=_; have hg:P*star C=star C:=by nth_rw 1 [←h.proj.isSelfAdjoint]; rw [←star_mul,p.2]
 rw [mul_neg,show O*(T*Z)*star C= -((1-P)*star W*B*star K)*star C from (by rw [←ht,←hg]; simp only [mul_assoc,hg]),neg_mul,neg_neg,star_mul,star_mul,star_mul,star_mul,star_star,star_star,h.helm.isSelfAdjoint.star_eq,star_star, t.proj.isSelfAdjoint,mul_assoc,mul_assoc]; simp only [mul_assoc]
end YM.CF.Thera
