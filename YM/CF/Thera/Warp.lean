import YM.CF.Spire.Folly
import YM.CF.Thera.Cal
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
section core
variable {n:Type*}[DecidableEq n][Fintype n]{P B K W Z C:Op n}
def TagG(P C:Op n):Prop:= P*C=0∧ C*P=C
lemma TagG.pen (v:TagG P C): (1-P)*C=C:=by rw [sub_mul,one_mul,v.1,sub_zero]
lemma TagG.nil(v:TagG P C): C*C=0:=by nth_rw 1 [←v.2]; rw [mul_assoc,v.1,mul_zero]
lemma TagG.mud (v:TagG P C): (1-C)*(1+C)=1:=by rw [mul_add,mul_one,sub_mul,one_mul,v.nil]; abel
lemma TagG.strap (v:TagG P C)(p: star P=P) : TagG (1-P) (-star C):=by
 have he: P*star C=star C:=by nth_rw 1 [←p]; rw [← star_mul,v.2]
 have hp:star C*P=0:=by rw [←p, ←star_mul,v.1,star_zero]
 exact ⟨by rw [sub_mul,one_mul,mul_neg,he,sub_self],by rw [mul_sub,mul_one,neg_mul,hp,neg_zero,sub_zero]⟩
lemma tag_g (A:Op n) (h:IsStarProjection P) : TagG P ((1-P)*A*P):=by refine ⟨?_,?_⟩; simp only [←mul_assoc,Porth h,zero_mul]; rw [mul_assoc,h.isIdempotentElem.eq]
variable (T:Clad P B W Z K)(Y:TagG P C)
-- exact graph formula including emitted relative log from tilt
abbrev bentT (K B W C:Op n): Op n:= K*(B*W)*C
def creep (K B W C:Op n): Op n:= (1+bentT K B W C)⁻¹*K
abbrev traitP(B K W C:Op n):Op n := laneP B (W*(1+C)) (creep K B W C)
include T Y
lemma storms: Commute P (bentT K B W C):=by
 unfold Commute SemiconjBy bentT; rw [←mul_assoc P,←mul_assoc P,T.tray, mul_assoc _ C P,Y.2] -- tune
lemma brace_r: B*W*(1+C)*P=B*W*P*(1+bentT K B W C) :=by
 simp only [bentT,mul_add,mul_one,add_mul]; rw [mul_assoc _ C,Y.2,←mul_assoc _ _ C,← mul_assoc _ K,T.right,←mul_assoc B,T.helm.isIdempotentElem.eq]
variable (H:IsUnit (1+bentT K B W C))
include H
lemma passage: Commute P (1+bentT K B W C)⁻¹:=by
 let Q:= 1+bentT K B W C; have he:Commute P Q:= Commute.add_right (Commute.one_right _) (storms T Y); change P*_=_*P; rw [show P*Q⁻¹=Q⁻¹*(Q*P)*Q⁻¹ by rw [←mul_assoc Q⁻¹,(live H).2,one_mul],he.eq.symm,mul_assoc Q⁻¹,mul_assoc P,(live H).1,mul_one]
lemma rideK : Clad P B (W*(1+C)) (Z*(1-star C)) (creep K B W C):=by
 let A:=1+bentT K B W C; have he:B*(W*(1+C))*P=B*W*P*A:=by rw [←mul_assoc B]; exact brace_r T Y
 unfold creep; refine ⟨T.proj,T.helm,?_,?_,?_,?_,?_⟩
 · rw [star_mul,star_sub,star_one,star_star,mul_assoc, ←mul_assoc (star Z),T.balance,one_mul,Y.mud]
 · rw [he,← mul_assoc (A⁻¹*K),mul_assoc A⁻¹,T.left,mul_assoc,(storms T Y|>Commute.add_right (Commute.one_right _)).eq,← mul_assoc,(live H).2,one_mul]
 · rw [he, ←mul_assoc (B*W*P*A), mul_assoc _ A,(live H).1,mul_one,T.right]
 · rw [←mul_assoc P,(passage T Y H).eq,mul_assoc,T.tray]
 rw [mul_assoc,T.stem]
lemma thrust_tag : TagG B (traitP B K W C) := ⟨(rideK T Y H).bare,(rideK T Y H).chest⟩
lemma wingPay {O:Op n}(g:Clad (1-P) (1-B) Z W O): traitP B K W C=laneP B W K+star O*C*((1+bentT K B W C)⁻¹*K):=by
 let M:=bentT K B W C; let N:=(1+M)⁻¹; let L:=laneP B W K; let G:= N*K
 have he :=rideK T Y H; have hv : B*(W*(1+C))*G=B:=he.quotaW; have hg:(1+M)*G=K:=by unfold G N M; rw [←mul_assoc,(live H).1,one_mul]
 have ht:star O*C=((1-B)*(1-L)*W)*C:=by rw [← show _=star O from T.sprint g,mul_assoc _ _ C,Y.pen]
 have hp :(1-B)*L=L:=by rw [sub_mul,one_mul,show B*L=0 from T.bare,sub_zero]
 have hk: (1-B)*W*G=L- L*(B*W*C)*G:=by
   rw [show L- L*(B*W*C)*G=L- (1-B)*W*M*G by unfold L laneP M bentT; simp only [←mul_assoc]]
   rw [add_mul,one_mul] at hg; unfold L laneP; rw [←hg,mul_add, mul_assoc ((1-B)*W) M]; abel
 change (1-B)*(W*(1+C))*G=L+star O*C*G; rw [mul_add,mul_one,mul_add,add_mul,hk,ht,mul_sub,mul_one,hp,sub_mul (1-B),sub_mul _ (L*W),sub_mul _ (L*W*C)]; rw [←mul_assoc L,←mul_assoc L,show L*B=L from T.chest,←mul_assoc (1-B)]; abel
end core
end YM.CF.Thera
