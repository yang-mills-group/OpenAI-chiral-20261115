import YM.CF.BPress.Bias.Pane
import YM.CF.BPress.Spin.Lock
/-! lem:B-bias. Graph projector identities, still use full torus and a fixed spatial momentum sector.
Quantitative exhaustion: show an approximate split across two bands for the projection W
using commutators with a slow temporal taper on the half-line. No cost on graphAway over all sectors is assumed.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Fir Lat Spin Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Dial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
section Hop
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{c a C:ℝ}{T L P Q A H E Y:Op I}
structure GraphW (P Q L A H E:Op I)(c:ℝ) : Prop extends Pass P Q L A c where -- order
 plane: IsStarProjection H
 corner:H*P=P
 other:H*Q=0
 origin: E*H=E
 upper:H*E=H
 spans:A*E=E
 returns:E*A=A
local notation "F"=> H-P -- avoid sig
local notation "W"=> ramp L P A
namespace GraphW
def road (L E H P:Op I):= L*E*(H-P)
local notation "D"=>road L E H P
variable (g:GraphW P Q L A H E c)
include g
lemma floor : IsStarProjection (H-P):=(g.p.le_iff_sub g.plane).mp ((g.p.le_iff_mul_eq_right g.plane).mpr g.corner)
lemma hi_F:P*H=P:= across g.plane g.p g.corner
lemma em_F: H*L=H-P:=by rw [g.l0,mul_sub,mul_add,g.corner,g.other,mul_one,add_zero]
lemma eF : (H-P)*L=H-P:=by rw [sub_mul,g.em_F,g.toPass.toEmpties.PL,sub_zero]
lemma wF: H*(H-P)=H-P:=by rw [mul_sub,g.corner,g.plane.isIdempotentElem.eq]
lemma roadE : W*D=D:=by
 let K:=rent0 P A; have hx:K*E*(H-P)=E*(H-P):=by
    unfold K; rw [rent0,sub_mul,g.spans, sub_mul,rent1,Trans.beam,pinv,star_mul,g.a.isSelfAdjoint,g.p.isSelfAdjoint]; have he:P*E=P:=by nth_rw 1 [←g.hi_F]; rw [mul_assoc,g.upper,g.hi_F]
    simp only [mul_assoc]; rw [←mul_assoc A E,g.spans,←mul_assoc P E,he,mul_sub P,g.hi_F,g.p.isIdempotentElem.eq,sub_self,mul_zero,mul_zero,mul_zero,sub_zero] -- tune
 unfold road; rw [mul_assoc L E (H-P)]; nth_rw 1 [← hx]; rw [mul_assoc K,←mul_assoc L,← mul_assoc W]; change _ = _; rw [show W*(L*K)=L*K from g.toPass.gate0.continuousSpace,mul_assoc L,←mul_assoc K,hx]
lemma road_F:F*D=F:= by rw [road,←mul_assoc (H-P),← mul_assoc (H-P),g.eF]; nth_rw 1 [←across g.plane g.floor g.wF]; rw [mul_assoc _ H E,g.upper,across g.plane g.floor g.wF,g.floor.isIdempotentElem.eq]
lemma stays_F:D*F=D:=by unfold road; rw [mul_assoc _ (H-P),g.floor.isIdempotentElem.eq]
lemma road_W:D*W=W:=by
 let X:=rent0 P A; have he:(H-P)*X=H*X:=by rw [sub_mul,g.toPass.cold,sub_zero]
 have hx:D*(L*X)=L*X:=by rw [road,mul_assoc,←mul_assoc F,g.eF,he,←mul_assoc,mul_assoc L E,g.origin, show L*E*X=L*X from ?_]; nth_rw 1 [← show A*X=X from g.toPass.ray0]; rw [←mul_assoc,mul_assoc L E,g.returns,mul_assoc L, g.toPass.ray0] -- wrong A*X
 rw [ramp,Trans.beam,←mul_assoc D,hx]
omit g in
lemma commG (y:IsSelfAdjoint Y)(p:Commute Y E)(q:Commute Y A)(h:Trans.Ready c A E): Commute Y (beam A E):=by
 have he:Commute Y (star E):=by have he:=congrArg star p.eq; rw [star_mul,star_mul,y] at he; exact he.symm
 let K:=gram A E; have hk:Commute Y K:=(he.mul_right p).add_right ((Commute.one_right Y).sub_right q); have hp:= live h.live_G; have hh: Commute Y K⁻¹:=by
    unfold Commute SemiconjBy; nth_rw 1 [← one_mul Y,← show K⁻¹*K=1 from hp.2]; rw [mul_assoc K⁻¹,← hk.eq, mul_assoc, mul_assoc,show K*K⁻¹=1 from hp.1, mul_one]
 exact p.mul_right (hh.mul_right he)
lemma commW (y:IsSelfAdjoint Y)(p: Commute Y P)(l:Commute Y L)(b:Commute Y A): Commute Y W:=by
 have hp:= b.sub_right (commG y (b.mul_right p) p g.toPass.gate1); exact commG y (l.mul_right hp) hp g.toPass.gate0

lemma ease (YH:Commute Y H)(YA:Commute Y A)(YE:Commute Y E)(y:IsStarProjection Y)(b:0<a)(h:a • (H*Y) ≤ H*A*H) : ‖E*Y‖≤Real.sqrt a⁻¹:=by
 let X:=E*Y; have hx:=star_right_conjugate_le_conjugate h E; have hy: star Y=Y:=y.isSelfAdjoint; -- left/right ordering?
 have he:X*star X= E*Y*star E:=by unfold X; rw [star_mul,hy,←mul_assoc, mul_assoc E,y.isIdempotentElem.eq]
 have ht:E*H*A*H*star E=A:=by rw [g.origin,g.returns,mul_assoc]; have hG:=congrArg star g.upper; -- actually H*star E=star E
                                    have hg:=congrArg star g.origin; rw [star_mul,g.plane.isSelfAdjoint] at hg; rw [hg]; have hv:=congrArg star g.returns; rwa [star_mul,g.a.isSelfAdjoint] at hv
 have hp:a • (X*star X)≤(1:Op I):=by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,←mul_assoc E,←mul_assoc E (H*A),←mul_assoc E H A,ht,g.origin,← he] at hx; exact hx.trans g.a.le_one
 have h':=CStarAlgebra.norm_le_one_iff_of_nonneg _ (show 0≤ a • (X*star X) from smul_nonneg b.le (mul_star_self_nonneg _)) -- search
 have hh:=h'.mpr hp; rw [norm_smul, Real.norm_of_nonneg b.le,CStarRing.norm_self_mul_star] at hh; apply Real.le_sqrt_of_sq_le; rw [← one_div,le_div_iff₀ b]; change ‖X‖^2 * a ≤ _; linarith -- tune

-- small area bracket forcing global commutator margin
lemma alert (YF:Commute Y F)(YD:Commute Y D)(YW:Commute Y W)(y:IsStarProjection Y)(TF:Commute T F)(TY:Commute T Y)(b:‖W*T-T*W‖ ≤a)(h:‖D*Y‖≤C) : ‖T*(D*Y)-D*Y*T‖≤(1+C)*(a*C):=by
 let B:=D*Y; let M:=T*B-B*T; have hc:0≤C:= (norm_nonneg _).trans h; have ha:0≤a:=(norm_nonneg _).trans b
 have hy:B*Y=B:=by unfold B; rw [mul_assoc,y.isIdempotentElem.eq]
 have hY:Y*B=B:=by unfold B; rw [←mul_assoc,YD.eq,mul_assoc,y.isIdempotentElem.eq]
 have hm:Y*M=M:=by unfold M; rw [mul_sub,←mul_assoc, ←TY.eq,mul_assoc T,hY,←mul_assoc Y B,hY] -- edit
 have vF:F*M=0:=by
    have hp:F*B=F*Y:=by unfold B; rw [←mul_assoc F,g.road_F]; -- tune inside
    unfold M; rw [mul_sub, ← mul_assoc, ←TF.eq, mul_assoc T, hp,← mul_assoc F B,hp,← mul_assoc T,TF.eq,mul_assoc F,TY.eq,mul_assoc F,sub_self]
 have v:D*Y*(M-W*M)= -(W*M):=by
    have he:D*M=0:=by nth_rw 1 [←g.stays_F]; rw [mul_assoc,vF,mul_zero]
    rw [mul_sub, mul_assoc D,hm,mul_assoc D, ←mul_assoc Y,YW.eq,mul_assoc W,hm,←mul_assoc,g.road_W,he,zero_sub]
 have hp:W*B=B:=by unfold B; rw [←mul_assoc,g.roadE]
 have ht: M-W*M= -( (W*T-T*W)*B):=by unfold M; rw [mul_sub,← mul_assoc _ B,hp,sub_mul,mul_assoc,mul_assoc T,hp,mul_assoc W T]; abel
 have hG:‖M-W*M‖≤a*C:=by rw [ht,norm_neg]; exact (norm_mul_le ..).trans (mul_le_mul b h (norm_nonneg _) ha)
 have hQ:‖W*M‖≤ C*(a*C):=by rw [← norm_neg,←v]; exact (norm_mul_le ..).trans (mul_le_mul h hG (norm_nonneg _) hc)
 exact (norm_le_norm_sub_add M (W*M)).trans ((add_le_add hG hQ).trans_eq (by ring))
end GraphW
end Hop
end YM.CF.BPress.Bias
