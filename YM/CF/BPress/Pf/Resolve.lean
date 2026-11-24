import YM.CF.BPress.Pf.Dual
/-! Resolving one-particle Wick projections, explicit formulas that remain support-priceable. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A T L C D X Y U V:Op I}{c d r:ℝ}
def dislodge(P C:Op I):= cutC P C*cc (1-lost P C)⁻¹*cc P -- parse cc ((1-...)⁻¹)
def hue_t(C L X Y:Op I):=L*Y-cc C* (L*X)
lemma adjacent(h:L*C=C*L)(v:cc L=L) : L*cc C=cc C*L:=by
 have he := congrArg cc h; rwa [cc_mul,cc_mul,v] at he
lemma dislodge_spec (h:Bore P C r): P*dislodge P C= dislodge P C ∧ cc P*cc C*dislodge P C= -cc P := by
 let R:= cutC P C; let G:=1-lost P C; let V := dislodge P C
 have he: cc G=star R*R+1-cc P:=by
    have hp:G=R*star R+1-P:=by rw [h.gram_eq]; unfold G; abel -- R tune
    have ht: star R= -cc R:=gapStar h.cuts; rw [hp,cc_sub,cc_add,cc_one,cc_mul,ht,cc_neg,cc_cc]; simp
 have hx: cc G*cc G⁻¹=1:=by rw [←cc_mul,(live h.realG).1,cc_one]
 have hv: cc P*cc G=cc P*(star R*R)+(0:Op I):=by rw [he,mul_sub,mul_add,mul_one,(ccProj h.p).isIdempotentElem.eq,add_sub_cancel_right,add_zero]
 have hy: star R= -(cc P*cc C*P):=by rw [gapStar h.cuts]; unfold cutC; rw [cc_mul,cc_mul,cc_cc] -- check height h.cuts uses cutC explicit
 have ht:cc P*star R=star R:=by
    have ht:= congrArg star h.bump.1; rwa [star_mul,(ccProj h.p).isSelfAdjoint] at ht
 have hp : P*V=V:=by unfold V dislodge; rw [←mul_assoc,←mul_assoc,h.bump.2]
 have hX: star R*V=cc P:=by change star R*(R * cc G⁻¹ * cc P)=_; simp only [←mul_assoc]; rw [show star R*R=cc P*cc G from (by rw [hv, ←mul_assoc,ht,add_zero]), mul_assoc (cc P),hx,mul_one,(ccProj h.p).isIdempotentElem.eq]
 refine ⟨hp,?_⟩; change cc P * cc C*V= _; nth_rw 1 [←hp]; rw [←mul_assoc, show cc P*cc C*P= -star R by rw [hy,neg_neg],neg_mul,hX]

/-- Fix a v-matrix component in the oblique decomposition with P part `P*Z`. It is a primary on A and in ran rent1. -/
def flatten (P A:Op I):= rent1 P A* star (Trans.pinv P (A*P)) * P
lemma landing (h:Pass P Q L A c) : P*flatten P A=P ∧ A*flatten P A=flatten P A:=by unfold flatten; refine ⟨?_,?_⟩ <;> rw [←mul_assoc,←mul_assoc]; rw [h.opens,h.p.isIdempotentElem.eq]; rw [h.ray1]
/-- A puncture on the L-mode residual. -/
def rebound (P L A:Op I):= rent0 P A * Trans.pinv (rent0 P A) (L*rent0 P A)
lemma rebirth (h:Pass P Q L A c) : L*rebound P L A= ramp L P A ∧ P*rebound P L A=0∧ A*rebound P L A=rebound P L A:=by
 unfold rebound ramp Trans.beam; refine ⟨(mul_assoc ..).symm,?_,?_⟩ <;> rw [←mul_assoc]; rw [h.cold,zero_mul]; rw [h.ray0]

-- pack solves any symbol matrix right part; residual left conditions. price independent of input-letter basis. Use L-space lines that may collapse to all modes at P empty.
def capw (P Q L A C X Y:Op I):= hue_t C L (X-flatten P A*X) (Y-flatten Q (1-cc A)*Y)
def seek (P Q L A C X Y:Op I):= dislodge (ramp L P A) C*capw P Q L A C X Y
def find_w (P Q L A C X Y:Op I):= capw P Q L A C X Y+cc C*seek P Q L A C X Y
def fitP (P Q L A C X Y:Op I):= flatten P A * X + rebound P L A * seek P Q L A C X Y
def fitW (P Q L A C X Y:Op I):= flatten Q (1-cc A)* Y + rebound Q L (1-cc A)*find_w P Q L A C X Y

structure Solves (P Q L A C X Y:Op I)(U V:Op I):Prop where
 paid : A*U=U
 joins : cc A*V=0
 gapP : P*U=P*X
 gapQ : Q*V=Q*Y
 rest: hue_t C L (X-U) (Y-V)=0
lemma solution (X:Pass P Q L A c)(H:PairBoard P Q L C)(B:Bore (ramp L P A) C r)(U V:Op I) : Solves P Q L A C U V (fitP P Q L A C U V) (fitW P Q L A C U V) :=by
 let A':=1-cc A; let R:=ramp L P A; let Z:=ramp L Q A'; let E:=capw P Q L A C U V; let w:=seek P Q L A C U V; let z:= find_w P Q L A C U V
 have he:= Dual.dualPass H X; obtain ⟨u₁,u₂⟩:= landing X; obtain ⟨w₁,w₂⟩:=landing he; obtain ⟨a,b,k⟩:= rebirth X; obtain ⟨t,r,g⟩:=rebirth he
 have hL : L*cc C=cc C*L:= adjacent (Dual.LC H) (Dual.L_real H)
 obtain ⟨hP,hM⟩:= dislodge_spec B; have hw:R*w=w:=by unfold w seek; rw [←mul_assoc,hP]
 have hv:L*w=w:=by nth_rw 1 [←hw]; rw [←mul_assoc,X.ramp_L]; exact hw
 have hz: Z*z=z:=by
    have hs:L*E=E:=by unfold E capw hue_t; rw [mul_sub,←mul_assoc,←mul_assoc L,hL,mul_assoc (cc C),←mul_assoc L L,H.toEmpties.r.isIdempotentElem.eq]; -- tune
    have hh:cc R*cc C*w= -cc R*E:=by unfold w seek; rw [←mul_assoc,hM]; -- tune
    unfold Z A'; rw [Dual.rampO H X]; change (L-cc R)*(E+cc C*w)=_; rw [sub_mul,mul_add,mul_add,hs,←mul_assoc L,hL,mul_assoc (cc C),hv,← mul_assoc (cc R),hh,neg_mul]; unfold z find_w; simp [E,w]
 let G:=flatten P A; let T:= rebound P L A; let K:=flatten Q A'; let W:=rebound Q L A'; have hQ:A'*(K*V+W*z)=K*V+W*z:=by rw [mul_add, ←mul_assoc,w₂,←mul_assoc A',g] -- Amet replaced
 have hh: cc A *(K*V+W*z)=0:=by unfold A' at hQ; rw [sub_mul,one_mul] at hQ; exact (sub_eq_self.mp hQ) -- tune
 refine ⟨?_,hh,?_,?_,?_⟩
 · unfold fitP; rw [mul_add,←mul_assoc,← mul_assoc A (rebound _ _ _),u₂,k]
 · unfold fitP; rw [mul_add,←mul_assoc,← mul_assoc P (rebound _ _ _),u₁,b,zero_mul,add_zero]
 · change Q*(K*V+W*z)=_; rw [mul_add,←mul_assoc,w₁,←mul_assoc Q,r,zero_mul,add_zero] -- tune
 change hue_t C L (U-(G*U+T*w)) (V-(K*V+W*z))=0; rw [←sub_sub, ←sub_sub]; unfold hue_t; rw [mul_sub L _ (W*_ ),mul_sub L _ (T*_ ),←mul_assoc L W, ←mul_assoc L T,a,t,mul_sub (cc C),hw,hz]; change L*(V-K*V)-z-(cc C*(L*(U-G*U))-cc C*w)=0; rw [show z=L*(V-K*V)-cc C*(L*(U-G*U))+cc C*w from rfl]; abel
end YM.CF.BPress.Pf
