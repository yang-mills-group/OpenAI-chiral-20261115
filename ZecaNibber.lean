import ZecaQuote
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Moment
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "R"=>saucer S
abbrev notch (D:Moment H):Moment H:=⟨D.n+1,R*D.op-D.op*R⟩
local notation "A" n:max t:max=> Par S n t
lemma slimP {s v:ℝ≥0} (p:0<s)(q:0<v)(m n:ℕ):
 Par S m s*Par S n v=Par S (m+n) (s+v):= by
 let f:=linkP S m n 0 p q
 rw [S.eZero,show ContinuousLinearMap.id ℂ H.space=1 from rfl,mul_one, add_zero] at f
 exact f

lemma stein {t:ℝ≥0} (p:0<t): deriv S.F (duration t)= A 0 t-A 1 t:=by
  have l:R*looper S (duration t)=R*A 1 t:=by
     have g:=K_E S 1 t p
     have h:R*A 1 t=S.E t:= (show Cache S 1=R from (by unfold Cache;rw [pow_one])) ▸ g
     rw [dorsal S _ (dur.mpr p),S.roots_heat p,h]
  have g:looper S (duration t)=A 1 t:=by ext1 x;exact paranoid S (DFunLike.congr_fun l x)
  change S.F _-_= _ at g
  rw [←g,show Par S 0 _=S.F _ from rfl,sub_sub_cancel]

lemma thinLR {t:ℝ≥0}(p:0<t)(n:ℕ):
 R*A (n+1) t=A n t ∧ A (n+1) t*R=A n t:=by
 have y:R*A (n+1) t=A n t:=by
   suffices Cache S n*(R*A (n+1) t)= Cache S n*A n t by ext1 x; exact cache_I S n (DFunLike.congr_fun this x)
   rw [←mul_assoc,show Cache S n*R=Cache S (n+1) from (pow_succ ..).symm]
   exact (K_E S _ t p).trans (K_E S n t p).symm
 constructor
 · exact y
 rw [←star_inj,star_mul,show star (A _ _)=_ from para_adj S (n+1) t p,
       show star R=R from saucer_sym S,y]
 exact (para_adj S n t p).symm

lemma billNotch (D:Moment H) (t s:ℝ≥0)(p:0<t)(q:0<s):
    deriv S.F (duration t)*D.cost S t s*S.E s -
       S.E t * D.cost S t s * deriv S.F (duration s)=
       (notch S D).cost S (t+t) (s+s):=by
 let n:=D.n
 rw [stein S p, stein S q,show S.E t=A 0 t from (S.roots_heat p).symm,
        show S.E s=A 0 s from (S.roots_heat q).symm]
 change (_ - _)*(A n t*D.op*A n s)*A 0 s -
      A 0 t*(A n t*D.op*A n s)*(A 0 s-A 1 s)=
     A (n+1) (t+t)*(R*D.op-D.op*R)*A (n+1) (s+s)

 have e(i j:ℕ):
     A i t*(A n t*D.op*A n s)*A j s=A (n+i) (t+t)*D.op*A (n+j) (s+s):=by
    rw [← mul_assoc _ _ (A n s),mul_assoc _ (A n s),
        ← mul_assoc _ _ D.op, slimP S p p,slimP S q q,add_comm i n]
 rw [sub_mul,sub_mul,mul_sub,e,e,e,add_zero,mul_sub,sub_mul]
 have v:=add_pos p p; have w:=add_pos q q
 rw [←mul_assoc _ R,(thinLR S v n).2,mul_assoc (A _ _) (D.op*R),mul_assoc D.op,
      (thinLR S w n).1]; simp only [mul_assoc];abel

open Boundary Probe
abbrev newTick (a:Axis):Test4 →L[ℂ] Test4 := -εpref a
variable (D:Moment H)(g:Test4)
lemma haddr : valise S (R*D.op-D.op*R) g=R * valise S D.op (newTick a g)*R:=by
 have e:∀ p,Commute (M S p) R:=fun _=>(tread ..).symm
 have negA(W:H.Op):valise S (-W) g= -valise S W g:=by rw [← neg_one_smul ℂ W,vscale,neg_one_smul]
 rw [sub_eq_add_neg,vadd,negA,overlap _ _ _ _ e,overlap_R _ _ _ _ e,
        newTick,_root_.neg_apply,
        show valise S D.op (- (εpref a g))= -_ from map_neg (barren S D.op) (εpref a g),
        orion S D.op g,mul_neg,neg_mul]
 abel
lemma visible : (notch S D).field S g=D.field S (newTick a g):=by
 ext1 x;apply Subtype.ext; apply cache_I S (D.n+1)
 let t:=D.n
 change Cache S (D.n+1) (ℑ S _ g (D.n+1) x).val= Cache S (D.n+1) (ℑ S _ _ _ x).val
 rw [native,haddr]
 have e:R (hall S (D.n+1) x)=hall S D.n x:=by
   apply cache_I S D.n
   rw [releases,show Cache S _ (R _)=_ from DFunLike.congr_fun (pow_succ R D.n).symm _]
   exact releases S (D.n+1) x
 change R (valise S _ _ (R _))=_
 rw [e, ←native]
 exact DFunLike.congr_fun (pow_succ' R D.n).symm _
#print axioms visible
