import Velour.Escutcheon.Leaves
import Velour.Sequins.Shell
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}{b:Axis}(h:a≠b)(A:S.Tiles h)
def stride (a b:Axis)(t v:ℝ) :E4:=t • basis a + v • basis b

namespace Livery
variable (k:ℝ)(c:|k|<1)
def streamOp (z:ℂ):H.Op:=
 if z.im=0 then M S (stride a b z.re (k*z.re)) else
    foil S (silk h) A 0 (-I*z) ((k:ℂ)*z)
local notation "ℜ"=>streamOp h A k
local notation "P"=>foil S (silk h) A 0

lemma tval(t v:ℝ): M S (stride a b t v)= S.edge t * albe S (silk h) v:=by
   have i:=bpay S (silk h) t v 0
   rw [show S.U 0=1 from S.uZero,mul_one] at i
   change M S ((0:E4)+v • basis b+t • basis a)=_ at i
   rw [zero_add,add_comm] at i; exact i
lemma norm_realM(x:E4) : ‖M S x‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
 intro v

 rw [one_mul]; exact (S.unit.unitary _ _).le

local notation "High"=>{z:ℂ|0<z.im}
local notation "Sky"=>{z:ℂ|0≤z.im}

include c
private lemma light (z:ℂ)(t: z ∈ High): Wheel (-I*z) (k*z):=by
   show |((k:ℂ)*z).im|<(-I*z).re
   have p:0<z.im:=t
   simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,mul_re,neg_re,I_re,neg_zero,
         abs_mul,abs_of_pos p,neg_im,I_im,neg_mul,one_mul,zero_sub,neg_neg]
      using (mul_lt_mul_of_pos_right c p)
local notation "ν"=>duration 1
private lemma lightT (z:ℂ)(t:z∈Sky): Wheel (-I*z+ν) (k*z):=by
   show |((k:ℂ)*z).im|<(-I*z+ν).re
   have p:0≤z.im:=t
   have h:=mul_le_mul_of_nonneg_right c.le p
   simp [duration,abs_mul,abs_of_nonneg p]
   linarith
lemma streamNorm(z:ℂ)(t:z∈Sky) :‖ℜ z‖≤4:=by
   unfold streamOp
   split
   · exact norm_realM _ |>.trans (by norm_num)
   rename_i p
   exact fol_norm S (silk h) A _ _ (light k c z ((show 0≤z.im from t).lt_of_ne (Ne.symm p)))

omit c in
lemma streamR (v:ℝ): ℜ v=M S (stride a b v (k*v)):=by simp [streamOp]

lemma streamDamp(z:ℂ)(t:z∈Sky):
 ℜ z * S.E 1=P (-I*z+ν) (k*z):=by
 by_cases v:z.im=0
 · obtain ⟨x,rfl⟩ : ∃x:ℝ,(x:ℂ)=z:=⟨_,Complex.ext rfl (v.symm)⟩
   have y:Wheel ν 0:=by change |(0:ℂ).im|<_ ;simp [duration]
   have e:Wheel (ν+sideways x) 0:=by change |(0:ℂ).im|<_; simp [duration]
   have r:(-I*x)=sideways x:=by unfold sideways; ring
   rw [streamR, r,add_comm, ←ofReal_mul, ←zero_add (↑(k*x):ℂ),
    hillside S _ A _ _ _ _ e, rolling S _ A _ _ _ _ y, mul_assoc, ← tval h,
    ← fol_fix S _ A]
   exact holds S _ _ _ _ _ y _
 have p:0<z.im:=(show 0≤z.im from t).lt_of_ne (Ne.symm v)
 rw [streamOp,if_neg v,(brassup S _ _ _ _ _ _ (light k c z p) zero_lt_one)]
#print axioms streamDamp

lemma streamA: AnalyticOnNhd ℂ ℜ High:=by
  intro z p
  refine (hol_whole S _ A 0 _ (fun y=> -I*y) (fun y=> (k:ℂ)*y)
    (analyticAt_const.mul analyticAt_id)
    (analyticAt_const.mul analyticAt_id)
    (light k c z p)).congr ?_
  filter_upwards [(continuous_im.continuousAt (x:=z)).eventually (lt_mem_nhds (show 0<z.im from p))]
    with w y
  exact (if_neg (Ne.symm y.ne):ℜ w=_).symm

lemma streamC(a':H): ContinuousOn (fun z=>ℜ z (S.E 1 a')) Sky:=by
 let F: H.Op →L[ℂ] H:=ContinuousLinearMap.apply ℂ H.space a'
 let D(z:ℂ):= P (-I*z+ν) (k*z)
 have y: AnalyticOnNhd ℂ D Sky:= fun z p=>hol_whole S _ A 0 _ _ _
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    (analyticAt_const.mul analyticAt_id) (lightT k c z p)
 refine (F.continuous.comp_continuousOn y.continuousOn).congr ?_
 intro z p
 exact DFunLike.congr_fun (streamDamp h A k c z p) _


lemma streamY(y:H): ContinuousOn (fun z=> ℜ z y) Sky:=by
 apply Metric.continuousOn_iff.mpr
 intro z p ε v
 obtain ⟨_,⟨a,rfl⟩,r⟩ := Metric.mem_closure_iff.mp (S.whole 1 y) (ε/12) (by positivity)
 have f(t:ℂ)(y':t∈Sky): dist (ℜ t y) (ℜ t (S.E 1 a))<ε/3:= by
     rw [dist_eq_norm,←map_sub]
     refine ((ℜ t).le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right
       (streamNorm h A k c t y') (norm_nonneg _)).trans_lt ?_)
     have i:= dist_eq_norm y (S.E 1 a); linarith [i]
 obtain ⟨δ,g,i⟩:=Metric.continuousOn_iff.mp (streamC h A k c a) z p (ε/3) (by positivity)
 refine ⟨δ,g,fun w hw j=>?_⟩
 have :=i w hw j
 linarith [f w hw,f z p,dist_triangle (ℜ w y) (ℜ w (S.E 1 a)) (ℜ z y),
     dist_triangle (ℜ w (S.E 1 a)) (ℜ z (S.E 1 a)) (ℜ z y),
     dist_comm (ℜ z y) (ℜ z (S.E 1 a))]

section
omit c
def chase (u v:H)(p:E4):=inner ℂ u (M S p v)
end
variable (u v u' v':H)
local notation "Y"=>chase (S:=S) u v
local notation "Z"=>chase (S:=S) u' v'
include A
lemma traceLine
 (p:E4){r:ℝ}(e:0<r)(q:∀t:ℝ,|t|≤r→Y (stride a b t (k*t)+p)=Z (stride a b t (k*t)+p)):
 ∀t:ℝ,Y (stride a b t (k*t)+p)=Z (stride a b t (k*t)+p):=by
 let F(x y:H)(z:ℂ):= inner ℂ x (ℜ z (M S p y))
 let G:ℂ→ℂ:= F u v-F u' v'
 have R(t:ℝ): G t=0 ↔ Y (stride a b t (k*t)+p)=Z (stride a b t (k*t)+p):=by
    simp only [G,Pi.sub_apply,F,streamR,chase,← tgo,sub_eq_zero]
    rfl
 have cont:ContinuousOn G Sky :=
    (continuousOn_const.inner (streamY h A k c _)).sub (continuousOn_const.inner (streamY h A k c _))
 have an(x y:H)(z:ℂ)(p':z∈High): AnalyticAt ℂ (F x y) z:=
    ((((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space (M S p y))).analyticAt _).comp
        (streamA h A k c z p'))
 have m:=Velour.hem_identical cont (fun z y=>(an u v _ y).sub (an u' v' _ y)) e (fun x t=>(R x).mpr (q _ t))

 intro t
 have fi:(G ↑t)=0:=by
   let d:ℝ→ℂ:=fun s=>t+s*I
   have p:d 0=t:=by simp [d]
   have x:Tendsto d (𝓝[>] 0) (𝓝[Sky] t):=by
     refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
     · rw [←p]; exact (show Continuous d from by unfold d;fun_prop).continuousAt.continuousWithinAt
     filter_upwards [self_mem_nhdsWithin] with w y
     show 0≤(d w).im; simpa [d] using (show 0<w from y).le
   refine tendsto_nhds_unique_of_eventuallyEq
       ((cont (↑t:ℂ) (show 0≤(↑t:ℂ).im by simp)).tendsto.comp x) tendsto_const_nhds ?_
   filter_upwards [self_mem_nhdsWithin] with y e
   exact m (d y) (by simpa [d] using (show 0<y from e))
 exact (R t).mp fi

#print axioms traceLine

omit c
lemma plumeLift (d:ℝ)
 (q:∀p:E4,|p a|≤1 → d≤|p b|→Y p=Z p):
     Y 0=Z 0:=by
 have y(t v:ℝ)(e:d≤|v|):
    Y (stride a b t v)=Z (stride a b t v):=by
     let p:=stride a b 0 v
     have e'(t):stride a b t (0*t)+p=stride a b t v:=by simp [stride,p]
     rw [← e' t]
     apply traceLine h A 0 (by norm_num) _ _ _ _ p (show (0:ℝ)<1 from zero_lt_one)
     intro w x
     rw [e']
     apply q
     · simpa [stride,h]
     simpa [stride,h.symm]
 let i:=2*(|d|+1)
 let P0(t:ℝ):=stride a b t ((1/2)*t)
 have f(t):P0 t+P0 i=P0 (t+i):=by
    simp only [P0,stride,mul_add,add_smul]; abel
 have t_r:P0 (-i)+P0 i=0:=by rw [f];simp [P0,stride]
 rw [←t_r]
 apply traceLine h A (1/2) (by norm_num) _ _ _ _ (P0 i) (show (0:ℝ)<1 from zero_lt_one)
 intro t s
 rw [f]
 apply y
 unfold i
 linarith [le_abs_self d,le_abs_self ((1/2:ℝ)*(t+2*(|d|+1))), (abs_le.mp s).1]
#print axioms plumeLift
