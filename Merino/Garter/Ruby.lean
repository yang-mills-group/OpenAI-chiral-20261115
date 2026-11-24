import Merino.Garter.Tunic
import YM.SU5.Thin.Glacier.Horizon
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}


open Sleigh Paddled clocks

def lace:ℝ:= 1/50000
abbrev arm(x:ℝ):=x^lace
abbrev pad(x:ℝ):=x^(4*lace)
abbrev lint(x:ℝ):=x^(-4*lace)
abbrev lean(x:ℝ):=x^(-lace)
abbrev tiltB(x:ℝ):=x^(-30*lace)

lemma jip:Paddled (-4*lace) (fun x=>(pad x)⁻¹):=
 (park _).agree ((eventually_gt_atTop (0:ℝ)).mono fun x h=> by
   dsimp only; rw [neg_mul,Real.rpow_neg h.le])
lemma wearDown (q:Clip)(L:ℝ):
 ∀ᶠ x in atTop,lost q L (lint x) (arm x) (pad x) (tiltB x) ≤ lean x:= by
 have a:Paddled lace arm:=park _
 have t:Paddled (4*lace) pad:=park _
 have k:Paddled (-30*lace) tiltB:=park _
 have i:Paddled (-4*lace) (fun x=>nick L (lint x) (arm x) (pad x)):=
    (park _).add ( ((((jip.power 2).mul (lake _)).mul (a.power 4)).scale L).agrees
      (by norm_num [lace]))
 have b:Paddled (2*lace) (fun x=>basisCost L (lint x) (arm x) (pad x)):=
    (i.up (by norm_num [lace]:(-4*lace≤2*lace))).add
     (((a.power 2).scale L).agrees (by norm_num [lace]))


 have m:Paddled (-2*lace) (fun x=>meanTick q L (pad x)):=
    ((((jip.power 2).scale _).mul (lake _)).scale _).up (by norm_num [lace])
 have e:Paddled (-2*lace) (fun x=>sceneTick L (lint x) (arm x) (pad x) (tiltB x)):=by
   unfold sceneTick; dsimp only
   simp_rw [div_eq_mul_inv]
   exact (((b.scale (2:ℝ)).mul i).agrees (b:=-2*lace) (by norm_num [lace])).add
      ((k.mul (((b.power 2).power 2).mul (lake _))).up (by norm_num [lace]))
 have f:Paddled (-2*lace) (fun x=>spikeTick q L (pad x) (tiltB x)):=
   (((((t.power 3).scale _).power 2).scale _).mul k).up (by norm_num [lace])
 exact ((m.add e).add f).pure (by norm_num [lace]) 


lemma velvet (d:ℕ)(h:0<d)(k:ℝ) :
  ∀ᶠ x in atTop,Real.log x*k ≤ ↑(height x / d):=by
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (d*|k|+(d:ℝ))] with x e
 have z:(0:ℝ)<d:=by exact_mod_cast h
 have y:(1:ℝ) ≤ d:=by exact_mod_cast (show 1 ≤ d from h)
 have v:1≤ Real.log x:=y.trans ((le_add_of_nonneg_left (by positivity: 0 ≤ (d:ℝ)*|k|)).trans e)
 have a:(d:ℝ)*k+d ≤ Real.log x:=(add_le_add_left
    (mul_le_mul_of_nonneg_left (le_abs_self k) z.le) _).trans e
 have g:Real.log x * k*d+d ≤ (Real.log x)^2:=by
    nlinarith only [a,mul_le_mul_of_nonneg_left a (zero_lt_one.trans_le v).le, mul_le_mul_of_nonneg_left v z.le]
 have q:(Real.log x)^2 ≤ (height x:ℝ):=Nat.le_ceil _
 have e':height x ≤ height x/d*d +d:=by
   have hm:=Nat.mod_lt (height x) h; have hz:= Nat.mod_add_div (height x) d
   rw [mul_comm]; omega
 have r:(height x:ℝ) ≤ ↑(height x/d)*(d:ℝ)+d:=by exact_mod_cast e'
 apply le_of_mul_le_mul_right _ z
 linarith only [g,q,r]


abbrev tarnish (a:ℝ)(x:ℝ):=Real.exp (-a*↑(height x/10))

lemma dimmed (a:ℝ)(ha:0<a) (b:ℝ): Paddled b (tarnish a) :=by
 apply singers
 filter_upwards [eventually_gt_atTop (0:ℝ),velvet 10 (by decide) (-b/a)] with x p t
 rw [abs_of_nonneg (Real.exp_pos _).le,Real.rpow_def_of_pos p]
 rw [←mul_div_assoc, div_le_iff₀ ha] at t
 exact Real.exp_monotone (by linarith only [t])

lemma button (R:Rules G)(L A a τ:ℝ)(ht:0<τ)(ha:0<a)(L0:0≤L)(pA:0≤A):
 ∀ᶠ x in atTop,∀ β, x/2 ≤ β→β≤2*x→∀ p:BudgetPoint, p.threshold=temp x→
    Offer R p (height x) L β (tarnish a x*A) τ (lint x) (arm x) (pad x)
      (tiltB x) (scant x):=by
 have t:Paddled (4*lace) pad:=park _
 have k:Paddled (-30*lace) tiltB:=park _
 have j:Paddled 1 (fun x=> 2*x):=
   ((park 1).agree (Eventually.of_forall fun x=>Real.rpow_one x)).scale _
 have s:Paddled (-(2/5)) scant:=park _
 have e:Paddled (-(6/5)) (fun x=>L*(2*scant x)^3+tarnish a x*A):=
    ((((s.scale _).power 3).scale _).agrees (b:=-(6/5)) (by norm_num)).add
      (((dimmed a ha (-(6/5))).mul (lake _)).agrees (add_zero _))


 have w:Paddled (-(1/2)+lace/2) (fun x=>temp x+faceCutError R (scant x)):=
    (tempay (by norm_num [lace])).add (((s.power 2).scale _).up (by norm_num [lace]))
 have r:Paddled (1/2) (fun x:ℝ=>Real.sqrt (2*x)):=
    ((park _).scale (Real.sqrt 2)).agree ((eventually_gt_atTop (0:ℝ)).mono fun x _=>by
       dsimp; rw [Real.sqrt_mul (by norm_num),Real.sqrt_eq_rpow x])
 have f:Paddled (-30*lace+(4*lace*2)*2) (fun x=> tiltB x*(L*pad x^2)^2):=
    (k.mul (((t.power 2).scale _).power 2)).agrees (by norm_num)
 have u:Paddled 2 (fun x=>1+tiltB x*(2*x*L)^2):=
    ((lake _).up (b:=2) (by norm_num)).add
      ((k.mul ((j.mul (lake _)).power 2)).up (by norm_num [lace]))
 filter_upwards [
   eventually_gt_atTop (0:ℝ), Work.E01.radiusB_tendsto.eventually_ge_atTop 400,
   (s.lim (by norm_num)).eventually (ge_mem_nhds R.radius),
   ((s.scale 2).lim (by norm_num)).eventually (ge_mem_nhds ht),
   (j.mul e).pure (b:=-4*lace) (by norm_num [lace]),
   (r.mul w).pure (b:=lace) (by norm_num [lace]),
   (f.lim (by norm_num [lace])).eventually (ge_mem_nhds zero_lt_one),
   u.pure (b:=3) (by norm_num), velvet 100 (by decide) 3]
    with x px ox rx ax bx cx fx ux mx b βp βh p hp


 have bp : 0 ≤ b:=(show 0≤ x/2 from by positivity).trans βp
 refine ⟨ox,Real.rpow_pos_of_pos px _,(Real.rpow_pos_of_pos px _).le,(Real.rpow_pos_of_pos px _).le,
     rx,ax,bp, (mul_le_mul_of_nonneg_right βh ?_).trans bx,?_,fx,?_⟩
 · unfold scant tarnish; positivity
 · rw [hp]
   have hc:=G.colorScale_pos; have he:=R.positive; have hx:=Work.E09.temp_pos px
   have N:0 ≤ temp x+faceCutError R (scant x):=by unfold faceCutError; positivity
   exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt βh) N).trans cx
 apply le_trans _ (Real.exp_monotone mx)
 rw [Real.rpow_def_of_pos px] at ux
 apply le_trans _ ux
 have pp:0≤tiltB x:=(Real.rpow_pos_of_pos px _).le
 gcongr

end YM.CF.Merino.Garter

