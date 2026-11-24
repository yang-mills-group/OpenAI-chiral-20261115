import YM.CF.BPress.Calendar.Stip
/-! Severe suppressions and entropy.Lc^3 factors included. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange Peel Spine Mosaic
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}
namespace Around
open Currencies Pulse Manna Manna.Budget House Huon Stripe Contour Rates
variable (G:Curb f E)
local notation "cV"=> K.top.clip
local notation "wD"=> (ellK X)
def Bcap(x:ℝ) := 2*(estate 29*(volume_k G x^3*depth X x):ℕ)*(value E).price + Pilot.costY 0 (g x) (volume_k G x) (ellK X) X.z.M -- tune casting add Border.S
lemma costp(x:ℝ): 0 ≤ Bcap G x :=by unfold Bcap Pilot.costY; positivity [(value E).bought] -- ensure definitions accessible
lemma uSever : 0<sever cV f.κ (ellK X):= sever_pos _ f.bore _ _ (ell_pos X) -- notation issues omitted x etc
lemma area_pl : PL (Bcap G):=by
 have hm:PL fun i=>(volume_k G i:ℝ):= G.PL; unfold Bcap; apply PL.add; · simp only [Nat.cast_pow,Nat.cast_mul]; exact ((PL.const 2).mul ((PL.const _).mul ((hm.pow 3).mul (dp (X:=X))))).mul (PL.const _) -- tune notations push_cast depth reducible
 have he : PL (fun i=>|Real.log (g i)|):= by
    refine (PL.log.mul (PL.const (1/2))).mono <| (eventually_gt_atTop 0).mono fun y p=> (?_ ); have hp:= Real.log_pow (g y) 2; rw [gscale p.le, Real.log_inv] at hp; have he:Real.log (g y)= -(Real.log y)*(1/2):= by norm_num at hp; linarith
    rw [he, neg_mul, abs_neg,abs_abs]
 unfold Pilot.costY; simp_rw [Nat.cast_mul,Nat.cast_pow]; exact (((PL.const _).mul (hm.pow 3)).mul (PL.const _)).mul he
-- $choose exponent from Θ_Q list at each y$; no additional delays before proving its eventual.
def beams(x:ℝ):= X.strength/16*(volume_k G x:ℝ)^3
lemma bp : 0< beams G x:=by unfold beams; positivity [(G.width x).property,X.wage]
def RR(x:ℝ):=reward (ellK X) f.κ x K.top.clip -- `G` not deps? type no G. prefer f explicit
lemma ss : 0<RR (f:=f) x:=by unfold RR reward; have ht:=uSever (f:=f); positivity [drift_pos x]
def boss(x:ℝ):Rates:=⟨beams G x,Bcap G x,RR (f:=f) x,(bp G).le,costp G x,ss.le⟩
-- normalized entropy slack. choose tiny α margin. 
def alpha :ℝ:=min 1 (lavish fixedR/4)
lemma tiny : 0<alpha:= lt_min one_pos (div_pos (lavish_pos _) (by norm_num))
lemma severed(r u:ℝ→ℝ)(p:∀ x,0<u x)(f:PL r)(h:NPL (fun i=>(u i)⁻¹)): NPL fun i=> Real.exp (r i - u i):=by
 have hx: NPL fun i=> (r i + (small i:ℝ))*(u i)⁻¹:= (f.add small_PL).times h
 refine (rate_Exp (t:=1) zero_lt_one).mono ?_; filter_upwards [hx.drop.eventually (ge_mem_nhds zero_lt_one)] with x g; change _*_≤ _ at g; rw [← div_eq_mul_inv] at g; have he:= (div_le_one (p x)).1 g; rw [one_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; linarith -- tune `he` maybe Lean reserved
lemma hurry : NPL fun i=> (RR (f:=f) i)⁻¹ :=by
 unfold RR reward; simp_rw [mul_inv_rev]; exact NPL.mul (show NPL fun i=> (drift i^2)⁻¹ from by simp_rw [← Real.rpow_two]; exact npl_drift _ zero_lt_two) (PL.const _) -- maybe mult reassoc
abbrev paceB(y:ℝ):= (1/4:ℝ)*heigh y^2
lemma pq(x:ℝ):0<paceB x:=by unfold paceB; positivity [heigh_pos x]
lemma psl : NPL fun i=>(paceB i)⁻¹:=by unfold paceB; simp_rw [mul_inv_rev,←inv_pow]; exact (heigh_npl.mul heigh_npl.pl|>.mono (by filter_upwards with x; show |(heigh x)⁻¹^2|≤ _; rw [sq])).mul (PL.const _) -- tune simp.slow
abbrev HumK(x:ℝ):= HumCost (ellK X) (volume_k G x) x
lemma mk_earn (D:ℝ→ℝ)(h:PL D): NPL fun i=> Real.exp (D i)*HumK G i:=by
 have he:= (severed _ _ pq h psl); have hm:NPL fun i=> ((volume_k G i:ℝ)^3*hBound (ellK X))*Real.exp (D i-paceB i):= (((G.PL.pow 3).mul (PL.const _))).times he; refine hm.mono (Eventually.of_forall fun y=> ?_); unfold HumK HumCost paceB
 rw [sub_eq_add_neg,Real.exp_add,neg_mul]; exact le_of_eq (congrArg abs (by ring))
-- local compiler performance
lemma HumPL : NPL (HumK G):=by simpa only [Real.exp_zero,one_mul] using mk_earn G (fun _=>0) (PL.const 0)
lemma odds0 (S:Side): (0:ℝ)< 2*(10:ℝ)^S.val:=by positivity
abbrev breeze(x:ℝ):= (2:ℝ)*10^(volume_k G x^3)
lemma odds(x:ℝ):0<breeze G x:=by unfold breeze; positivity
abbrev esteem (x:ℝ):= Real.log (breeze G x)
lemma aboveF : PL (esteem G):=by unfold esteem breeze; simp_rw [Real.log_mul (by norm_num: (2:ℝ)≠0) (pow_ne_zero _ (by norm_num: (10:ℝ)≠0)), Real.log_pow, Nat.cast_pow]; exact (PL.const _).add ((G.PL.pow 3).mul (PL.const _))
abbrev hch(x:ℝ):=Bcap G x + esteem G x+ kroot*(esteem G x-Real.log alpha)
lemma hch_pl : PL (hch G):= ((area_pl G).add (aboveF G)).add ((PL.const _).mul ((aboveF G).add (PL.const (-Real.log alpha)))) -- tune sub
lemma hot_S : NPL fun x=>Real.exp (Bcap G x)*breeze G x*(Real.exp (-RR (f:=f) x)+HumK G x)*(breeze G x/alpha)^kroot:=by
 let T (x):= hch G x; have hu := (severed _ _ (fun _=> ss (f:=f)) (hch_pl G) hurry); have ht:= mk_earn G T (hch_pl G); apply (hu.add ht).mono; refine Eventually.of_forall fun x=>?_ ; let RP:=RR (f:=f) x; let H:= esteem G x; let C:=Bcap G x; change |Real.exp C*breeze G x*(Real.exp (-RP)+HumK G x)*(breeze G x/alpha)^kroot| ≤ _; rw [mul_assoc _ _ (_^kroot), mul_comm (_+_) (_^kroot),←mul_assoc]; -- `hu.add ht` expression on abs; need simp
 have he:Real.exp C*breeze G x*(breeze G x/alpha)^kroot=Real.exp (T x):=by unfold T hch; rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul, Real.exp_sub, Real.exp_log (odds G x), Real.exp_log tiny] -- tune abbrev
 change _ ≤ |Real.exp (T x-RP)+Real.exp (T x)*HumK G x|; rw [he,mul_add,sub_eq_add_neg,Real.exp_add (T x) (-RP)]
lemma breeze_l : Tendsto (volume_k G) atTop atTop:=by
 suffices Tendsto (fun x=>(volume_k G x:ℝ)) atTop atTop from tendsto_atTop.mpr fun i=> (this.eventually_ge_atTop (i:ℝ)).mono (fun j p=> Nat.cast_le.mp p)
 refine tendsto_atTop_mono' _ ((Pocket.hobby G).mono fun i p=>?_ ) lscale_late; rw [←small_l]; have ht:=p.thick; unfold spanN at ht; exact Nat.cast_le.mpr (by unfold volume_k; omega) -- tune implicit f
lemma cool_P : Tendsto (fun x=> coolCap (boss G x)) atTop (𝓝 0):=by
 have ht: Tendsto (beams G) atTop atTop:= ((tendsto_pow_atTop (by omega : (3:ℕ)≠0) |>.comp (tendsto_natCast_atTop_atTop.comp (breeze_l G)))).const_mul_atTop (show 0<X.strength/16 from (by positivity [X.wage])); simpa only [mul_zero,Function.comp_apply,coolCap,boss] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (8:ℝ) -- tune congr.
end Around
end YM.CF.BPress.Calendar
