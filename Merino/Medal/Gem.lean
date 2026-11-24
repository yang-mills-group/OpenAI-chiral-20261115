import Merino.Medal.Gilt
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Medal
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Vale RG
open scoped Matrix Matrix.Norms.L2Operator Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Py.Rate Py.Rate.LocalLimit Preparation
open Skye Scree Buffered Afterglow MeasureTheory
open Yoke Papal Garter Gleam
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))


open Finset Cuff Hem Fock StepIn Lamour.Bridge.Celeste.Clock.Fabric Py.Rate.Pannier
open Lamour.Bridge.Celeste.Clock
open Journey
variable {n:Side}
open CF.Pannier.Chancel
open Reed
open Diadem Sleigh clocks Paddled
abbrev wp (x:ℝ):=Real.exp ((Real.log (Real.log x))^2)
/-- ticks in gauge lattice steps from origin plane in axis3. -/
def Strut (x:ℝ)(t:ℕ):=wp x^99 ≤ t∧(t:ℝ) ≤wp x^102
def diameter (q:ℝ):=4*⌈wp q^102⌉₊
def hike (B:ℕ)(q:ℝ):=B*⌈wp q^100⌉₊


lemma spire(x:ℝ):1≤wp x:=Real.one_le_exp (sq_nonneg _)
lemma strut_d {x t}(h:Strut x t): 1 ≤ t ∧4*t≤diameter x:=
 ⟨by have := (one_le_pow₀ (spire x) (n:=99)).trans h.1; exact_mod_cast this,
   Nat.mul_le_mul_right _ le_rfl|>.trans <|Nat.mul_le_mul_left 4
     (by have := h.2.trans (Nat.le_ceil _); exact_mod_cast this)⟩

lemma peaks : Tendsto wp atTop atTop:=Real.tendsto_exp_atTop.comp <|
   (tendsto_pow_atTop (by decide :2≠0)).comp <|(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
lemma haze : ∀ᶠ x in atTop,↑(height x)≤wp x:=by
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 3] with x p q
 change 3≤Real.log (Real.log x) at q
 have h:(Real.log x)^3≤wp x:=by
   have z:= Real.exp_monotone (show (3:ℕ)*Real.log (Real.log x) ≤ (Real.log (Real.log x))^2 by norm_num; nlinarith)
   rwa [Real.exp_nat_mul,Real.exp_log (show 0<Real.log x by linarith)] at z
 exact (Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le.trans <|
    le_trans (by nlinarith only [p, mul_nonneg (sub_nonneg.mpr p) (sq_nonneg (Real.log x)),sq_nonneg (Real.log x-1)]) h


lemma hike_yes {B:ℕ}(o:0<B): ∀ᶠ x in atTop,Strut x (hike B x):=by
 filter_upwards [peaks.eventually_ge_atTop (2*B:ℝ)] with x h
 have a:=spire x
 constructor
 · refine (pow_le_pow_right₀ a (by decide:99≤100)).trans <| (Nat.le_ceil _).trans ?_
   exact_mod_cast Nat.le_mul_of_pos_left _ o
 have u:0<wp x:=zero_lt_one.trans_le a
 unfold hike; push_cast
 refine le_trans (mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one
    (show 0 ≤wp x^100 from pow_nonneg u.le _)).le (Nat.cast_nonneg B)) ?_
 rw [show (102:ℕ)=100+2 by rfl,pow_add]
 nlinarith only [one_le_pow₀ a (n:=100),
  mul_nonneg (sub_nonneg.mpr (one_le_pow₀ a (n:=100))) (Nat.cast_nonneg (α:=ℝ) B),
  mul_le_mul_of_nonneg_left (h.trans
      (by simpa using (pow_le_pow_right₀ a (show 1≤2 by decide):wp x^1≤wp x^2)))
      (pow_nonneg u.le 100)]


lemma offPeak (B:ℕ):
 ∀ᶠ x in atTop,∀ t,Strut x t→ (2*(shellC (height x)+B)+4)^2 ≤ t:=by
 filter_upwards [haze,peaks.eventually_ge_atTop (20+B:ℝ)]
   with x h u t b
 have : (↑(2*(shellC (height x)+B)+4:ℕ):ℝ)≤wp x^2:=by
    unfold shellC; push_cast; nlinarith [(show (0:ℝ)≤B from Nat.cast_nonneg B)]
 have v:= (pow_le_pow_left₀ (Nat.cast_nonneg _) this 2).trans <|
    (show (wp x^2)^2 ≤wp x^99 by rw [←pow_mul]; exact pow_le_pow_right₀ (spire x) (by decide))
 exact_mod_cast v.trans b.1

abbrev shiver:ℝ:=lace/16

open Pressure.Worth
lemma twilight:Paddled (-40*lace) dusk:=by
 have h: Paddled r_meter meterC := (park r_meter).agree <| (eventually_gt_atTop (0:ℝ)).mono fun x v=>by
    dsimp only [meterC,BProof.coin]
    simp [Real.rpow_def_of_pos v]
 exact (h.agrees (by norm_num [r_meter,lace]) (b:=-40*lace)).scale 12 |>.add
   ((park _).up (by norm_num [lace]))

lemma twilightPos (x:ℝ)(p:0<x):0<dusk x:=by unfold dusk meterC BProof.coin oar; positivity



lemma width : Paddled shiver (fun x:ℝ=>↑(diameter x)):=by
 have p:0<shiver:=by norm_num [shiver,lace]
 have h:Paddled shiver (fun x=>wp x^102):= singers <|
  (Vac.Numbers.cost (↑(102:ℕ)) shiver p).mono fun x h=>by
    rw [abs_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
    simpa only [Real.rpow_natCast,Vac.Numbers.P] using h
 apply ((h.add ((lake 1).up p.le)).scale 4).caps
 filter_upwards with x
 have a:=Nat.ceil_lt_add_one (pow_nonneg (show 0≤wp x from (Real.exp_pos _).le) 102)
 rw [abs_of_nonneg (Nat.cast_nonneg (diameter x))]
 apply le_trans _ (le_abs_self _)
 unfold diameter; push_cast
 linarith only [a]
lemma tariff_low(K:Calibration): Paddled (4*shiver)
   (fun x=>Diadem.tariff K (diameter x)):=by
 have u:0≤ shiver:= by norm_num [shiver,lace]
 refine (((((width.add ((lake ↑(addgap K)).up u)).scale 4).power 4).agrees
    (by push_cast;ring)).agree ?_)
 exact Eventually.of_forall fun x=>by unfold Diadem.tariff; push_cast; rfl


lemma harvest (K:Calibration)(C:ℝ):
 ∀ᶠ x in atTop,
   tiltB x * (C+2) ≤ 1 ∧ lean x≤1 ∧ (C+2)^2*tiltB x ≤ lean x∧
   3*(dusk x*Diadem.tariff K (diameter x)) ≤ tiltB x*lean x :=by
 have z:Paddled (-30*lace) tiltB:=park _
 have y:Paddled (-lace) lean:=park _
 have h:=z.scale (C+2)
 filter_upwards [eventually_gt_atTop (0:ℝ),
   h.pure (b:=0) (by norm_num [lace]),y.pure (b:=0) (by norm_num [lace]),
   (z.scale ((C+2)^2)).pure (b:=-lace) (by norm_num [lace]),
   ((twilight.mul (tariff_low K)).scale 3).pure (b:=-30*lace+-lace)
      (by norm_num [shiver,lace])] with x p u a b w
 rw [Real.rpow_add p] at w; rw [Real.rpow_zero] at a u
 exact ⟨(mul_comm ..).trans_le u,a,b,w⟩

/-- Trap at the scale of the Wick prediction. -/
lemma melt (δ:ℝ)(h:0<δ):
  ∀ᶠ x in atTop,∀ t,Strut x t →
     (↑(2*t:ℕ):ℝ)^8*(3*lean x) ≤ δ :=by
 filter_upwards [eventually_gt_atTop (0:ℝ),
   (((width.power 8).mul ((park (-lace)).scale 3)).lim
     (by norm_num [shiver,lace])).eventually (ge_mem_nhds h)] with x p u t v
 apply le_trans _ u
 apply mul_le_mul_of_nonneg_right _ (by unfold lean; positivity)
 exact pow_le_pow_left₀ (by positivity) (by
    exact_mod_cast (Nat.le_trans (by omega:2*t≤4*t) (strut_d v).2)) _

lemma above (M:ℕ):∀ᶠ x in atTop, ∀ t,Strut x t → M≤t:=by
 filter_upwards [peaks.eventually_ge_atTop ↑M] with x p t h
 exact_mod_cast p.trans <|(show wp x≤wp x^99 by
    simpa using (pow_le_pow_right₀ (spire x) (by decide:1≤99))).trans h.1

end YM.CF.Merino.Medal

