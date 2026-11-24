import Bay.D.Cake
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group


open Cake
def grit(x:ℝ):=atRate (-300) x
def tilt(x:ℝ):=wavePay x+grit x
lemma tilt_price: Sugar (-224) tilt:= waveprice.honey ((Cake.bowl _).raise (by norm_num:- (300:ℝ)≤ -224))
lemma tilt_non {x:ℝ}(p:0≤x):0≤tilt x:=by
 unfold tilt wavePay titheB tithe Regis.trend Mi Ei Li thetaB grit atRate; positivity

/-- grip by ALL z (enough to test 4). -/
def Grip (x m:ℝ)(a:ℂ):Prop:= |m|≤Ni x ∧ ∀z:ℂ,‖z‖≤thetaB x →
      ‖1+z*a‖≤Real.exp (z.re*m+tilt x)
variable {x m:ℝ}{a z:ℂ}
def spume(x:ℝ):=thetaB x * Ni x + tilt x
lemma wave_puffs:Sugar (-115) spume:= ((bowl (-200)).stew (bowl 85) (by norm_num)).honey (tilt_price.raise (by norm_num))

lemma Grip.pays (g:Grip x m a)(p:0<x)(h:spume x ≤1):
 ‖a-m‖ ≤ (tilt x+spume x^2) * (thetaB x)⁻¹:=by
 rw[←div_eq_mul_inv,le_div_iff₀ (by unfold thetaB atRate; positivity)]
 let w:=a-(m:ℂ); let t:=thetaB x; have ht:0<t:=by unfold t thetaB atRate; positivity
 by_cases z0:w=0
 · change ‖w‖*t≤_
   rw[z0,norm_zero, zero_mul]; exact add_nonneg (tilt_non p.le) (sq_nonneg _)
 let z:ℂ := (t*‖w‖:ℝ) / w
 have hz: ‖z‖=t:= by
   rw[show ‖z‖=_ from norm_div ..,Complex.norm_real,Real.norm_eq_abs,
     abs_of_nonneg (mul_nonneg ht.le (norm_nonneg _)), mul_div_cancel_right₀ t (norm_ne_zero_iff.mpr z0)]
 let X:=z.re*m+tilt x
 have hv: |X| ≤ spume x:=by
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_nonneg (tilt_non p.le)]
    exact add_le_add (mul_le_mul ((Complex.abs_re_le_norm z).trans_eq hz) g.1 (abs_nonneg _) ht.le) le_rfl
 have hp: Real.exp X ≤ 1+X+spume x^2:=by
    linarith only [ ((abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hv.trans h))).2).trans (sq_le_sq.mpr (hv.trans (le_abs_self _)))]
 have e:= ((Complex.re_le_norm (1+z*a)).trans (g.2 z hz.le)).trans hp

 rw [show a=w+m from (sub_add_cancel ..).symm, mul_add,
     show z*w=(t*‖w‖:ℝ) from div_mul_cancel₀ _ z0, Complex.add_re,
     Complex.one_re,Complex.add_re, Complex.ofReal_re, Complex.mul_re,
     Complex.ofReal_re,Complex.ofReal_im,mul_zero] at e
 unfold X at e
 change ‖w‖*t ≤_
 nlinarith only [e]

lemma gripBack:
 ∀ᶠ x:ℝ in atTop,∀ m a, Grip x m a → ‖a-m‖ ≤ atRate (-23) x:=by
 have hy:= ((tilt_price.honey
   (wave_puffs.bake 2 (by norm_num))).stew (bowl_inv (-200))
      (by norm_num : (-224:ℝ)+ -(-200) ≤ -24)).food (b:= -23) (by norm_num)
 filter_upwards [eventually_gt_atTop (0:ℝ),wave_puffs.serve (by norm_num),hy]
   with x p h t m a u
 exact (u.pays p h).trans t

structure PairGrip (x:ℝ)(m a:ℂ):Prop where
 bill: ∃ r i:ℂ,a=r+Complex.I*i ∧ Grip x m.re r ∧ Grip x m.im i
theorem pairBack:
 ∀ᶠ x:ℝ in atTop,∀ m a, PairGrip x m a → ‖a-m‖ ≤ atRate (-20) x:=by
 filter_upwards [gripBack, ((Cake.bowl (-23)).icing 2).food (b:=-20) (by norm_num)] with x p h m a q
 obtain ⟨r,i,rfl,t,v⟩:=q.bill
 have hm:m=↑m.re+Complex.I*m.im:=by rw[mul_comm,Complex.re_add_im]
 

 rw [hm,add_sub_add_comm,←mul_sub] -- orientation? add_sub_add_comm...
 apply (norm_add_le ..).trans
 rw [norm_mul,Complex.norm_I,one_mul]
 exact (add_le_add (p _ _ t) (p _ _ v)).trans ((two_mul ..).ge.trans h)
end YM.CF.Bay.D
