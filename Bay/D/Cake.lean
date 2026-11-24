import Bay.D.Ivora
import YM.SU5.Thin.Glacier.Responsive
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

open Sleigh Paddled
abbrev thinRate (a:ℝ):=a/200000
abbrev atRate(a x:ℝ):ℝ:=x^(thinRate a)
abbrev bWindow:=atRate 20
abbrev thetaB:=atRate (-200)

open Next.Rank.Spindle
-- powers in PRESSURE units 200000
namespace Cake
variable {a b c d:ℝ}{F G:ℝ→ℝ}
def Sugar(a:ℝ)(F:ℝ→ℝ):Prop:=Paddled (thinRate a) F
theorem Sugar.raise(h:Sugar a F)(l:a≤b):Sugar b F:= Paddled.up h (div_le_div_of_nonneg_right l (by norm_num))
lemma Sugar.honey (f:Sugar a F)(g:Sugar a G):Sugar a (fun x=>F x+G x):=Paddled.add f g
lemma Sugar.stew {d:ℝ}(f:Sugar a F)(g:Sugar b G)(v:a+b≤d):
   Sugar d (fun x=>F x*G x):= (Paddled.mul f g).up (by unfold thinRate; linarith)
lemma Sugar.bake(f:Sugar a F)(n:ℕ)(v:a*(n:ℝ)≤b):
   Sugar b (fun x=> (F x)^n):= (Paddled.power f n).up (by unfold thinRate; nlinarith only [v])
lemma Sugar.icing(f:Sugar a F)(d:ℝ): Sugar a (fun x=>d*F x):=Paddled.scale f d
lemma Sugar.food(f:Sugar a F)(v:a<b):
 ∀ᶠ x in atTop,F x ≤ atRate b x:= pure f (by unfold thinRate;linarith)
lemma Sugar.serve(f:Sugar a F)(v:a<0):
 ∀ᶠ x in atTop,F x ≤ 1:= (Paddled.lim f (by unfold thinRate;linarith)).eventually (ge_mem_nhds zero_lt_one)

lemma bowl(a:ℝ):Sugar a (atRate a):=park _
lemma spice(C:ℝ): Sugar 0 (fun _=>C):= by unfold Sugar thinRate;rw[zero_div];exact lake _
lemma bowl_inv(a:ℝ):Sugar (-a) (fun x=>(atRate a x)⁻¹):=by
 apply (park (thinRate (-a))).agree
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x t
 rw [show thinRate (-a)= -thinRate a by unfold thinRate; ring,Real.rpow_neg t.le]

theorem lemon : Sugar 100000 Real.sqrt:=by
 unfold Sugar thinRate;rw[show (100000/200000:ℝ)=1/2 by norm_num]
 simpa only [←Real.sqrt_eq_rpow] using Paddled.park (1/2)
theorem mintR : Sugar (-80000) clocks.scant:=by
 unfold Sugar thinRate; rw [show (-80000/200000:ℝ)=-(2/5) by norm_num];exact park _
theorem fruit (R:Rules T4):
 Sugar (-99999) (fun x=>temp x+faceCutError R (clocks.scant x)):=by
 apply Sugar.honey
 · unfold Sugar thinRate; rw[show (-99999/200000:ℝ)=-(1/2)+1/200000 by norm_num];exact tempay (by norm_num)
 exact (mintR.bake (b:=-99999) 2 (by norm_num)).icing _

-- generic wheel prices. 
def loss₁(R:Rules T4)(u x:ℝ):= u*Real.sqrt x^2*(2*clocks.scant x)^3+ u*2*
 (Real.sqrt x*(temp x+faceCutError R (clocks.scant x)))^4 / bWindow x^2


lemma cake₁(R:Rules T4)(u:ℝ):Sugar (-36) (loss₁ R u):=by
 apply Sugar.honey
 · exact Sugar.stew ((lemon.bake (b:=200000) 2 (by norm_num)).icing u) ((mintR.icing 2).bake (b:= -240000) 3 (by norm_num)) (by norm_num)
 let h:= ((Sugar.stew lemon (fruit R) (d:=1) (by norm_num)).bake (b:=4) 4 (by norm_num)).icing (u*2)
 apply Paddled.agree (Sugar.stew h ((bowl_inv 20).bake (b:=-40) 2 (by norm_num)) (by norm_num : (4:ℝ) + -40 ≤ -36))
 exact Eventually.of_forall fun x=>by simp only [inv_pow,bWindow, div_eq_mul_inv]

end Cake

section Candle
variable {n:Side}
 {q:Clip}{Z:PathData T4}{H:Bed}{η C S:ℝ}

abbrev Mi:=atRate 8
abbrev Ni:=atRate 85
abbrev Ei:=atRate (-24)
abbrev Li:=atRate 67

abbrev Candle {R:Type}[NormedAddCommGroup R][NormedSpace ℝ R][MeasurableSpace R][BorelSpace R]
 (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(x β:ℝ)(o d:Site n)
 (F:Yn n R)(W:Chalk n R):Prop:=Ion B P p β (clocks.scant x) o d F W (Mi x) (Ni x) (Ei x) (Li x)
abbrev titheB(x:ℝ):=tithe (Ei x) (Li x) (thetaB x)
end Candle

abbrev wavePay(x:ℝ):=titheB x+thetaB x^2*Mi x^2

open Cake
lemma titheprice:Sugar (-224) titheB:=by
 refine (Sugar.stew (bowl _) (bowl _) (by norm_num: - (200:ℝ)+ -24 ≤ -224)).honey ?_
 exact (((bowl 67).bake 2 (b:=134) (by norm_num)).icing Regis.trend).stew ((bowl (-200)).bake 2 (b:= -400) (by norm_num)) (by norm_num)
lemma waveprice:Sugar (-224) wavePay:= titheprice.honey
 (((bowl (-200)).bake 2 (b:= -400) (by norm_num)).stew ((bowl 8).bake 2 (b:=16) (by norm_num)) (by norm_num))
lemma waveBurn:∀ᶠ x in atTop, thetaB x * (Mi x + Ni x) ≤1:=Sugar.serve
 ((bowl (-200)).stew (((bowl 8).raise (b:=85) (by norm_num)).honey (bowl _)) (d:=-100) (by norm_num))
 (by norm_num)
end YM.CF.Bay.D
