import Merino.Lace.Palette
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Lace
open Garter Regis.Circuit CF.Lat
open Stationary (Gaia)
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

variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "wE"=>stamen B P n
local notation "χ"=>stdGaussian wE
local notation "J"=>Husk G n


open Maxwell


abbrev pole:Axis:=3
abbrev ray:Gaia:=basis pole
abbrev armPay := 4*Maxwell.normal
lemma gold:0<armPay:=by unfold armPay normal; positivity
lemma rayon:‖ray‖=1:=by simp [ray,basis]
lemma ray0:ray≠0:=by have :=rayon; intro h;rw [h,norm_zero] at this; norm_num at this
abbrev hm(i:Axis):ℝ:=if i=pole then 6*Maxwell.normal else -2*Maxwell.normal
lemma ray2(i j:Axis):
 grad i (grad j Maxwell.Green) ray=
 if i=j then hm j else 0:=by
 rw [second_Green ray0,rayon]
 simp [ray,basis,hm] 
 split_ifs <;> grind


lemma ray3(a b:PlaqAxes) :
 ↑(orient (Signed.mirror pole) b)*specter a b ray=(↑(if a=b then armPay else (0:ℝ)):ℂ):=by
 rw [specter,← Complex.ofReal_mul]
 congr 1 -- danger if pulls ite / cost semired? 
 rw [bareCurl,Pi.sub_apply,Bare.opp_grad ray0,Bare.opp_grad ray0,
   ray2,ray2,ray2,ray2]
 by_cases h:a=b
 · rw [if_pos h,h]
   simp [b.property.ne,b.property.ne',b.property.not_gt,hm,orient,turnb,Signed.mirror,armPay,eq_comm]
   have hz:=b.property.ne
   split_ifs<;>grind
 rw [if_neg h]
 have ha:=a.property; have hb:=b.property
 have he:=mt (fun t: a.val.1=b.val.1 ∧ a.val.2=b.val.2=>show a=b from
    Subtype.ext (Prod.ext t.1 t.2)) h
 convert mul_zero (orient ..) using 2
 grind


end YM.CF.Merino.Lace
