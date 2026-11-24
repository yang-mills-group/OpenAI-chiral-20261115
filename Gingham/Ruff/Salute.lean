import Gingham.Ruff.Zach
import Gingham.Ruff.Boarding
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Pressure
open Buffered Afterglow Satin Tapestry
open Rush Scroll
lemma well_pitch(p:BudgetPoint)(h:Roomy (wisp p) N):
    2*(p.B/10+1) < (More N).val:=by
 by_contra! k
 have v:(More N).val ≤ p.B+8:=by omega
 let m:=(More N).val
 let s:Cover:= fun _ => (m:ℤ)
 have u:s∈wisp p:=ore_mem.mpr (box_test.mpr 
     ⟨fun _=>by rw [sub_zero]; unfold s m;omega,fun _=>by rw [sub_zero]; unfold s m;omega⟩)
 have z:(0:Cover)∈wisp p:=ore_mem.mpr (box_test.mpr 
     ⟨fun _=>by rw [sub_zero];change _≤(0:ℤ); omega,fun _=>by rw [sub_zero];change (0:ℤ) ≤_;omega⟩)
 have f:wrap (More N) s=wrap _ (0:Cover):=by
    rw [map_zero];funext i; change (((m:ℤ)):ZMod m)=0
    rw [Int.cast_natCast,ZMod.natCast_self]
 have e:=congrFun (h.seats.seat_ u z f) 0
 have :=(More N).property
 change (m:ℤ)=0 at e
 have ht:(0:ℤ)< ↑m:=by exact_mod_cast this
 exact ht.ne' e


lemma fee_fairy (a:ℝ)(h:0<a):
 ∀ᶠ x:ℝ in atTop, fairy a (radiusB x) ≤ temp x ^3:=by
 have A: Tendsto Real.log atTop atTop:= Real.tendsto_log_atTop
 filter_upwards [eventually_gt_atTop (1:ℝ),A.eventually_ge_atTop (9600/a)] with x t v
 have y:0<x:=zero_lt_one.trans t
 let l:=Real.log x
 have l0:0<l:=Real.log_pos t
 have e:(-a*(radiusB x:ℝ)/3200) ≤ -3*l:=by
   have m:l^2≤(radiusB x:ℝ):= Nat.le_ceil (l^2)
   have q:9600≤l*a:=(div_le_iff₀ h).mp v
   nlinarith only [mul_le_mul_of_nonneg_left m h.le, mul_le_mul_of_nonneg_right q l0.le]
 apply (Real.exp_monotone e).trans
 rw [neg_mul,Real.exp_neg]
 have v: Real.exp (3*l)=x^3:=by
    change Real.exp (3*(Real.log x))=x^3
    convert Real.exp_nat_mul (Real.log x) 3 using 1
    · norm_num
    · rw [Real.exp_log y]
 rw [v,←inv_pow]
 refine pow_le_pow_left₀ (by positivity) (le_trans ?_ 
   (le_mul_of_one_le_right (by positivity:0≤(Real.sqrt x)⁻¹)
    (Real.one_le_exp (by positivity:0≤(Real.log (Real.log x))^2)))) 3
 exact (inv_le_inv₀ y (Real.sqrt_pos.2 y)).2 ((Real.sqrt_le_iff.mpr ⟨y.le,by nlinarith⟩))


open Py.Rate.Location
#check Py.Rate.Location.Boot
def WharfCost(a ρ:ℝ)(p:BudgetPoint):Prop:=
 Parasols p ρ (p.B/10) ∧ fairy a p.B ≤ p.threshold^3 ∧ fairy a p.B ≤ p.threshold^2

lemma wharf_fee(a ρ:ℝ)(h:0<a)(r:0<ρ):
 ∀ᶠ x:ℝ in atTop, ∀ p, Boot x p → WharfCost a ρ p:=by
 have t:Tendsto temp atTop (𝓝 0):= by simpa using Work.E09.radiusB_temp 0
 let F x:= temp x*(1+(radiusB x:ℝ))
 have v:Tendsto F atTop (𝓝 0):=by
    have q:= t.add (Work.E09.radiusB_temp 1)
    rw [zero_add] at q
    exact q.congr fun x=>by unfold F;ring_nf


 filter_upwards [t.eventually (ge_mem_nhds zero_lt_one),fee_fairy a h, v.eventually
    (ge_mem_nhds (div_pos clockPin.radius (show (0:ℝ)<4 from by norm_num))),
    v.eventually (gt_mem_nhds (div_pos r (show (0:ℝ)<8 from by norm_num)))] with x e c u v p z
 have j:= p.threshold_pos
 rw [←z.threshold] at e
 rw [←z.threshold,←z.B] at c
 unfold F at u v;rw [←z.threshold,←z.B] at u v
 have g:(((p.B/10:ℕ):ℝ)) ≤ p.B:=by exact_mod_cast Nat.div_le_self _ _
 refine ⟨⟨?_,?_,r⟩,c,c.trans ?_⟩
 · nlinarith
 · unfold liltCost; rw [div_lt_one r]; nlinarith
 rw [pow_succ]; exact mul_le_of_le_one_right (sq_nonneg _) e

