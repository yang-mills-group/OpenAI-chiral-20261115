import Organdy.Vent
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Lor SectorNext.Remainder Pressure Fief Py
open Py.Rate.BScale BPress

variable (R:Patch)
local notation "Q" => allotΨ R.L
def tailWidth (B:ℕ)(M:ℕ):ℝ :=
     (1/(18*(M+1):ℝ))*B

def prismPan (R:Patch)(w:ℕ)(x:ℝ):ℝ :=
   (1+(radiusB x :ℝ))^w * (allotΨ R.L x)⁻¹


/-- compare radius b to log, as in computed_rc. -/
private lemma iceTime (d:ℝ)(e:0<d) :
 sizeK R.L 4 (fun x=>Real.exp (-d*(radiusB x:ℝ))):=by
 have he:0<d/2:= by positivity
 apply ((sizeK.tip R.L (d/2) he).square 2).cost_d
 filter_upwards with x; rw [abs_of_pos (Real.exp_pos _)]
 refine le_trans ?_ (le_abs_self _)
 unfold Neige.tipPay; rw [←Real.exp_nat_mul]; apply Real.exp_monotone
 push_cast
 have ht:(↑(radiusB x/60):ℝ) ≤ (radiusB x:ℝ):=by exact_mod_cast (Nat.div_le_self (radiusB x) 60)
 nlinarith only [mul_le_mul_of_nonneg_left ht e.le]

abbrev plx (x:ℝ):ℝ:=1+radiusB x

lemma beryl(α:ℕ):BoreP (fun x=>plx x ^α):=
 ((BoreP.still 1).join BoreP.radius_c).self _

lemma opulence (α M:ℕ):
   ∀ᶠ x in atTop, (0<allotΨ R.L x ∧ 2 ≤ prismPan R α x ∧
       2*prismPan R α x ≤ Real.exp (tailWidth (radiusB x) M)):=by
 let d:= (1/(18*(M+1):ℝ))
 have e:0<d:=by unfold d;positivity
 let f(x:ℝ):=(2*(plx x)^α)*Real.exp (-d*(radiusB x:ℝ))
 have u:sizeK R.L (2+1) f:=((((beryl α).creditK R.L).scale 2).tint (iceTime R _ e)).low (by omega)
 have h:=pill_R (R:=R) (k:=2) (d:=1) _ zero_lt_one u
 let j:=((size_ψ R.L).low (k:=1) (by omega)).spine
 filter_upwards [h,(Scales.year SU.group R.L).eventually_gt_atTop 0, j.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2))] with x p q z
 have hr:0<Q x:=pow_pos (Scales.gauge _ _ q) _
 have hs:2*Q x≤(plx x)^α :=(show _≤(1:ℝ) from by change Q x≤1/2 at z; linarith).trans (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
 refine ⟨hr, by unfold prismPan; rw [←div_eq_mul_inv,le_div_iff₀ hr];exact hs, ?_⟩ -- mul_inv_ge_iff?

 let E:=Real.exp (tailWidth (radiusB x) M)
 have hh:(2*plx x ^α) / E ≤Q x:=by
   change 2*plx x^α*Real.exp _ < 1*Q x at p
   rw [neg_mul,Real.exp_neg,←div_eq_mul_inv, one_mul] at p
   exact p.le
 unfold prismPan
 rw [←mul_assoc,←div_eq_mul_inv,div_le_iff₀ hr,mul_comm (Real.exp _)]
 exact (div_le_iff₀ (Real.exp_pos _)).mp hh
end YM.CF.Organdy
