import YM.SU5.Interaction.Reg.High
import YM.CF.Beau.Chair
import YM.Next.RANK.Scatter

/-! Route cost tools: mixing cover-rate bills & spending the small bandwidth on incidence.-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
open Beau Next.Rank.Thirst -- Thirst namespace adjust
local notation "Hz"=> Scree.Hub n
local notation "α"=> P.supportExponent

lemma mergeRates {E F:RegBudget n}(p:IncX (fun _=>False) E P h a)(q:IncX (fun _=>False) F (ups P) h b) (w:0≤h) (k:ℕ) (t:∀i:Hz,k < coverNumber P.B i.val.2 → E i= F i) : IncX (fun _=>False) E (ups P) h (Real.exp k*a+b) := by
 obtain ⟨v,hv,u⟩:=p.weight; obtain ⟨z,hz,r⟩:=q.weight
 let g(i:Hz):= if k<coverNumber P.B i.val.2 then z i else v i
 refine ⟨⟨g,fun i=>?_,fun i=>?_⟩,fun _ p=>p.elim⟩
 · unfold g; split_ifs with k; rw [t i k]; exact hz i; exact upsPress (hv i)
 apply le_trans _ (add_le_add (mul_le_mul_of_nonneg_left (u i) (Real.exp_pos (k:ℝ)).le) (r i)); rw [mul_sum,←sum_add_distrib]; apply sum_le_sum; intro j _; split
 · unfold g; split_ifs with H
   · exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (grit_p _ (hv j) w)))
   refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (grit_p _ (hz j) w))); unfold BudgetPoint.mass; rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (grit_p _ (hv j) w); apply Real.exp_monotone
   simp only [ups,editRate]; linarith only [(show (coverNumber P.B j.val.2:ℝ) ≤ (k:ℝ) from (by exact_mod_cast le_of_not_gt H))]
 · simp only [mul_zero,add_zero,le_refl]

/-- When B is large mix cheaply at the intermediate rate. Will use when b≲O(1) but a small. e⁻ᴮ loss absorbs hierarchy. -/
def midRate (P:BudgetPoint)(r:ℝ)(p:0 < r):= editRate P (P.supportExponent+r/P.B) (add_pos P.exponent_pos (div_pos p (by exact_mod_cast P.B_pos)))
lemma bandwidth (e:ℝ)(u:0<e)(δ:2*e ≤ (P.B:ℝ)) {E:RegBudget n}(p:IncX (fun _=>False) E P h a)(q:IncX (fun _=>False) E (ups P) h b)(w:0≤h) : IncX (fun _=>False) E (midRate P e u) h (Real.exp e*a+Real.exp (-(P.B:ℝ)/2)*b):=by
 obtain ⟨v,hv,u'⟩:=p.weight; obtain ⟨z,hz,r⟩:=q.weight
 let g(i:Hz):= if P.B<coverNumber P.B i.val.2 then z i else v i
 have Hα:(P.B:ℝ)>0:= by exact_mod_cast P.B_pos
 refine ⟨⟨g,fun i=>?_,fun i=>?_⟩,fun _ p=> p.elim⟩
 · unfold g; split_ifs
   · exact editPress (hz i) (α+e/P.B) (add_pos P.exponent_pos (div_pos u Hα))
   exact editPress (hv i) _ _
 let c:= Real.exp (- (P.B:ℝ)/2)
 apply le_trans _ (add_le_add (mul_le_mul_of_nonneg_left (u' i) (Real.exp_pos e).le) (mul_le_mul_of_nonneg_left (r i) (Real.exp_pos _).le)); rw [mul_sum,mul_sum,←sum_add_distrib]; apply sum_le_sum; intro j _; split
 · unfold g; let k:ℕ:=coverNumber P.B j.val.2
   split_ifs with s
   · refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos e).le (mul_nonneg (Real.exp_pos _).le (grit_p _ (hv j) w))))
     unfold BudgetPoint.mass; rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (grit_p _ (hz j) w); apply Real.exp_monotone; change (α+e/(P.B:ℝ))*(k:ℝ) ≤ - (P.B:ℝ)/2 + (α+1)*(k:ℝ)
     have f:e/(P.B:ℝ)≤1/2:= (div_le_iff₀ Hα).mpr (by linarith only [δ]); have v:(P.B:ℝ) < (k:ℝ):= Nat.cast_lt.mpr s; linarith only [v,mul_le_mul_of_nonneg_right f (show (k:ℝ)≥0 by positivity)]
   refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (grit_p _ (hz j) w))))
   unfold BudgetPoint.mass; rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (grit_p _ (hv j) w); apply Real.exp_monotone; change (α+e/(P.B:ℝ))*(k:ℝ) ≤ e+α*(k:ℝ)
   have g:(k:ℝ) ≤ (P.B:ℝ):=Nat.cast_le.mpr (le_of_not_gt s); linarith only [mul_le_mul_of_nonneg_left g (show 0≤e/(P.B:ℝ) by positivity), div_mul_cancel₀ e Hα.ne']
 · simp only [mul_zero,add_zero,le_refl]
end YM.CF.Ione
