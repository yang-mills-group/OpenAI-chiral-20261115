import YM.SU5.Intrinsic.Rate.Local
import YM.CF.Ione.Lean
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
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
-- root pension distribute. supports preserving regular total memory.
variable (τ:Ids n) {v:Aura n→ℝ}(qE:Sym_a E)(p:Turf E)(s_:0≤h) (t:∀ i:Aura n, Vow.Medal P i.val ∅ (E i) h (v i))

/- Exploit slack: `Ione.loan_t` and `worth_R` adaptations. -/
include s_ t
lemma loan_surcharge(i:Aura n)(j:Hz)(p:lagE j=i): (plusOneRate P).mass j.val.2 (pence_Q P v j)≤ reserveT P.power P.order P.B 1 * (v i* Trees.currency P.B (P.supportExponent+1+1) i.val):=by
 let R:=reserveT P.power P.order P.B 1; let x:= pence_Q P v j; have hf:=t i; have hv:=hf.wage s_; have hx:0≤R:=by unfold R reserveT coin_n stilK; positivity
 have hp:j.val.2=i.val:= congrArg Subtype.val p; change (plusOneRate P).mass _ x ≤_; rw [show x=bassH i* (v i*fareX P.B P i.val) from ?_]
 swap; · unfold x pence_Q; rw [p,hp,mul_comm (Vow.fareX ..)]
 rw [hp]; let A:= (plusOneRate P).mass i.val (v i); unfold BudgetPoint.mass; have hU: 0≤ A:=mul_nonneg (Real.exp_pos _).le hv; have hh : (1:ℝ) ≤ (i.val.card:ℝ):= Nat.one_le_cast.mpr (card_pos.mpr i.property)
 calc
    _ ≤ A*fareX P.B P i.val:=by
       unfold A BudgetPoint.mass; rw [mul_assoc (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; exact mul_le_of_le_one_left (mul_nonneg hv (health_f ..)) (inv_le_one_of_one_le₀ hh)
    _ ≤ A*(R*Real.exp (1 *coverNumber P.B i.val)):=by exact mul_le_mul_of_nonneg_left (coinPay P _ 1 zero_lt_one) hU
    _ = _ := by unfold A BudgetPoint.mass Trees.currency; dsimp only [plusOneRate,surchargeRate]; rw [add_mul (P.supportExponent+1),Real.exp_add]; unfold R; ring -- reserve expansion?

include p qE
/-- Raises cost at literally `cast_E` with no additional RHS loss. -/
lemma worth_surcharge (u:∀ i:Seat n,tallB v P.B (P.supportExponent+1+1) i≤b): IncX Utrue (cast_E E τ) (plusOneRate P) h (reserveT P.power P.order P.B 1*b):=by
 let V:=pence_Q P v; refine ⟨⟨V,fun i=> (pressure_unchanged ..).2 (dare_L P E τ p s_ t i),fun i=> ?_⟩,(worth_R P E τ qE p s_ t u).face⟩
 let R:= reserveT P.power P.order P.B 1; let X:= univ.filter (fun j:Hz=>i=j.val.1); let G:= univ.filter (fun z:Aura n=>i∈z.val); apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (show 0≤R from (by unfold R reserveT coin_n stilK; positivity)))
 rw [←sum_filter,←sum_fiberwise_of_maps_to (s:=X) (t:=G) (g:=lagE) (fun j p=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.symm ▸ j.property⟩), tallB,mul_sum]; apply sum_le_sum; intro j y; let Z:Hz:=⟨(i,j.val),(mem_filter.mp y).2⟩; have hk : lagE Z=j:=Subtype.ext rfl; rw [sum_eq_single_of_mem (s:=X.filter fun i=>lagE i=j) Z (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,hk⟩)]; exact loan_surcharge P E s_ t j Z hk
 intro v t' h; have hx:v=Z:= Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t').1).2.symm) (congrArg Subtype.val (mem_filter.mp t').2)); exact False.elim (h hx)
end YM.CF.Ione
#print axioms YM.CF.Ione.worth_surcharge
