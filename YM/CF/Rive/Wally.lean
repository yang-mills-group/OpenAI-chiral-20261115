import YM.CF.Rive.Meal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Mew Ione
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
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
open Bake Gas Palot
abbrev giftK(P:BudgetPoint)(Θ:ℝ)(i:Force n)(x:Seat n):ℝ:= if x∈ i.val.1.val.2 then Trees.currency P.B Θ i.val.1.val.2 else 0
abbrev filmK(P:BudgetPoint)(Θ:ℝ)(i:Scree.Hub n)(x:Seat n):ℝ:= if x=i.val.1 then Trees.currency P.B Θ i.val.2 else 0
-- ONE rebate extra. SanB and ForgeB true analytical rooted budgets
lemma quoteK {Θ α z h:ℝ}(W:Aura n→ Support (More n)→ℝ)(K: Vow.Cusp n)(t: ArmsK P K W h)(hb:∀ i: Seat n,tallB (Vow.hymn W) P.B (Θ+α) i ≤ z)(hr:0≤h)(hp:0<α): SanB (budgetR K) (giftK P Θ) P h (fun _=>reserveT P.power P.order P.B α*z):=by
 refine ⟨⟨rentH P W,fun i=> hardy t i hr,fun j=>?_⟩⟩; unfold giftK; simp_rw [ite_mul,zero_mul]; exact (mezzo t hr j α Θ hp).trans (mul_le_mul_of_nonneg_left (hb j) (show 0 ≤ Nor.reserveT P.power P.order P.B α from (by unfold reserveT coin_n stilK; positivity)))
lemma quoteE {Θ α z h:ℝ}(W:Aura n→ℝ)(F:Pax n)(t:∀ x:Aura n, Medal P x.val ∅ (F x) h (W x))(p:Turf F)(v: Ids n)(hb:∀ i: Seat n,tallB W P.B (Θ+α) i ≤ z)(hr:0≤h)(hp:0<α): ForgeB (cast_E F v) (filmK P Θ) P h (fun _=>reserveT P.power P.order P.B α*z):=by
 let R:=reserveT P.power P.order P.B α; have hR:0≤R:=by unfold R reserveT coin_n stilK; positivity
 have he(j:Scree.Hub n):let i:=lagE j; Trees.currency P.B Θ i.val*(pence_Q P W j) ≤ R*(W i*Trees.currency P.B (Θ+α) i.val):=by
    intro i; have hx:0 ≤ W i:= (t i).wage hr; let A:=Trees.currency P.B Θ i.val; let f:=fareX P.B P i.val; have hw:0 ≤ f:=health_f ..; have ht:=le_trans (show A *(bassH i * (f*W i))≤ A*(f*W i) from mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg hw hx) (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (card_pos.mpr i.property)))) (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nor.coinPay P i.val α hp) hx) (Real.exp_pos _).le)
    refine ht.trans (le_of_eq ?_); unfold A R Trees.currency; rw [add_mul,Real.exp_add]; ring
 refine ⟨⟨pence_Q P W,dare_L P F v p hr t,fun i=> ?_⟩⟩
 unfold filmK; simp_rw [ite_mul,zero_mul]
 let Hz:=Scree.Hub n; let X:= univ.filter (fun j:Hz=>i=j.val.1); let G:= univ.filter (fun z:Aura n=>i∈z.val); apply le_trans _ (mul_le_mul_of_nonneg_left (hb i) hR)
 rw [←sum_filter,←sum_fiberwise_of_maps_to (s:=X) (t:=G) (g:=Bake.lagE) (fun j p=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.symm ▸ j.property⟩), tallB,mul_sum]; apply sum_le_sum; intro j y; let Z:Hz:=⟨(i,j.val),(mem_filter.mp y).2⟩; have hk : lagE Z=j:=Subtype.ext rfl; rw [sum_eq_single_of_mem (s:=X.filter fun i=>lagE i=j) Z (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,hk⟩)]; exact (he Z).trans (by rw [hk]) -- check defeq.
 intro v t' h; have hx:v=Z:= Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t').1).2.symm) (congrArg Subtype.val (mem_filter.mp t').2)); exact False.elim (h hx)
end YM.CF.Rive
