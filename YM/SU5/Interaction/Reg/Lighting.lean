import YM.SU5.Interaction.Reg.Brim

/-! 124: Lit uses on any final support and exact flags (including even some ties).
Do not invoke generic continuity of flags; read per flag configuration. -/
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



def illuminated (E:RegBudget n) (i:Scree.Hub n) (D:Support (More n)) : Copy n := if Disjoint i.val.2 D then oV (head_L E i) else 0

structure Litigation (b:ℝ)(E:RegBudget n)(h v:ℝ) : Prop where
 weight : ∃ z: Scree.Hub n → ℝ,(∀i D (X:Support (More n)),i.val.2 ⊆ X → Vow.Medal P X D (illuminated E i D) h (z i)) ∧ ∀ x:Seat n,(∑ i:Hz,if x∈i.val.2 then Real.exp (b*coverNumber P.B i.val.2)*z i else 0) ≤ v

variable {R:RegBudget n} {A D: Support (More n)}
lemma LocalHead.asLit (p:LocalHead P b R h a)(hv:0≤h) : Litigation P b R h (Vow.chi_f P.order * a) := by
 obtain ⟨v,t,u⟩:= p.weight; let z(i: Scree.Hub n):= Vow.chi_f P.order * v i
 refine ⟨⟨z,fun i D X h=>?_,fun i=>?_⟩⟩
 · let w:= rimR (t i) hv; unfold illuminated; split_ifs with hq
   · apply w.stretchB h (empty_subset _); rw [sdiff_empty]; exact fun k a=> mem_sdiff.mpr ⟨h a, Finset.disjoint_left.mp hq a⟩
   exact Vow.Medal.zeroT.big (w.wage hv)
 apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (spicy_f _)); rw [mul_sum]; apply le_of_eq; apply sum_congr rfl; intro j _; unfold z; split; exact mul_left_comm ..; exact (mul_zero _).symm
lemma litRule (V:Orbit n)(t:V.1 ∈ litres P.threshold A D)(i:Scree.Hub n)(p:i.val.2 ⊆ A): numbE P.threshold i.val.2 (head_L R i) V.1 = illuminated R i D V:=by
 unfold illuminated numbE; split_ifs with h
 · rw [Set.indicator_of_mem]; exact grow_b (fun j a=>mem_sdiff.mpr ⟨p a,Finset.disjoint_left.mp h a⟩) t.1 -- placeholders
 rw [Set.indicator_of_notMem]; rfl; intro a; exact h (Disjoint.mono_right t.2 (ping_le a))
end YM.CF.Ione
