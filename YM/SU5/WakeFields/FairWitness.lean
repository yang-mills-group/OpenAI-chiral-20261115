import YM.SU5.WakeFields.CircuitBooks
import YM.SU5.WakeFields.Costumes
import YM.SU5.Exchange.Seed.Ticket

/-! # Moving witness budget (with the same circle counts). Even for bandwidths
inversely as B. Important on the birth of the transferred `Y'` and pack integrity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog
open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open Roots Py
open scoped YM.CF.Mew

lemma filmHue (P : BudgetPoint)(i : Scree.Hub n)(j:Seat n)(w : ℝ) : 0≤ filmK P w i j := by
 unfold filmK; split; exact (Real.exp_pos _).le; exact le_rfl
lemma filmHon (P : BudgetPoint)(i : Scree.Hub n)(w : ℝ) : 0 < filmK P w i i.val.1 := by
 rw [filmK,if_pos rfl]; exact Real.exp_pos _
lemma giftHue (P : BudgetPoint)(i : Force n)(j:Seat n)(w : ℝ) : 0≤ giftK P w i j := by
 unfold giftK; split; exact (Real.exp_pos _).le; exact le_rfl
lemma giftHon (P : BudgetPoint)(i : Force n)(w : ℝ) : 0 <giftK P w i i.val.1.val.1 := by
 rw [giftK,if_pos i.val.1.property]; exact Real.exp_pos _
lemma ForgeInc {F : RegBudget n}(Z:ForgeB F (filmK P P.supportExponent) P h (fun _=> c)) : IncX primeU F P h c := by
 obtain ⟨f,q,v⟩:= Z.bit; refine ⟨⟨f,q,fun i=>?_⟩, fun i p=>False.elim p⟩; refine le_trans ?_ (v i); apply le_of_eq; exact sum_congr rfl fun j _=> by simp only [filmK,ite_mul,zero_mul]; rfl
lemma SanDark {F : ForceBudget n}(Z:SanB F (giftK P P.supportExponent) P h (fun _=> c)) : Dark primeU F P h c := by
 obtain ⟨f,q,v⟩:= Z.bit; refine ⟨⟨f,q,fun i=>?_⟩,fun i p=>False.elim p⟩; refine le_trans ?_ (v i); apply le_of_eq; exact sum_congr rfl fun j _=> by simp only [giftK,ite_mul,zero_mul]; rfl
-- high-Key entries together.W.pricing with only η of order reciprocal B
variable {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n) {t:ℕ}(p:Force_M P.B σ t)
variable (E:Key I→RegBudget n)(F:Key I→ForceBudget n)
variable (he:∀ X:Scree.Hub n,Hush σ X.val.2 (fun z=> E z X) ∧ ∀ u,River (fun z:Key I=> E z X u))
variable (hf:∀ X:Force n,Hush σ X.val.1.val.2 (fun z=> F z X) ∧ ∀ u,River (fun z:Key I=> F z X u))
variable (z:Key I) (c':ℝ)(hp:∀ i, ‖z i‖≤ c') (δ X θ:ℝ)(hc:1 ≤ c') (cv:2*c' ≤ Real.exp X) (hA:0 ≤ X)(hδ:0 ≤ δ) (hV:0 < h)
local notation "A₁"=> manySet σ
local notation "A₂"=> trueSet σ
local notation "Zξ"=> sigma δ P.B
local notation "pτ"=>P.supportExponent
include p hp hc cv hA hδ hV
include he
lemma manyCircuit
    (u' : ∀ z∈hill I, ForgeB (E z) (filmK P (θ+δ)) P h (fun _=>a))
    (w : 9*X*t ≤ (δ/2)*(P.B:ℝ)^2) : ForgeB (rim_C σ E z) (filmK P θ) P h (fun _=>sigma δ P.B*a) := by
 have hΓ:0≤ Zξ:=(Real.exp_pos _).le
 have hr(t):= (he t).2
 obtain ⟨K,hW,u⟩:= earnChar (P:=P) E hV (filmK P (θ+δ)) (fun i j=> filmHue P i j _) (fun i=>⟨i.val.1,filmHon P i _⟩) _ u' hr
 have hpK(i:Scree.Hub n):0 ≤ K i:= Roots.gradeE _ _ (hW ∅ i) hV.le
 let wξ (i:Scree.Hub n):= ((A₁).filter (·⊆ sits_at σ i.val.2))
 have hz(i:Scree.Hub n)(j:Finset I)(l:j∈A₁)(w:j∉wξ i):νΦX E j i=0:=by
    have t:¬ j ⊆ sits_at σ i.val.2:= fun v=> w (mem_filter.mpr ⟨l,v⟩)
    obtain ⟨x,p,v⟩:= Finset.not_subset.mp t
    let q:= (he i).1; funext U; exact Neon.husht_B _ _ _ (show Hush σ i.val.2 (fun z=>E z i U) from fun a b t x p=>congrFun (q a b t x p) U) (hr i U) (Mew.Cue I j) x (fun s=>v (mem_filter.mpr ⟨mem_univ _,s⟩)) (by simpa [Mew.Cue] using p)
 let uX(i:Scree.Hub n):= (∑ j∈wξ i, ‖Mew.pine j z‖*K i)
 refine ⟨⟨uX,fun i=> ?_,fun j=>?_⟩⟩
 · unfold rim_C; rw [Finset.sum_apply, ←sum_subset (filter_subset (fun i'=> i'⊆ sits_at σ i.val.2) (A₁)) (fun j l t=> ?_)] -- leaves extra goals order
   · exact Larch.prop_sum _ _ _ _ _ _ (fun j _=> súe _ _ (hW j i) (Mew.pine j z)) -- requires norm after smul, and z
   change Mew.pine j z • νΦX E j i=0; rw [hz i j l t,smul_zero]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (u j) hΓ); rw [mul_sum]; refine Finset.sum_le_sum (fun i _=> ?_)
 unfold filmK; split_ifs with g; swap; · simp
 unfold uX; rw [←sum_mul]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (stars σ t p i.val.2 _ i.property z c' hp δ X hc cv hA hδ w) (hpK i)) (Real.exp_pos _).le).trans (le_of_eq ?_)
 unfold Trees.currency; rw [add_mul,Real.exp_add]; ring
omit he
include hf
lemma forceCircuit
    (u' : ∀ z∈hill I, SanB (F z) (giftK P (θ+δ)) P h (fun _=>a))
    (w : 6*X*t ≤ δ*(P.B:ℝ)^2) : SanB (bustle σ F z) (giftK P θ) P h (fun _=>Real.exp (X*t)*a) := by
 have hr(t):= (hf t).2
 obtain ⟨K,hW,u⟩:= earnFirth (P:=P) F hV (giftK P (θ+δ)) (fun i j=>giftHue P i j _) (fun i=>⟨i.val.1.val.1,giftHon P i _⟩) _ u' hr
 have hpK(i:Force n):0 ≤ K i:= Roots.gradeQ _ _ (hW ∅ i) hV.le
 let wξ (i:Force n):= ((A₂).filter (·⊆ sits_at σ i.val.1.val.2))
 have hz(i:Force n)(j:Finset I)(l:j∈A₂)(w:j∉wξ i):νΦK F j i=0:=by
    have t:¬ j ⊆ sits_at σ i.val.1.val.2:= fun v=> w (mem_filter.mpr ⟨l,v⟩)
    obtain ⟨x,p,v⟩:= Finset.not_subset.mp t
    let q:= (hf i).1; funext U; exact Neon.husht_B _ _ _ (show Hush σ i.val.1.val.2 (fun z=>F z i U) from fun a b t x p=>congrFun (q a b t x p) U) (hr i U) (Mew.Cue I j) x (fun s=>v (mem_filter.mpr ⟨mem_univ _,s⟩)) (by simpa [Mew.Cue] using p)
 let uX(i:Force n):= (∑ j∈wξ i, ‖Mew.pine j z‖*K i)
 refine ⟨⟨uX,fun i=> ?_,fun j=>?_⟩⟩
 · unfold bustle; rw [Finset.sum_apply, ←sum_subset (filter_subset (fun i'=> i'⊆ sits_at σ i.val.1.val.2) (A₂)) (fun j l t=> ?_)]
   · exact dom_K_fin _ _ _ _ (fun j _=> dúe _ _ (hW j i) (Mew.pine j z))
   change Mew.pine j z • νΦK F j i=0; rw [hz i j l t,smul_zero]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (u j) (Real.exp_pos _).le); rw [mul_sum]; refine Finset.sum_le_sum (fun i _=> ?_)
 unfold giftK; split_ifs with g; swap; · simp
 unfold uX; rw [←sum_mul]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (winter σ t p i.val.1.val.2 j g z c' hp δ X hc cv hA hδ w) (hpK i)) (Real.exp_pos _).le).trans (le_of_eq ?_)
 unfold Trees.currency; rw [add_mul,Real.exp_add]; ring
end TreasuryFog
end YM.CF.Vow

#print axioms YM.CF.Vow.TreasuryFog.manyCircuit
#print axioms YM.CF.Vow.TreasuryFog.forceCircuit
