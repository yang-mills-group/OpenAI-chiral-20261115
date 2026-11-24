import YM.CF.Wray.Tree
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "η"=> Rust (mid N B)
local notation "K'"=> LeanV (Single (mid N B))
variable {D:Sweep (mid N B)→ Prop}{S_:GramM (mid N B)}{δ δ' cX h:ℝ}
-- Accounting transfer startup ABI.
private lemma toe{i:Force (mid N B)}{y:Copy (mid N B)} (h:0 ≤ c)(p:Scree.ForceB (n:=mid N B) (p:=S_.p) i y c d):0 ≤ d:=by obtain ⟨a,hc,-,hq⟩:= p.costP; refine (sum_nonneg ?_).trans hq; intro i _; unfold Scree.tariff; exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg h _)) (hc _)
lemma calendarL (h0:0 ≤ h)(p:Scree.IncX D S_.F S_.p h δ) (r:Scree.IncX D S_.slip S_.p h δ') (u:Scree.Dark D S_.K S_.p h cX) :∃ C' Λ', Rustic S_.p Λ' C' h ((δ+δ')+cX) ∧ ∀ i,Yaw.Beat_ S_ i (C' i) h (Λ' i):=by
 obtain ⟨f,v,V₀⟩:= p.weight; obtain ⟨f',l,L⟩:= r.weight; obtain ⟨W,x,M⟩:= u.weight
 choose Q hc hv hz using fun i=>(v i).worth; choose Q' hC h hL using fun i=>(l i).worth; choose Z hp hu hx using fun i=>(x i).costP; let F0(i:Roc (mid N B)):= if i.2 then f i.1 else f' i.1; let V0(i:Roc (mid N B)):= if i.2 then Q i.1 else Q' i.1; let P:= Sum.elim F0 W; let U:= Sum.elim V0 Z
 refine ⟨U,P,⟨fun i j=>?_ ,fun i=>?_ ,fun o=>?_⟩,fun i=>?_⟩
 · rcases i with ⟨i,⟨⟩|⟨⟩⟩|i -- tune bool
   exact hC i j
   exact hc i j
   exact hp i j
 · rcases i with ⟨i,⟨⟩|⟨⟩⟩|i
   exact hL i
   exact hz i
   exact hx i
 · rw [sum_filter,Fintype.sum_sum_type]; refine add_le_add ?_ (le_trans (sum_le_sum ?_) (M o)); swap
   · intro i p; have he:=toe h0 (x i)
     by_cases hz:angle (Sum.inr i)=o
     · have hp:o∈i.val.1.val.2:= hz ▸ (show angle (Sum.inr i)∈i.val.1.val.2 from i.val.1.property); simp only [if_pos hz, if_pos hp]; exact le_rfl
     rw [if_neg hz]; split_ifs; exact (he.trans (S_.p.loMass _ _ he)); rfl
   rw [Fintype.sum_prod_type]; simp only [Fintype.sum_bool, sum_add_distrib]; -- ordering of if
   apply add_le_add
   · apply le_trans _ (V₀ o); refine sum_le_sum fun i _=>?_ ; change (if i.val.1=_ then _ else _ ) ≤ (if _=i.val.1 then _ else _); simp only [show i.val.1=o ↔ o=i.val.1 from eq_comm]; exact le_rfl
   apply le_trans _ (L o); refine sum_le_sum fun i _=>?_ ; change (if i.val.1=_ then _ else _ ) ≤ (if _=i.val.1 then _ else _); simp only [show i.val.1=o ↔ o=i.val.1 from eq_comm]; exact le_rfl
 rcases i with ⟨i,⟨⟩|⟨⟩⟩|i
 · exact ⟨l i,h i⟩
 · exact ⟨v i,hv i⟩
 exact ⟨x i,fun V I t j=> hu i (V,I) t j⟩
end YM.CF.Wray
