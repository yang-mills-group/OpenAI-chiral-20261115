import YM.CF.Brood.Rink
import Weft.Bridge
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
variable {I:Type}[LinearOrder I][Fintype I]
variable (L:Side)(σs:I→ Site (mid N B)) (hb:Very_Ψ σs X.p.B)
local notation "Yκ"=> sameY σs
local notation "Pt"=> PairKey I
include hb
-- adapted Rink & our Bridge.
lemma pairCourt :(Force_M X.p.B (Cube.node∘ sameY σs) 2):=by
 let B:= X.p.B
 constructor; · intro i j p; apply hb.2 _ _ p
 intro x; let c:=cape_B B; let S:= reach_B c B (Cube.node ∘ sameY σs) x; change S.card ≤ 2; by_cases t:S.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp t]; simp
 obtain ⟨i,h⟩:= t; have hf: S⊆ {pick i.1 false,pick i.1 true}:=by
    intro j p; have hzS(g)(v:g∈S): separation x ((Cube.node ∘σs) (yard g))≤ B+c:= (Finset.mem_filter.mp v).2; have heτ:(Cube.node ∘σs) (yard i)=(Cube.node∘σs) (yard j):=by
       by_contra k; have hp:= hb.2 _ _ k; have ht:separation ((Cube.node ∘σs) (yard i)) ((Cube.node ∘σs) (yard j))≤ (B+c)+(B+c):=(separation_triangle _ x _).trans (add_le_add ((separation_comm ..).le.trans (hzS i h)) (hzS j p)); unfold c B at ht; omega
    have he:=hb.1 heτ; simp only [mem_insert,mem_singleton]
    cases u:j.2; exact Or.inl (Prod.ext he.symm u); exact Or.inr (Prod.ext he.symm u)
 have he:pick i.1 false ≠ pick i.1 true:=fun h=>Bool.noConfusion (congrArg (altQ (I:=I)) h)
 exact (card_le_card hf).trans ((by rw [card_insert_of_notMem (fun p=>he (mem_singleton.mp p)),card_singleton]))
lemma seasonQ (u: ((L.val+1)*(4*X.p.B+2)+2*X.p.B)≤ X.p.B+cape_B X.p.B): GapN (sameY σs) X.p.B L.val 2 :=by
 intro y; exact le_trans (Finset.card_le_card fun i p=> mem_filter.mpr ⟨mem_univ _, ((separation_comm ..).le.trans ((mem_filter.mp p).2.trans u))⟩) ((pairCourt σs hb).2 y)
omit hb
lemma veryOne (o:Site (mid N B))(k:ℕ):Very_Ψ (fun _:Fin 1=>o) k:=⟨fun _ _ _=>Subsingleton.elim ..,fun i j p=> False.elim (p rfl)⟩
#print axioms seasonQ
end YM.CF.Py
end
