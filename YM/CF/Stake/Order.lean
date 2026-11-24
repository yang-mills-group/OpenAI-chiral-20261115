import YM.CF.Stake.Pilot
import YM.CF.Lor.Coin
import YM.CF.Vale.Muse
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
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
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y β:ℝ}(p:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
local notation "Q" => radiusB x
lemma mint_u(t:ℕ)(QF: Tab S→DirP (Domain N B))(z:Tips t QF)(p:t≤k): Tips k QF:=by intro P i j; obtain ⟨a,b⟩:=z P i j; exact ⟨fun h=> (a h).trans p,fun _ _ _ h hz=>b _ _ _ (kind_m h (Corona.halo_mono p (Subset.refl _))) fun i v=> hz i (v.trans p)⟩
lemma mild(t:ℕ)(F:Tab S→FileM (Domain N B) G5)(p:waysS t F)(e:t≤k):waysS k F:=fun i j b x y h g=>p i j b x y (kind_m h (Corona.halo_mono e (Subset.refl _))) fun i v=> g i (v.trans e)
-- combine via Certificate upgrade when oth/Fiscal station + hull. No relative ex norms here. probe Later (x O).
variable (Y:Muster G S x d T)
open Cascade
local notation "sN"=>mid N B
abbrev μE(Y: Muster G S x d T):=(μδ Y)
abbrev ιD(Y:Muster G S x d T):=Y.muK
lemma can_f(U:Tab S→FileM (Domain N B) G5)(A:Tab S→DirP (Domain N B))(h:Woven U A k l n p1 p2 p3)(t:ℕ)(hp:k+k≤ t)(v:∀ P P' i, Kind S P P' (pavilion t i)→ U P i=U P' i) : waysS t U:=by
 intro i j x V W k' w
 have ht (p q: SN)(hp: separation x p ≤ k) : A i p q V=A i p q W:=(h.crew i p q).1.reads _ _ (fun z u=> w z ((separation_triangle x p z.1).trans (by omega))) -- hp shadow!
 have hx: dict (A i) x V=dict (A i) x W:=by
    unfold dict; simp only [Pi.sub_apply,Finset.sum_apply]; apply congrArg₂ (·-·) (sum_congr rfl fun i' b=>?_ ) (sum_congr rfl fun i' b=>ht x i' (by simp)); by_cases hV:A i i' x=0; rw [hV]; rfl; exact ht i' x (by rw [separation_comm]; exact h.dawn _ _ _ hV)
 rw [← v _ _ _ k']; have hv:= (h.power i x).1.reads V W (fun i u=> w i (u.trans (by omega))); rw [Pi.add_apply,Pi.add_apply,hx] at hv; exact add_right_cancel hv
end YM.CF.Stake
