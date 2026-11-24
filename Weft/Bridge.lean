import Weft.Creek
import Palm.Trek
import Knotwise.Spawns
import Finance.Price
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
section
variable {I:Type}[LinearOrder I][Fintype I]
variable (o:I→Site (mid N B))(hrs:Injective (Cube.node ∘ o))
local notation "Pt"=> PairKey I
abbrev sameY (i:PairKey I): Site (mid N B):=o (yard i)
abbrev grainD (o:I→Site (mid N B))(J:Finset (Site (Domain N B))):=univ.filter fun i:I=> node (o i)∈J
include hrs
lemma melt_pipe(i:Pt)(F:Pt→ℂ): (∑ j∈pipe_ζ (Cube.node∘ sameY o) i,F j)= F (pick i.1 false)+ F (pick i.1 true):=by
 let D:= pipe_ζ (Cube.node ∘ sameY o) i; let t (k:Bool):PairKey I:=pick i.1 k
 have h (j k:Pt): (Cube.node ∘ sameY o) j=(Cube.node ∘ sameY o) k ↔ yard j=yard k:= ⟨fun p=>hrs p,fun p=>congrArg (Cube.node ∘ o) p⟩
 have u: D={t false,t true}:=by ext j; unfold D pipe_ζ; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]; rw [h]; exact ⟨fun p=> (show j=t false ∨ j=t true from by cases h:j.2; exact Or.inl (Prod.ext p h); exact Or.inr (Prod.ext p h)),fun z=> z.elim (fun k=> (show yard j=yard (t false) from congrArg yard k)) (fun k=>(show yard j=yard (t true) from congrArg yard k)) ⟩
 have g:t false ∉ ({t true}:Finset Pt):= fun g=>Bool.noConfusion (congrArg (altQ (I:=I)) (mem_singleton.mp g))
 change ∑ j∈D,_=_; rw [u,sum_insert g,sum_singleton]
abbrev stone (U W D:ℝ)(k l:Bool):ℂ:= if k then if l then (D:ℂ) else 0 else if l then (D*W:ℝ) else (U:ℂ)
abbrev cobble (I:Type)(U W D:ℝ)(i j:PairKey I):ℂ:=stone U W D i.2 j.2
lemma toV_o(C:Bool→Bool→ℂ)(z:Key Pt):Roots.toV_C (Cube.node ∘ sameY o) (fun i j=> C i.2 j.2) z=fiber C z:= funext fun _=> melt_pipe o hrs _ _
lemma step_key(U W D:ℝ)(z:Key Pt):Roots.toV_C (Cube.node ∘ sameY o) (cobble I U W D) z=fiber (stone U W D) z:=toV_o o hrs _ _
#check toV_C
lemma toVr (U W D:ℝ)(z:Key Pt)(B:ℝ)(hu:|W|≤1)(v:0≤D)(e:|U|≤B)(p:∀ i, ‖z i‖≤ 2)(j:Pt):‖toV_C (Cube.node ∘ sameY o) (cobble I U W D) z j‖ ≤ 2*(B+D):=by
 have hp:0≤B:= (abs_nonneg U).trans e
 have ht(k:ℝ)(i:Pt): ‖(k:ℂ)*z i‖≤2*|k|:= by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm (abs k)]; exact mul_le_mul_of_nonneg_right (p i) (abs_nonneg _)
 rw [step_key o hrs]; unfold fiber Drift.entry stone; cases h:j.2<;> simp only [altQ,h,Bool.false_eq_true, ↓reduceIte] -- IDs
 · refine (norm_add_le _ _).trans ((add_le_add (ht U _) (ht (D*W) _)).trans ?_); rw [abs_mul,abs_of_nonneg v]; nlinarith only [v,e,mul_le_mul_of_nonneg_left hu v]
 rw [zero_mul,zero_add]; refine (ht D _).trans ?_; rw [abs_of_nonneg v]; linarith
end
#print axioms melt_pipe
end YM.CF.Py
end
