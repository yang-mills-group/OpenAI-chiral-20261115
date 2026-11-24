import Knotwise.Spawns
import Knotwise.Thrills
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
open Ione Nacre Both Compass
variable {m:Side}
@[simp] lemma tax_std: taxK (1:staff m)=1:= by unfold taxK taxF taxB; change (if tariffX (1:Signed) then (-1:ℝ) else 1) = 1; rw [tax_i]; norm_num
lemma mirror1 (i:Scree.Hub m) : moveHub (1:Sweep m) i=i:=by
 have h:=step_k (1:Sweep m) (1:Sweep m) i
 have p:= (scope_q (1:Sweep m)).injective -- type?
 rw [one_mul] at h
 first| exact p h|exact p h.symm
#check moldA
#check cast_B
#check tape_B
#check yell_t
lemma enter1(i:Site m):orbitT (1:staff m) i=i:=by
 apply yu; rw [orbitT,node_inspire]; apply (boxA (1:Sweep m)).injective; change boxA (1:Sweep m) ((boxA (1:Sweep m)).symm _) = _; rw [Equiv.apply_symm_apply,sitA]; change _=affine 1 ((assembly m).root 0) (Cube.node i); unfold affine; rw [Signed.act_one,map_zero,add_zero] -- or zero_add
lemma yellE(T:Orbit m):yellA (1:Sweep m) T=T:=by
 have hp:yellA (1:Sweep m) (yellA (1:Sweep m) T)=T:=by
    apply Prod.ext (by change flashA (1:Sweep m) (flashA (1:Sweep m) T.1)=_; rw [rev1, rev1])
    change bun (1:Sweep m) (bun (1:Sweep m) T.2)=_; simpa only [inv_one] using tuftT (1:Sweep m) T.2
 rw [yell_t,one_mul] at hp; exact hp
#check force_V
lemma pecs1 (q:Copy m):pecs (1:staff m) q=q:=by
 funext T
 change suit_Y (1:Sweep m)⁻¹ (q (yellA (1:Sweep m) T))=_
 rw [yellE,inv_one,toon_Q]
abbrev PaysPin(y:staff m)(E E':RegBudget m):Prop:=backing y E'= taxK y • E
lemma pinch(y:staff m)(E E':RegBudget m)(p:PaysPin y E E')(i:Scree.Hub m)(V:Pane m):taxK y • E' (moveHub y.val i) (flashA y.val V)=suit_Y y.val (E i V):=by
 have hu:=congrFun (congrFun p i) V; change suit_Y ((↑y:Sweep _)⁻¹) (E' (moveHub y.val i) (flashA y.val V))= taxK y • E i V at hu
 apply (show Function.Injective (suit_Y ((↑y:Sweep m)⁻¹)) from by intro x z e; have ht:=congrArg (fun T=>suit_Y (↑y) (T:Cipher m)) e; rwa [moon_Y,moon_Y,inv_mul_cancel,toon_Q,toon_Q] at ht)
 rw [map_smul,hu, smul_smul,(prop1 y).2,one_smul,moon_Y,mul_inv_cancel,toon_Q]
#print axioms mirror1
end YM.CF.Py
end
