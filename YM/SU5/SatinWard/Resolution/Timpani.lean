import YM.SU5.SatinWard.Resolution.Frame
import YM.SU5.SatinWard.Resolution.Recital
import YM.SU5.SatinWard.Resolution.PseudoSpin
import YM.SU5.SatinWard.Resolution.FF
import YM.SU5.SatinWard.Resolution.Column

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

-- End and turns. Preliminary rank receipts. Don't replace operator norm on preparation.
namespace SoulField
open Mezzo
variable {j:Axis}{U V:UNI SU.Slot}(h:Registrar U)(v:Registrar V)
local notation "Jι"=> Wage3
abbrev Soul:=Coords Wage3
noncomputable abbrev Reg : Soul ≃ₗ[ℝ] chiralModule:= Θc.equivFun.symm
noncomputable abbrev GuardF (h:Registrar U) : chiralModule→ₗ[ℝ]chiralModule where
 toFun a:= ⟨twist U a.val,by
    have q:ChiralX 0 a.val:= a.property; refine (show ChiralX 0 _ from ⟨fun i=>?_,?_⟩)
    · refine (h i) ▸ (show Commute (twist U a.val) (twist U (SU.matter i).val) from (q.1 i).map (twist U))
    rw [←map_star,q.2]⟩ -- fill
 map_add' x y:=Subtype.ext (map_add (twist U) _ _)
 map_smul' x y:=Subtype.ext (map_smul (twist U) _ _)
noncomputable def rotor(h:Registrar U):Soul→ₗ[ℝ]Soul:= (Reg.symm.toLinearMap.comp (GuardF h)).comp Reg.toLinearMap
include h
lemma rotor_pay (z:Soul): (Reg (rotor h z)).val=twist U (Reg z).val:=by unfold rotor; rw [LinearMap.comp_apply,LinearMap.comp_apply]; change (Reg (Reg.symm _)).val=_; rw [Reg.apply_symm_apply]; rfl
lemma rotor_undo(z:Soul): rotor h.inv (rotor h z)=z:=by
 apply Reg.injective; apply Subtype.ext; rw [rotor_pay,rotor_pay]; exact twist_inv ..
omit h in
lemma rotor_one(z:Soul): rotor Registrar.one z=z:=by
 apply Reg.injective; apply Subtype.ext; rw [rotor_pay, one_des]
include v in
lemma rotor_mul (z:Soul):rotor (h.mul v) z=rotor h (rotor v z):=by
 apply Reg.injective; apply Subtype.ext; simp only [rotor_pay,twist_formula, Submonoid.coe_mul,star_mul]; rw [mul_assoc]; simp [mul_assoc]
lemma rotor_redo(z:Soul):rotor h (rotor h.inv z)=z := by
 rw [←rotor_mul, show rotor (h.mul h.inv)=rotor Registrar.one from ?_,rotor_one]
 apply LinearMap.ext; intro a; apply Reg.injective; apply Subtype.ext; rw [rotor_pay,rotor_pay,mul_inv_cancel]


noncomputable abbrev costD:ℝ:=‖Reg.toLinearMap.toContinuousLinearMap‖
noncomputable abbrev costC:ℝ:=‖Reg.symm.toLinearMap.toContinuousLinearMap‖
noncomputable def surgeBudget:ℝ:=1+costD*costC
omit h
lemma surge_herald : 1≤ surgeBudget:= le_add_of_nonneg_right (mul_nonneg (by exact ContinuousLinearMap.opNorm_nonneg _) (by exact ContinuousLinearMap.opNorm_nonneg _))
include h
lemma surge_power (z:Soul): ‖rotor h z‖ ≤ surgeBudget*‖z‖:=by
 have he: ‖Reg (rotor h z)‖=‖Reg z‖:=(congrArg (fun A:EndC=> ‖A‖) (rotor_pay h z)).trans (twist_norm ..)
 have hx:= Reg.symm.toLinearMap.toContinuousLinearMap.le_opNorm (Reg (rotor h z))
 change ‖Reg.symm _‖ ≤ costC* ‖Reg _‖ at hx
 rw [Reg.symm_apply_apply,he] at hx
 refine hx.trans ((mul_le_mul_of_nonneg_left (?_:‖Reg z‖ ≤ costD*‖z‖) (show 0≤ costC from by exact ContinuousLinearMap.opNorm_nonneg _) ).trans ?_)
 exact Reg.toLinearMap.toContinuousLinearMap.le_opNorm _
 unfold surgeBudget; rw [add_mul, mul_comm costD, mul_assoc]; rw [show costC*(‖z‖*costD)=costD*(costC*‖z‖) by ring]
 exact le_add_of_nonneg_left (mul_nonneg zero_le_one (norm_nonneg z))
-- rank: chiralModule via product
omit h
local notation "HE"=> ↥chiralModule
local notation "MZ"=> Mezzo.TuneM
def unitH : HE:=⟨1,(show ChiralX _ _ from ⟨fun i=> Commute.one_left _,star_one _⟩)⟩
lemma hUnit : unitH≠0:=fun f=> one_ne_zero (α:=EndC) (congrArg Subtype.val f) -- Prop
instance present_income : Nonempty Wage3:=by
 have ht:Nontrivial HE:= ⟨unitH,0,hUnit⟩
 exact ⟨⟨0,Module.finrank_pos⟩⟩
noncomputable def keepsake (A B:MZ)(p:star A=A)(b:star B=B):HE:=⟨sonnet A B,(show ChiralX _ _ from ⟨fun i=> (firmSuite A B i).symm,by rw [←coeffStar,p,b]⟩)⟩
lemma paid_shape (a:HE):let X:=a.val; let A:=passage X ac ac; let B:=passage X ab ab; star A=A ∧ star B=B ∧ X=sonnet A B:=by
 intro X A B; have he:= (show ChiralX 0 X from a.property); have hp:= collaborations X (fun i=> (he.1 i).symm); have hh:star X=X:=he.2; let hu:= coeffInj (show sonnet (star A) (star B)=sonnet A B from (coeffStar A B).trans (by change star (sonnet (passage X ac ac) (passage X ab ab))= sonnet (passage X ac ac) (passage X ab ab); rw [←hp]; exact hh)); exact ⟨hu.1,hu.2,hp⟩ -- scope collision names
end SoulField
end ShapeLab
end YM.CF.QuadClock
