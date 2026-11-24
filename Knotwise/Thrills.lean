import Knotwise.PriceTag
import YM.CF.Tuft.Quip
import WinterX.Camera
import Compass.Pavilion
import Knotwise.Gesture
import WinterX.Instrument
import WinterX.Pantry
import YM.CF.Fans.Cause
import Thin.CapsEarn
import YM.CF.Fans.Elm

/- Adapted from YM/CF/Fans/Elm.lean for the NoSlip, capped ScaledV use below. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
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
variable {d e η t z gg A B':ℝ} {j k k' m n l:ℕ}
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
open Trees Footprint Iva Eire
open Jade
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open Neon Mew Vow Tap Rive Bake Larch Salt Ione Sour Moto
open scoped Mew
open Both
-- Feynman transfer interface. γΓ is κPass. Key submission at fine Y $f/g/r. inputs.Xo offset. exact stage backend same for all. capacities flexible via callers. Expose Stage$ device per submission as existential with commitments obeying simultaneous comparison through same equivalence; can `Classical.choose` based solely on inputs, no future Pledge.
variable {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q:Chi}
local notation "Nk"=> mid N B
local notation "Pk"=> mid P B
variable (Wξ:Op SU.Slot)(v1 kF Wκ Δ_ f0 g0 g1 g2 Q₁ Q₂ Q₃ cΦ Zμ:ℝ)
variable (price_R:ℝ→ℝ)(θc:ℝ)(gK:ℕ)
variable {J:Type}[LinearOrder J][Fintype J]{h Kv Zv:ℝ}(ζP:J→Site (mid N B))(E' S':Key J → RegBudget (mid P B))(Yf:Key J→ ForceBudget (mid P B))(A_:J→ ArcΦ)(Dϕ:J→ℝ)
local notation "σ_p" => (Cube.node ∘ Hove.heel G ∘ ζP)
-- returns oracle.Binder ABI. Fintype & LOrder for LabelΩ need avoid instance paths.
open Compass Both
variable {Wξ v1 kF Wκ Δ_ f0 g0 g1 g2 Q₁ Q₂ Q₃ cΦ Zμ gK θc}
variable {AΦ:Cusp (mid N B)→ Cusp (mid N B)}{Kc:Cusp (mid N B)}{γt:ℝ}
open Lattice.PlaqAxes AnalyticBridge.VerifiedReset
open Nacre 
variable {n1 m1:Side}(Gs:Ratio n1 m1)(s:staff n1)(hGee:Odd Gs.count.val)
def roles {n1:Side}(Gs:Ratio n1 m1)(s:staff n1):staff m1:=⟨reSweep Gs (↑s),s.property⟩
include hGee
lemma claw (v:Site n1): Cube.node (Hove.heel Gs v)=(Rush.ratio Gs).embed (Cube.node v):=by
 unfold Hove.heel; rw [embed_node Gs hGee]; simp
lemma orbit_heel(v:Site n1): orbitT (roles Gs s) (Hove.heel Gs v)= Hove.heel Gs (orbitT s v):=by
 apply yu; unfold orbitT; rw [node_inspire,claw Gs hGee,claw Gs hGee,node_inspire]; apply (boxA (roles Gs s).val).injective; rw [Equiv.apply_symm_apply,sitA, show (roles Gs s).val.s=s.val.s from rfl,show (roles Gs s).val.b=Gs.embed s.val.b from rfl,←Skye.reA Gs s.val]; nth_rw 1 [←Equiv.apply_symm_apply (boxA s.val) (Cube.node v),sitA]; unfold affine; rw [←Ratio.signed]; exact map_add (Rush.ratio Gs).root _ _
#check Ratio.signed
#print axioms orbit_heel
omit hGee
variable {mQ pQ:Side}(F:RegBudget (mid n1 mQ))(K:ForceBudget (mid n1 mQ))(Y:GramM (mid n1 mQ))
-- unperturbed. use existing Tuft.Pant_W? import Quip. Provides via Shelf later.
lemma nun_royal (p:Pant_W (N:=n1) (B:=mQ) Y)(o:Site (mid n1 mQ))(s:Sweep (mid n1 mQ)):
    nun_ω Y.F (inspire s o)= Spire.payZ s (nun_ω Y.F o) := by
 have he:= (p s).1 (Moto.Φrap (mid n1 mQ) o 10) 1; rw [rapX,flash_one] at he
 unfold nun_ω Moto.ωX Taxi.lifeH; rw [he,pane_tax]; unfold Spire.payZ Scroll.cSignX; split; exact Complex.exp_conj _; rfl -- tune conj
lemma Bolten (p:Pant_W (N:=n1) (B:=mQ) Y):∃ c:ℝ,∀ o:Site (mid n1 mQ),nun_ω Y.F o=c:=by
 let a:= nun_ω Y.F (0:Site (mid n1 mQ)); obtain ⟨v,u,f,r⟩:= stabilizes (0:Site (mid n1 mQ)) (1:Signed) Anchored.one true
 have he:= nun_royal Y p 0 (↑v); rw [show inspire v.val 0=0 from r] at he -- inspire vs orbitT. use via rfl
 have hp:wageZ v.val=true:=by unfold wageZ; rw [f,u,det_i]; rfl
 unfold Spire.payZ at he; rw [hp] at he
 have ht:a=(a.re:ℂ):=Complex.ext rfl (by have h:=congrArg Complex.im he; change a.im= -a.im at h; change a.im=0; linarith)
 refine ⟨a.re,fun t=>?_⟩
 obtain ⟨u,Q,vS,y⟩:= Compass.nodesTo (0:Site (mid n1 mQ)) t
 have hx:=nun_royal Y p 0 u.val
 have hy:wageZ u.val=false:=by unfold wageZ; rw [vS,Q,det_i]; rfl
 rw [show inspire u.val 0=t from y] at hx; unfold Spire.payZ at hx; rw [hy] at hx; exact hx.trans ht
end YM.CF.Py
end
