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
variable {Clock:∀ (J:Type)[LinearOrder J][Fintype J],(J→Site (mid N B))→capture J (mid P B)→capture J (mid P B)→attach J (mid P B)→(J→ArcΦ)→(J→ℝ)→Key J→Cusp (mid N B)}
variable {hh:ℝ}
variable (Bq: Hourly V U X Y S G G₀ G₁ Wξ q kL hh v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ Q₁ Q₂ Q₃ cΦ θc gK AΦ Kc γt Clock)(he:1≤hh)
variable {I I':Type}[LinearOrder I][Fintype I][LinearOrder I'][Fintype I'](σ:I→Site (mid N B))(E Eo:capture I (mid P B))(Y₀:attach I (mid P B))(F:I→ArcΦ)(U₁:I→ℝ)(qt:MissionH Y hh R.L G σ E Eo Y₀ F U₁ Q₁ Q₂ Q₃ cΦ)
    (σ':I'→Site (mid N B))(M Mo:capture I' (mid P B))(F':attach I' (mid P B))(Z':I'→ArcΦ)(W₀:I'→ℝ)(t':MissionH Y hh R.L G σ' M Mo F' Z' W₀ Q₁ Q₂ Q₃ cΦ)
open Classical
-- Key singleton perturbation marker. relation same kind on signs.$B_clock.
abbrev singletonK {I:Type}[LinearOrder I][Fintype I](i:I)(u:ℝ):Key I:= Function.update 0 i (u:ℂ)
variable (y:staff (mid N B))(j:I)(j':I')
local notation "F₁"=> Clock I σ E Eo Y₀ F U₁
local notation "F₂"=> Clock I' σ' M Mo F' Z' W₀
local notation "nX"=> mid N B
local notation "zA" r:max=>singletonK j r
local notation "zB" r:max=> singletonK j' r
local notation "a"=> taxK y -- collides variable a ℝ non-$use
variable (hs : ∀ u:ℝ, ‖u‖≤1 →
    sees (reSweep (G:Ratio (mid N B) (mid P B)) (↑y)) E Eo Y₀ (singletonK j u) M Mo F' (singletonK j' (taxK y*u))) -- notation args may inaccessible. sees only P B implicit problem.
-- scalar axis input relation, may weaken to germ. comparison of Cusp.Phase etc then Cold.E
lemma legalS (j:I)(u:ℝ)(p:‖u‖ ≤1): singletonK j u∈ hill I:=fill_I roots _ (mem_closedBall_zero_iff.mpr (Complex.norm_real _ |>.trans_le p))
include V Bq qt t' he hs
set_option synthInstance.maxSize 28000 in
lemma costKin (u:ℝ)(v:‖u‖≤1)(K1 K2:Cusp (mid N B))(p:PotZ y.val K1 K2):
 let X1 (u:ℝ):= AΦ ((F₁) (zA u)); let X2 (u:ℝ):= AΦ ((F₂) (zB (a*u)))
 PhaseR y.val (restoring X.p AΦ (F₁) (zA u)) (restoring X.p AΦ (F₂) (zB (a*u))) ∧ ForceR y.val (budgetR (roomV X.p (Fex (X1 u)) (X1 u) K1)) (budgetR (roomV X.p (Fex (X2 u)) (X2 u) K2)):=by
 intro X1 X2
 have ht1:= Bq.hand I σ E Eo Y₀ F U₁ qt; have ht2:=Bq.hand I' σ' M Mo F' Z' W₀ t'
 unfold Soloing at ht1 ht2
 have hv(u:ℝ)(p:‖u‖≤1): ‖(a*u)‖ ≤1:=by rw [norm_mul,Real.norm_eq_abs (r:=taxK _),(prop1 y).1,one_mul]; exact p
 have hz (u:ℝ)(v:‖u‖≤1) := Bq.compare I I' σ E Eo Y₀ F U₁ σ' M Mo F' Z' W₀ qt t' (zA u) (legalS _ _ v) (zB (a*u)) (legalS _ _ (hv u v)) y.val (hs u v)
 have hI (u:ℝ)(v:‖u‖ ≤1):= (ion_A X.p y.val _ _ _ _ AΦ (ht1.1 (zA u) (legalS _ _ v)) (ht2.1 (zB (a*u)) (legalS _ _ (hv u v))) (hz u v) K1 K2 p he).2
 refine ⟨fun T i=>?_, (hI u v).2⟩
 have h0:= hI 0 (by simp); have hv':∀ {κ:Type}[LinearOrder κ][Fintype κ](i:κ),singletonK i 0=0:=by intro κ _ _ i; funext j; by_cases p:i=j; subst i; simp[singletonK]; rw [singletonK, update_of_ne (Ne.symm p)]; -- PiZero
 rw [mul_zero,hv' _,hv' _] at h0
 unfold restoring; rw [Pi.sub_apply,Pi.sub_apply, Pi.sub_apply,Pi.sub_apply, map_sub]; exact congrArg₂ (·-·) ((hI u v).1 T i) (h0.1 T i)
#check Hourly.hand
#check legalS
end YM.CF.Py
end
