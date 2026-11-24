import YM.CF.Pyx.Like
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
-- full gauge covariance for diagnostics off all paths. lin tests not always gauge invariant; Wilson-tree from Flavor at shared center.Muni. transport preserves.
variable {F:Oracle (mid M B)}{V':Oracle (mid C B)}
include p t X
local notation "NQ"=> mid M B
local notation "N'"=> mid C B
lemma harp (g:Seat N' → SU.E)(A:Forest (ratio G))(W:Orbit NQ)(V:Orbit N')(Q:Phys N'): tale (j:=j) G R F₁ F₂ q u T A (gird (scaleG G g) W) (gird g V) (effectK (tradew N' g).val Q)= effectK (tradew NQ (scaleG G g)).val (tale G R F₁ F₂ q u T A W V Q (j:=j)) :=by
 obtain ⟨b,x,a,U,U'⟩:= X.cap; let Z':= scaleG G g; let Y' :=YF G F₁ F₂ q u A; let B:= Y' W V
 have hv:Y' (gird Z' W) (gird g V)=july G g B:=by
    unfold B Y' Girt.YF july; change (seine _ _ _ _ _ _,F₁ (_, _))=(Lattice.gauge g _,Lattice.gauge _ _); rw [U.rev,show F₂ (gird g V)=_ from U'.rev _ _ _, brake_g G q u A (X.power.symm ▸ ho)] -- tune
 obtain ⟨s,h,l,d,mHp,k,y⟩:= X.wick; let Vb:= T.covary t g R.beta V.1 W.1
 have ht: scaleG G g=g ∘ T.ratio.embed:=by rw [p]; rfl
 unfold tale; rw [show YF .. =_ from hv,rain_c G g d _ X.power _ s k mHp (ambient _ _ X.pe y (X.trial ..)) Q]
 unfold effectK; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul]; apply congrArg (· • _); rw [ht]; exact congrArg _ Vb -- type
omit p t X
def Loyal (F:Oracle n):Prop:= ∀ g y V, F (gird g y) (effectK (tradew n g).val V)=F y V
lemma gird_inv(g:Seat n→ SU.E)(V:Orbit n):gird g⁻¹ (gird g V)=V:=by
 unfold gird; apply Prod.ext
 · funext i; dsimp [Lattice.gauge]; group
 exact threads_T g V.2
private lemma loom_e(g:Seat n→SU.E): MeasurePreserving (gird g) (city _) (city _):= (Wilson.prior_gauge g).prod (threads g)
private abbrev fam(g:Seat n→SU.E): MeasurableEquiv (Orbit n) (Orbit n) := ⟨⟨gird g,gird g⁻¹,gird_inv _,fun i=>by simpa only [inv_inv] using gird_inv g⁻¹ i⟩,(loom_e g).measurable,(loom_e g⁻¹).measurable⟩
include p t X
lemma cruise_g (F:Oracle (mid M B)) (k:Loyal F) (g:Seat N'→SU.E)(y:Orbit NQ)(x:Orbit N')(V: Phys N'): swipeP (j:=j) G R F₁ F₂ q u T F (gird g x) (gird (scaleG G g) y) (effectK (tradew N' g).val V)= swipeP G R F₁ F₂ q u T F x y V (j:=j):=by
 let U':=scaleG G g; let Q(v: Phys NQ):= effectK (tradew NQ U').val v; let V':=(acts (quant (tradew NQ U').val)).restrictScalars ℝ; unfold swipeP; simp_rw [harp X T p t g _ y x]; change F _ (_ • ∑ i: Forest (ratio G),V' _) =_; rw [← _root_.map_sum,←map_smul]; exact k _ _ _
lemma heart(p':dawnB (j:=j) G R F₁ F₂ q u T F V') (w:Loyal F): Loyal V':=by
 intro s g v; let Q':=effectK (tradew N' s).val v; let Y(i:Orbit NQ):= swipeP G R F₁ F₂ q u T F (gird s g) i Q' (j:=j); let C:=scaleG G s
 rw [p',p']; rw [← (show MeasurePreserving (fam C) _ _ from loom_e C).integral_comp' Y]; apply integral_congr_ae; exact Eventually.of_forall fun i=>cruise_g X T p t F w s i g v
end YM.CF.Pyx
