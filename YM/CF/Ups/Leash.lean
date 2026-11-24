import YM.CF.Ups.Fresh
import YM.CF.Spark.Blush
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
omit p t X
open Haro Tap
lemma dr_K (H:SpaceM)(g:Seat n→SU.E)(v:Phys n): scaleW n H.val (effectK (tradew n g).val v) = effectK (tradew n g).val (scaleW n H.val v):=by
 let Q:=tradew n g; let Z:= -(plankP n H.val)
 have hu: (Q.val)*Z= Z*Q.val:=by
    let W:=love n; apply W.symm.injective; change W.symm _ = W.symm _; rw [map_mul,map_mul]; unfold Z plankP Tap.headW; unfold W Q; rw [map_neg, StarAlgEquiv.symm_apply_apply, Cascade.twine]; simp only [mul_neg,neg_mul,jump_mul]; congr 2; ext1 i; rw [op_kron_mul,op_kron_mul]; simp only [one_mul,mul_one,H.property.firm]; rfl
 have hx:= (show Commute Q.val Z from hu).exp_right; simp_rw [ans, effectK,scaleZ,map_smul]; apply congrArg; change acts (quant (exp Z)) _=_; rw [←act_mul,←act_mul,←quant_mul,←quant_mul, hx.eq]
lemma brace_ps(g:Seat n→SU.E):MeasurePreserving (gird g) (city _) (city _):=(Wilson.prior_gauge g).prod (threads g)
private abbrev famPS(g:Seat n→SU.E): MeasurableEquiv (Orbit n) (Orbit n):= ⟨⟨gird g,gird g⁻¹,gird_inv _,fun i=>by simpa only [inv_inv] using gird_inv g⁻¹ i⟩,(brace_ps g).measurable,(brace_ps g⁻¹).measurable⟩
abbrev Hebi(V:Orbit n→ Phys n):Prop:=∀ g:Seat n→SU.E,∀ᵐ x∂city _,V (gird g x)=effectK (tradew n g).val (V x)
include X p t
lemma loaf_p(U:SpaceM)(h: Hebi (denZ R P F₂)):∀ g: Seat NQ→SU.E,∀ W:Orbit NQ, stove P F₁ R F₂ G T q u U.val (gird g W)=effectK (tradew NQ g).val (stove P F₁ R F₂ G T q u U.val W):=by
 let K:=denZ R P F₂
 intro g W; let z:= ((ratio G).parent); let Gp:= g ∘ z
 have hz: scaleG G Gp=g:=funext (fun i=> congrArg g ((ratio G).embed_parent ..))
 let F (x y):= integrated P F₁ R F₂ G T q u U.val x y; let W':=gird g W; let C: Phys NQ→L[ℝ] Phys NQ:=(acts (quant (tradew NQ g).val)).restrictScalars ℝ
 have he (A:Forest (ratio G))(x y) : carrier P F₁ R F₂ G T q u U.val A x y=scaleW _ U.val (tale (j:=j) G R F₁ F₂ q u T A x y (K y)):=by unfold tale; rw [map_smul]; rfl
 have hp: Integrable (F W) (city N'):= Env.integrableX (snap (buoy X T p t U.val) (X:=fun j=>(W,j)) (by fun_prop)) _
 change (∫ y,F W' y ∂city N')= C (∫ y,F W y ∂city N'); rw [← (show MeasurePreserving (famPS Gp) _ _ from brace_ps Gp).integral_comp' (F W'),← C.integral_comp_comm hp]; apply integral_congr_ae; filter_upwards [h Gp] with i hi
 unfold F integrated W'; rw [map_smul, map_sum]; refine congrArg _ (sum_congr rfl fun F0 _=>?_); simp_rw [he]; change scaleW _ _ (tale (j:=j) G R F₁ F₂ q u T F0 (gird g W) (gird Gp i) (K (gird Gp i)))=C (scaleW _ _ _); rw [show K _= _ from hi,← hz,harp X T p t Gp,dr_K,hz]; rfl -- rw ←hz hits C g? only outside avoids var.c.L? Gp let.
end YM.CF.Pyx
