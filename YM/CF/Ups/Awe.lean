import YM.CF.Ups.Canon
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
variable (P G R F₁ F₂ q u)
local notation "NQ"=> mid M B
local notation "HQ"=> mid C B
-- discharge continuous perturb oriented emitter.Rank.Scope θ budget. O complex. Exact projection to ℓ findings.Basis.S.G.Integrable B.No regular covariance assumptions. Stone
open Reed Girt Haro
-- point evaluation of C
lemma camp_x {Z: Type} [MeasurableSpace Z] (O:Z→Phys n→L[ℝ]ℂ){A B:Z→FC (Single n)}(T:LampC O A B)(p q:Z)(g:Seat n→ SU.E)(h:∀ y:Phys n,O q (effectK (tradew _ g).val y)=O p y): A q=twist (quantU (tradew _ g)) (A p)∧ B q=twist (quantU (tradew _ g)) (B p):=by
 let V:=quantU (tradew n g); let x:=mateK n; have ht:acts V.val x=x:=mastC g
 refine (insight (T.cryO q) (symψ g (T.cryO p)) (T.cryE q) (symψ g (T.cryE p)) fun z=> ?_).symm
 let v:= acts (star V.val) z; have hp: acts V.val v=z:= by unfold v; rw [←act_mul,(show V.val*star V.val=1 from V.property.2),act_one]
 rw [←map_add,←hp,T.lamp]; refine (h v).trans ((T.lamp p v).symm.trans ?_); change inner ℂ x _=inner ℂ x (acts (twist V (A p+B p)) (acts V.val v)); rw [←Fock.swivel]; have hv:= act_unit_inner V x (acts (A p+B p) v); rw [ht] at hv; exact hv.symm
-- relative opacity f
abbrev RealC {N:Side}(O:Oracle N):Prop:= ScalarC O
variable {P G R F₁ F₂ T q u}{F:Oracle (mid M B)}{W:Oracle (mid C B)}(b:BoundedT (n:=mid M B) F)
local notation "Kp"=> mid C B
local notation "Wf"=> mid M B
include j
lemma sip_Q(W:SpaceM)(x:Orbit Wf)(y: Orbit Kp)(v:Phys Kp) : swipeP (j:=j) G R F₁ F₂ q u T (sweepM W F) y x v=F x (Fps (j:=j) G F₁ F₂ q u T R.beta W x y v):=by
 let U:=scaleW Wf W.val; let V(i: Forest (ratio G)):= sPout (j:=j) G F₁ F₂ q u x y i v; let S:= Fintype.card (Forest (ratio G)); let d:=T.density R.beta y.1 x.1; unfold swipeP; simp_rw [show ∀ D: Forest (ratio G), tale (j:=j) G R F₁ F₂ q u T D x y v=d • V D from fun i=> rfl]; apply congrArg (F x);
 change U ((S:ℝ)⁻¹ • (∑ i,d • V i))= d • U ((S:ℝ)⁻¹ • (∑ i:Forest (ratio G),sPout (j:=j) G F₁ F₂ q u x y i) v); rw [← Finset.smul_sum,←map_smul,smul_comm d, ContinuousLinearMap.sum_apply]
lemma χPS {Q:Oracle (mid C B)}{W:SpaceM}(C: dawnB (j:=j) G R F₁ F₂ q u T (sweepM W F) Q)(h:RealC F):RealC Q:=by
 have hp(x:Scree.Phys Wf)(z:ℂ):scaleW _ W.val (z • x)=z • scaleW _ W.val x:=by rw [ans,ans]; unfold scaleZ; dsimp only; rw [map_smul, smul_comm z]
 intro i x z; rw [C,C]; simp_rw [sip_Q]; rw [← integral_smul]; refine integral_congr_ae (Eventually.of_forall fun y=>?_ ); dsimp only; rw [← (h y ((Fps G F₁ F₂ q u T R.beta W y i (j:=j)) x) z)]; apply congrArg (F y); let U:=scaleW Wf W.val; let V:=gentK (j:=j) G F₁ F₂ q u y i; let c:= T.density R.beta i.1 y.1
 change c • U (V _) = z • c • U _; rw [map_smul V,hp,smul_comm]; rfl -- hp U
end YM.CF.Pyx
