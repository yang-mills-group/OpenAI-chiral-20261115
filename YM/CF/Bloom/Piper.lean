import YM.CF.Pyx.Tree
import YM.CF.Bloom.Fennel
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
variable {P G R F₁ F₂ T q u}{F:Oracle (mid M B)}{W:Oracle (mid C B)}(b:BoundedT (n:=mid M B) F)
open Haro Tap Cascade
abbrev sweepM(H:SpaceM)(X:Oracle n):Oracle n:= fun x =>(X x).comp (scaleW n H.val)
lemma frock(H:SpaceM)(p:Loyal F) : Loyal (sweepM H F):=by
 intro g y v; let Q:=tradew _ g; let Z:= -(plankP (mid M B) H.val) -- tune line implicit N
 have hu: (Q.val)*Z= Z*Q.val:=by
    let W:=love (mid M B); apply W.symm.injective; change W.symm _ = W.symm _; rw [map_mul,map_mul]; unfold Z plankP Tap.headW; unfold W Q; rw [map_neg, StarAlgEquiv.symm_apply_apply, Cascade.twine]
    simp only [mul_neg,neg_mul,jump_mul]; congr 2; ext1 i; rw [op_kron_mul,op_kron_mul]; simp only [one_mul,mul_one, H.property.firm]; rfl -- tune
 have hx:= (show Commute Q.val Z from hu).exp_right; have hp := p g y (scaleW _ H.val v)
 unfold sweepM; simp only [ContinuousLinearMap.comp_apply]; rw [←hp]; change F _ (scaleW _ H.val (acts (quant Q.val) v))= F _ (acts (quant Q.val) (scaleW _ H.val v)); apply congrArg; simp_rw [ans,scaleZ,map_smul]; apply congrArg; change acts (quant (exp Z)) _= _; rw [←act_mul,←act_mul,←quant_mul,←quant_mul, hx.eq]
lemma barQ(H:SpaceM)(p:BoundedT F):BoundedT (sweepM H F):=fun x=> p (scaleW _ H.val x)
include X p t b
lemma ticket (H:SpaceM){R0: GramM (mid M B)}{W:Oracle (mid C B)} (v:dawnB (j:=j) G R F₁ F₂ q u T (sweepM H F) W) (hp: Rue.IsleB group R0.p.threshold)(hx: ∀ U:Orbit (mid M B),Rue.FleetS R0.p.threshold U.1→ Scree.stove P F₁ R F₂ G T q u H.val U=denZ R0 P F₁ U) : (∫ z:Orbit NQ,F z (denZ R0 P F₁ z) ∂city _)=∫ z:Orbit HQ,W z (denZ R P F₂ z) ∂city _:=by
 let U:=scaleW NQ H.val; let Qκ:= swipeP (j:=j) G R F₁ F₂ q u T (sweepM H F); let K(z:Orbit NQ×Orbit HQ):=Qκ z.2 z.1 (denZ R P F₂ z.2)
 let f(V W):= integrated P F₁ R F₂ G T q u H.val V W
 have he: Integrable K ((city _).prod (city _)):= Env.integrableX (snob X T p t (barQ H b) (snap (enter_p X) measurable_snd)) _
 have hv(V W):K (V,W)= F V (f V W):=by
    let d:= denZ R P F₂ W; have hs(i:Forest (ratio G)): U (tale (j:=j) G R F₁ F₂ q u T i V W d)=carrier P F₁ R F₂ G T q u H.val i V W:=by unfold carrier tale; rw [map_smul]; rfl
    unfold K Qκ swipeP; change F V (U _) = F V _; rw [map_smul,map_sum]; exact congrArg (F V) (congrArg _ (sum_congr rfl (fun i _=>hs i))) -- tune
 calc
   _ = ∫ z:Orbit NQ, (∫ y:Orbit HQ, K (z,y)∂city _)∂city _:= by
      apply integral_congr_ae; refine ((Measure.quasiMeasurePreserving_fst (μ:=prior group (More NQ)) (ν:=depot NQ)).ae (hp _)).mono fun i p0=>?_ ; dsimp only; simp_rw [hv]; rw [←hx _ p0]; exact ((F i).integral_comp_comm (Env.integrableX (snap (buoy X T p t _) (X:=fun j=>(i,j)) (by fun_prop)) _)).symm -- orientation check integral_comp_comm: ∫ K(f)=K∫.symm
   _=∫ y:Orbit HQ,(∫ x:Orbit NQ,K (x,y) ∂city _) ∂city _:= (integral_prod K he).symm.trans (integral_prod_symm K he)
   _= _:= by apply integral_congr_ae; exact Eventually.of_forall fun i=> (v i (denZ R P F₂ i)).symm
end YM.CF.Pyx
