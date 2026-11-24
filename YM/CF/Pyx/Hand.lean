import YM.CF.Pyx.Pull
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
abbrev dawnB(F:Oracle (mid M B))(Q: Oracle (mid C B)):Prop:=∀ i:Orbit (mid C B), ∀ W: Phys (mid C B), Q i W=∫ j':Orbit (mid M B),swipeP (j:=j) G R F₁ F₂ q u T F i j' W∂city _
local notation "NQ"=> mid M B
local notation "HQ"=> mid C B
variable {P G R F₁ F₂ T q u}{F:Oracle (mid M B)}{W:Oracle (mid C B)}(b:BoundedT (n:=mid M B) F)
local notation "Qκ"=> swipeP (j:=j) G R F₁ F₂ q u T F
lemma crisp_e (D:Forest (ratio G))(V:Orbit NQ)(U:Orbit HQ):∃ K:Phys HQ→L[ℝ]Phys NQ,tale (j:=j) G R F₁ F₂ q u T D V U=K:=by
 let W:=unionP (YF G F₁ F₂ q u D V U); refine ⟨T.density R.beta U.1 V.1 • ContinuousLinearMap.restrictScalars ℝ ((((sect0 G *chargeA (Thread j) G R.J.M W)⁻¹:ℂ) • pailL (patchQ G) (reefS G true)).comp ((acts (quant (ticketT (Thread j) true R.J.M G W))).comp (hoist (switchG G).symm.toEmbedding ∅))),rfl⟩ -- tune pail.L.P tag
lemma crux_f (V:Orbit NQ)(U:Orbit HQ) (F:Oracle NQ): ∃ K:Phys HQ→L[ℝ]ℂ,swipeP (j:=j) G R F₁ F₂ q u T F U V=K:=by
 choose A v using fun D=> crisp_e (G:=G) (j:=j) (R:=R) (T:=T) (F₁:=F₁) (F₂:=F₂) (q:=q) (u:=u) D V U; let X:=(Fintype.card (Forest (ratio G)):ℝ)⁻¹; refine ⟨(F V).comp (X • ∑ i:Forest _, A i), funext fun w=>?_⟩; unfold swipeP; simp_rw [show ∀ D (i:Phys HQ), tale (j:=j) G R F₁ F₂ q u T D V U i=A D i from fun D i=> congrFun (v D) i]; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,X] -- tune
include b X p t
lemma boardQ : ∃ W:Oracle (mid C B),dawnB (j:=j) G R F₁ F₂ q u T F W∧BoundedT W := by
 let E(U:Orbit HQ)(x:Phys HQ):= ∫ V: Orbit NQ, Qκ U V x∂city _
 have he(x:Phys HQ):Envelope (fun i:Orbit NQ×Orbit HQ=>Qκ i.2 i.1 x):= snob X T p t b (⟨measurable_const,_,fun i=> (le_refl ‖x‖)⟩)
 have hy(x:Phys HQ)(y:Orbit HQ): Integrable (fun i:Orbit NQ=>Qκ y i x) (city _):=Env.integrableX (snap (he x) (X:=fun i=>(i,y)) (by fun_prop)) _
 choose Q H using fun i y=> crux_f (G:=G) (R:=R) (j:=j) (T:=T) (F₁:=F₁) (F₂:=F₂) (q:=q) (u:=u) i y F
 have heq(i y x): swipeP G R F₁ F₂ q u T F y i x (j:=j) = Q i y x:= congrFun (H i y) x
 have ht(y:Orbit HQ): ∃ g:Phys HQ→ₗ[ℝ]ℂ, ∀ x,g x=E y x:=by
    refine ⟨{toFun:=E y,map_add':= ?_, map_smul':= ?_},fun i=> rfl⟩
    · intro i j; unfold E; have hp:= hy i y; have hz:=hy j y; simp_rw [heq] at hp hz ⊢; simp only [map_add]; exact integral_add hp hz
    intro i j; unfold E; simp_rw [heq, map_smul]; exact integral_smul ..
 choose g hg using ht; refine ⟨fun y=>(g y).toContinuousLinearMap,fun i x=> hg i x,fun i=> ?_⟩
 rw [show (fun y:Orbit HQ=> (g y).toContinuousLinearMap i)= fun y=>E y i from funext (fun y=>hg y i)]; exact Env.marginal (he i) _ -- tune g nomen
lemma habitat {R0: GramM (mid M B)}{W:Oracle (mid C B)} (v:dawnB (j:=j) G R F₁ F₂ q u T F W) (hp: Rue.IsleB group R0.p.threshold)(hx: ∀ U:Orbit (mid M B),Rue.FleetS R0.p.threshold U.1→ Scree.stove P F₁ R F₂ G T q u 0 U=denZ R0 P F₁ U) : (∫ z:Orbit NQ,F z (denZ R0 P F₁ z) ∂city _)=∫ z:Orbit HQ,W z (denZ R P F₂ z) ∂city _:=by
 let K(z:Orbit NQ×Orbit HQ):=Qκ z.2 z.1 (denZ R P F₂ z.2)
 let f(U V):= integrated P F₁ R F₂ G T q u 0 U V
 have he: Integrable K ((city _).prod (city _)):= Env.integrableX (snob X T p t b (snap (enter_p X) measurable_snd)) _
 have hv(U V):K (U,V)= F U (f U V):=by
    let d:= denZ R P F₂ V; have hs(i:Forest (ratio G)): tale (j:=j) G R F₁ F₂ q u T i U V d=carrier P F₁ R F₂ G T q u 0 i U V:=by unfold carrier; rw [←ans,Jade.thin_k]
    unfold K swipeP; simp_rw [show ∀ i: Forest (ratio G),tale G R F₁ F₂ q u T i U V (denZ R P F₂ V) (j:=j)=_ from hs]; rfl -- tune nth
 calc
   _ = ∫ z:Orbit NQ, (∫ y:Orbit HQ, K (z,y)∂city _)∂city _:= by
      apply integral_congr_ae; refine ((Measure.quasiMeasurePreserving_fst (μ:=prior group (More NQ)) (ν:=depot NQ)).ae (hp _)).mono fun i p0=>?_ ; dsimp only; simp_rw [hv]; rw [←hx _ p0]; exact ((F i).integral_comp_comm (Env.integrableX (snap (buoy X T p t 0) (X:=fun j=>(i,j)) (by fun_prop)) _)).symm -- orientation check integral_comp_comm: ∫ K(f)=K∫.symm
   _=∫ y:Orbit HQ,(∫ x:Orbit NQ,K (x,y) ∂city _) ∂city _:= (integral_prod K he).symm.trans (integral_prod_symm K he)
   _= _:= by apply integral_congr_ae; exact Eventually.of_forall fun i=> (v i (denZ R P F₂ i)).symm
end YM.CF.Pyx
