import YM.CF.Girt.Bridge
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
include p t X
lemma tidesR(F:Forest (ratio G)): RG.Envelope fun x:Orbit (mid M B)×Orbit (mid C B) => T.density R.beta x.2.1 x.1.1 • waveV P G R F₁ F₂ q u F x.1 x.2:=by
 have he:RG.Envelope fun x:Orbit (mid M B)× Orbit (mid C B)=>T.density R.beta x.2.1 x.1.1:=by
    unfold StepData.density; exact RG.Envelope.sum univ (fun i (x:Orbit (mid M B) × Orbit (mid C B))=>taggedKernel T R.beta i x.2.1 x.1.1) (fun i=>env_tagged R.beta i t (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_fst)) -- tuner
 exact Env.scale he (entersL X F)
omit X t p
def scaleW (n:Side)(Q: Op SU.Slot): Phys n →L[ℝ] Phys n:= let Z:=exp (-(Tap.plankP n Q)); (((skyGlow (mateK n) Z (mateK n))⁻¹:ℂ) • acts (quant Z)).restrictScalars ℝ
lemma ans (Q:Op SU.Slot)(x: Phys n): scaleW n Q x=scaleZ Q x:=rfl
include X t p
lemma bureau(Q:Op SU.Slot)(F:Forest (ratio G)): RG.Envelope (uncurry (carrier P F₁ R F₂ G T q u Q F)):=by
 let K:=scaleW (mid M B) Q
 let H:=fun x:Orbit (mid M B)×Orbit (mid C B)=> T.density R.beta x.2.1 x.1.1 • waveV P G R F₁ F₂ q u F x.1 x.2
 have hz:= pole_w H K K.continuous (tidesR X T p t F); rw [show uncurry (carrier P _ _ _ _ _ _ _ Q F)= (fun x=>K (H x)) from funext (fun x=> (by unfold H; rw [map_smul]; rfl))]; exact hz
lemma buoy(Q:Op SU.Slot):RG.Envelope (uncurry (integrated P F₁ R F₂ G T q u Q)):=by
 refine Env.scale (H:=fun x:Orbit (mid M B)× Orbit (mid C B)=> ((Fintype.card (Forest (ratio G)):ℝ)⁻¹)) (Envelope.const _) (f:=fun x=>∑ F,carrier P F₁ R F₂ G T q u Q F x.1 x.2) ?_ ; exact Env.total (g:=fun F=> uncurry (carrier P F₁ R F₂ G T q u Q F)) _ (fun i=>bureau X T p t Q i)
omit t p
omit X in
private abbrev tags (g:Seat n→ E): MeasurableEquiv (Ids n) (Ids n):= ⟨⟨threadG g,threadG g⁻¹,threads_T _, by intro i; simpa using threads_T g⁻¹ i⟩,(threads _).measurable,(threads _).measurable⟩
omit X
variable (P G R F₁ F₂ q u) in
def ropeG (F: Forest (ratio G))(V:Orbit (mid M B))(U:Pane (mid C B)):=∫ z:Ids (mid C B),waveV P G R F₁ F₂ q u F V (U,z) ∂depot _
include X
lemma grain (F:Forest (ratio G))(V:Orbit (mid M B)): RG.Envelope (ropeG P G R F₁ F₂ q u F V):=by
 let f(z:Ids (mid C B)× Pane (mid C B)):= waveV P G R F₁ F₂ q u F V (z.2,z.1); exact Env.marginal (g:=f) (snap (X:=(fun x:Ids (mid C B) × Pane (mid C B)=> (V,x.2,x.1))) (entersL X F) (by fun_prop)) _
lemma rope_p (F:Forest (ratio G))(V:Orbit (mid M B))(U:Pane (mid C B))(g:Seat (mid C B)→ E)(v:∀ i:Seat (mid M B),g ((ratio G).embed i)=1): ropeG P G R F₁ F₂ q u F V (gauge g U)= ropeG P G R F₁ F₂ q u F V U:=by
 unfold ropeG; rw [← (show MeasurePreserving (tags g) _ _ from threads g).integral_comp' (fun i:Ids (mid C B)=> waveV P G R F₁ F₂ q u F V (gauge g U,i))]; apply integral_congr_ae; filter_upwards with x; exact hut_k X F V g v (U,x)
end YM.CF.Girt
