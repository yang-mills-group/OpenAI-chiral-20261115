import YM.CF.Girt.Lane
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
variable (V:Orbit (CSide M B))(Q:Op SU.Slot)(Z:Allocation G₀ T x W)
-- true tag-aux gauge slicing. keep wave renormalization optional. ∑ over same F uniformly remains.
lemma peakV(F:Forest T.ratio) :
 (∫ i,carrier P F₁ R F₂ G T q u Q (p ▸ F) V i ∂city _) = scaleW _ Q (∑ A:Stores T,output Z F R.beta (ropeG P G R F₁ F₂ q u (p ▸ F) V) A V.1):=by
 let f:=waveV P G R F₁ F₂ q u (p ▸ F) V; let U(i: Orbit (mid C B)):=T.density R.beta i.1 V.1 • f i; let L:=ropeG P G R F₁ F₂ q u (p ▸ F) V; let W'(u:Pane (mid C B)):=T.density R.beta u V.1 • L u; let M:=scaleW (mid M B) Q
 have hc(i : Orbit (mid C B)):carrier P F₁ R F₂ G T q u Q (p ▸ F) V i=M (U i):= by unfold U; rw [map_smul]; rfl
 have hb: Integrable U (city _):= Env.integrableX (f:=U) (snap (X:=fun x=> (V,x)) (tidesR X T p t (p ▸ F)) (measurable_const.prodMk measurable_id)) _
 simp_rw [hc]; rw [M.integral_comp_comm hb, city, integral_prod U hb]
 apply congrArg M; have ht:∫ (x:Pane (mid C B)), (∫ z:Ids _, U (x,z) ∂depot _) ∂prior SU.group _=T.push R.beta L V.1:=by
    unfold U; simp_rw [integral_smul]; rfl
 rw [ht]; clear ht
 have he(i:T.Choices): Integrable (through T F R.beta V.1 (fun _ a=> L (F.drape a)) i) (F.order _):= through_integrable F R.beta V.1 (fun _ a=> L (F.drape a)) t _ (Env.integrableX (snap (grain X (p ▸ F) V) F.continuous_drape.measurable) _)
 have hh: Integrable W' (prior G₀ _):=StepData.push_slice (T.isKernel t R.beta) _ _ (Env.integrableX (grain X _ V) _) -- tune name
 unfold StepData.push; change (∫ i,W' i ∂_)=∑ A, Z.column A F V.1 (through T F R.beta V.1 (fun _ a=> L (F.drape a))); rw [F.pack _ hh ?_,Z.partitions t F V.1 _ he]
 unfold tagTotal; rw [← integral_finsetSum _ fun i _=> he i]; apply integral_congr_ae; filter_upwards with i; unfold W' StepData.density; rw [Finset.sum_smul]; rfl
 intro g he D; have ht:L (gauge g D)=L D:=rope_p X _ V _ _ (by rw [←p]; exact he); have hp:Lattice.gauge (g ∘ T.ratio.embed) V.1=V.1:=by funext; simp [Lattice.gauge,he]
 unfold W'; rw [ht]; apply congrArg (· • L D); have hv:=T.covary t g R.beta D V.1; rw [hp] at hv; exact hv
lemma valley : Scree.stove P F₁ R F₂ G T q u Q V= scaleW (mid M B) Q (((Fintype.card (Forest T.ratio):ℝ)⁻¹) • ∑ F:Forest T.ratio,∑ A:Stores T,output Z F R.beta (ropeG P G R F₁ F₂ q u (p ▸ F) V) A V.1):=by
 have hx(F:Forest (ratio G)): Integrable (carrier P F₁ R F₂ G T q u Q F V) (city _):= Env.integrableX (snap (X:=fun x=>(V,x)) (bureau X T p t Q F) (measurable_const.prodMk measurable_id)) _
 unfold Scree.stove integrated; rw [integral_smul,integral_finsetSum _ (fun F _=>hx F),map_smul,map_sum]
 let f:= Equiv.cast (congrArg Forest p); rw [Fintype.card_congr f,← Equiv.sum_comp f] -- tune
 congr 1; refine sum_congr rfl ?_; intro i _; change (∫ _, _ ∂_) = _; rw [show f i=(p ▸ i) from ?_, peakV X T p t V Q Z]; -- tune
 refine (show ∀ {α β:Ratio (Domain M B) (Domain C B)} (g:α=β)(i: Forest α),Equiv.cast (congrArg Forest g) i=(g ▸ i) from ?_) p i
 intro α β p i; subst p; rfl
end YM.CF.Girt
