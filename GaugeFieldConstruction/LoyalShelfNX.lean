import YM.SU5.Assay.Dawn
import YM.SU5.Thin.Operators
-- bridge issuing width-varying Dawn stage and genuine independent markField resolution prices
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2800
set_option linter.unusedSectionVars false
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{D N:Doorway}{M:P.Menagerie}
variable {F G:SampleDose}{s n:ℕ}{o:Orders}(w:P.Dawn R x s n D N o F G M)(Z W:Lead.Clan)
lemma exposeFrontNX(P:Spine)(Z:Lead.Clan)(n s t:ℕ)(F:SampleDose): P.prepared t (P.refront n Z s) F=P.thinOutgoing Z s n t F:=rfl
lemma exposeForeNX(P:Spine)(Z:Lead.Clan)(n s t:ℕ)(F:SampleDose): P.prepared t (P.fore (P.refront n) Z s) F=P.thinIncoming Z s n t F:=rfl
local notation "Y"=>P.electro M
local notation "ψ" t:max=>P.singleState 3 t x
include w
lemma properFlowNX (ε:ℝ)(p:0<ε): ∀ᶠ j:ℕ×ℕ in atTop,∀t≥max j.1 j.2,
    ‖P.singleState 3 t x (P.thinIncoming Z j.1 n t F*P.thinOutgoing W j.2 n t G)-star (P.electro M Z)*P.electro M W‖≤ε:=by
    have ht:= w.hits.map (show Continuous (fun y:CrossRead=> y Z W) from (continuous_apply W).comp (continuous_apply Z))
    filter_upwards [ht.earnest (Metric.ball_mem_nhds _ p)] with j q t h
    have hk: ‖P.spiritBoth R x t (P.fore (P.refront n) Z j.1) F (P.refront n W j.2) G-star (P.electro M Z)*P.electro M W‖ < ε:= by rw [←dist_eq_norm]; exact Metric.mem_ball.mp (q.2.2 _ h) -- tune metacoercion
    rw[P.spirit_pair] at hk
    exact hk.le
private lemma singleFilterNX {X:Type}[TopologicalSpace X]{f:ℕ→ℕ→X}{y:X}{S:Set X}(p:Tendsto (fun i=>f i.1 i.2) (Escrow id) (𝓝 y))(u:S∈𝓝 y):∀ᶠ j:ℕ in atTop,∀t≥j,f j t∈S:=by
 have ht:= p.eventually u; change Filter.Eventually (fun i:ℕ×ℕ=> f i.1 i.2 ∈ S) (_ ⊓ _) at ht
 rw[eventually_inf_principal] at ht
 obtain ⟨b,q⟩:=eventually_atTop.mp ht
 filter_upwards [eventually_ge_atTop (max b.1 b.2)] with j h t y
 exact q (j,t) ⟨le_of_max_le_left h, (le_of_max_le_right h).trans y⟩ y
lemma properSingleNX (ε:ℝ)(p:0<ε):∀ᶠ j:ℕ in atTop,∀ t≥j,
   ‖P.singleState 3 t x (P.thinIncoming Z j n t F)-star (P.electro M Z)‖≤ε ∧ ‖P.singleState 3 t x (P.thinOutgoing W j n t G)-P.electro M W‖≤ε:=by
   let A:= w.rise.1
   have ht:= (A.early.scene R A.walls.1 id Z tendsto_id).together
   have h':=(A.late.scene R A.walls.2 id W tendsto_id).together
   rw [(P.sip_read _ _ Z A.walls.1 A.old.oil).2] at ht
   rw [(P.sip_read _ _ W A.walls.2 A.old.water).1] at h'
   have ho:=singleFilterNX w (f:=fun s t => P.spiritOne R x t (P.fore (P.refront n) Z s) F) ht (Metric.ball_mem_nhds _ p)
   have hx:=singleFilterNX w (f:=fun s t=> P.spiritOne R x t (P.refront n W s) G) h' (Metric.ball_mem_nhds _ p)
   filter_upwards [ho,hx] with j v d t h
   have hk:=v t h; have hg:=d t h
   rw[Metric.mem_ball,dist_eq_norm,P.spirit_single] at hk hg; exact ⟨hk.le,hg.le⟩
#print axioms properSingleNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
