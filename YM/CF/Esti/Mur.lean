import YM.CF.Esti.Jet
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open CF.Jet
variable (G:Gauge) (n:ℕ)
lemma stipend(n:ℕ):∃ C:ℝ,0 ≤ C ∧∀ f:Side, Push.Uniform.Inputs (increment (1:Config G f)) n C:=by
 obtain ⟨K,h,H⟩:= Push.Uniform.exp_receipt G n; let C:=Push.Uniform.composeCost n K 1; have hx : 0≤C:=by unfold C Push.Uniform.composeCost; positivity
 refine ⟨C,hx,fun f=>⟨?_,hx,fun i x k=>?_⟩⟩
 · funext i; simp [increment]
 let L: Directions G f →L[ℝ] G.Color:= ContinuousLinearMap.proj i; have hl : ‖L‖ ≤ 1:= L.opNorm_le_bound zero_le_one fun k=> by rw [one_mul]; exact norm_le_pi_norm k _
 have ht: ‖x i‖ ≤ 1:=(norm_le_pi_norm x i).trans k
 have p:=Push.Uniform.Allows.comp (f:=L) (H _ ht) (Push.Uniform.allows_linear hl ht); simp only [increment, Pi.one_apply,mul_one]; exact p -- tune
structure Opium (G:Gauge) (n:ℕ)(S:StepData c f)(a b:ℝ): Prop where
 uses (x:Directions G f)(u:‖x‖<a)(p:S.Choices)(e:Bond c): S.patch.usesMin S.kernel (expandAt (S.ratio.embed e.1) (increment 1 x)) ∧ S.patch.usesBest S.kernel (S.connector (increment 1 x) p.1 e) ∧ Jet.Allows n (fun y:Directions G f=> G.mat (S.prediction (increment 1 y) p e)) x b
lemma strut(K:Teller G)(P:Patch)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind n)(h:3 ≤ n):∃ a b:ℝ,0<a ∧1 ≤ b ∧∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch=P → K.Funds S T → Opium G n S a b:=by
 obtain ⟨C,hC,hF⟩:=stipend G (n+1); let A:=Push.Uniform.predictionRadius P G K.bind n W.lc C W.D W.δ W.r; let B:=Push.Uniform.composeCost n W.W (Push.Uniform.connectorCost P G n W.lc C); refine ⟨if 0<A then A else 1,max 1 B,(by split; assumption; exact zero_lt_one),le_max_left ..,@fun c f S T hP ht => ⟨fun x u p e=>?_⟩⟩ -- tune
 have he:= Push.Uniform.prediction_radius_pos S (hF f) (show 2 ≤ n by omega) W.exp W.log W.focus; rw [ht.knobs,hP] at he; change 0<A at he; rw [if_pos he] at u
 have hv:x∈ Metric.ball 0 (Push.Uniform.predictionRadius S.patch G S.kernel n W.lc C W.D W.δ W.r):=by rw [hP,ht.knobs,mem_ball_zero_iff]; exact u
 have hx:= Push.Uniform.prediction_pay S (hF f) (show 2 ≤ n by omega) W.exp W.log W.focus x hv p e
 have hh:=Push.Uniform.selects S.patch (hF f) W.exp (by omega) W.log (r:=S.ratio.embed e.1) (Metric.ball_subset_ball (min_le_left ..) hv)
 rw [hP] at hx; refine ⟨hh.1,(Push.Uniform.uses_bond S (hF f) (show 2 ≤ n by omega) W.exp W.log x hv p e).1, ⟨hx.1.of_le le_top,fun i p=>(hx.2 i p).trans (le_max_right ..)⟩⟩
open Push.GridApprox AnalyticBridge.LocalGaussian
abbrev sideP (S:StepData c f)(e:Bond c): Set (Site f):= predictorUses S e
lemma connector_p (h:S.patch.Branches S.kernel G)(e:Bond c)(u:S.Choices)(V W:Config G f)(p: Agrees (sideP S e) V W): S.connector V u.1 e=S.connector W u.1 e:=connector_dep S h e u.1 u.1 rfl rfl (fun i p1 p2=> p i (Or.inl p1) (Or.inl p2)) (fun i p1 p2=> p i (Or.inr p1) (Or.inr p2))
lemma bestP(h:S.patch.Branches S.kernel G)(g: Site f→G.El)(V:Config G f)(u:S.Choices)(e:Bond c): S.patch.usesBest S.kernel (S.connector (Lattice.gauge g V) u.1 e)→ S.patch.usesBest S.kernel (S.connector V u.1 e) :=by
 rw [S.updateGauged h]; let a:=g (S.ratio.embed e.1); let b:=g (S.ratio.embed (e.1+step e.2)); let X:=S.connector V u.1 e; let Z(i):=a*X i*b⁻¹; intro he; let Y:= S.patch.best Z; let v:=a⁻¹*Y*b
 change S.patch.bondCost Z Y<_ at he; refine ((S.patch.bond_min _).choose_spec v).trans_lt (lt_of_le_of_lt (le_of_eq ?_) he); unfold Patch.bondCost Z v
 exact sum_congr rfl fun i _ => congrArg (S.patch.weight i * ·) ((G.price_conj a (X i * (a⁻¹*Y*b)⁻¹)).symm.trans (congrArg G.price (by group)))
lemma gauge_t(S:StepData c f)(e:Bond c)(p:S.patch.Branches S.kernel G)(g:Site f→G.El)(t:S.Choices)(V:Config G f): S.prediction (Lattice.gauge g V) t e=g (S.ratio.embed e.1) * S.prediction V t e * (g (S.ratio.embed (e.1+step e.2)))⁻¹:=by rw [StepData.prediction,S.updateGauged p]; exact (S.patch.bond_gauge (h:=p) ..).2
end YM.CF.Esti
