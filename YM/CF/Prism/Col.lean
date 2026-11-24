import YM.CF.Prism.Pang
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q R v ε d r η t x:ℝ}{c f: Side}{L:Side}
local notation "G"=> SU.group
open Cube (More)
open Tree
variable {S: StepData (More c) (More f)}{F:Forest S.ratio}{T:Tube G S}{V:Pane c}{k:S.Choices}
theorem returnP (n:ℕ)(u:ℝ)(p:2 ≤ n)(ht:1≤u):∃ C:ℝ,1 ≤ C ∧∀ {c f: Side} {S: StepData (More c) (More f)}{T:Tube G S}{V:Pane c}{P B:BudgetPoint}{X:Hub f}{Y: Support (More c)}{U:Pane c→Pane f}{L:Side}{ℓ:ℕ}{a:ℝ}, Fame B P T u ((L.val:ℝ)⁻¹^2) n X Y V U L ℓ a→ Nonwrapping X.val.2 X.val.1→ n ≤ P.order→ B.order=n→ 4 ≤ (More f).val →∃ g:Seat c→SU.E, Heir.Canvas B (S.ratio.parent X.val.1) ℓ V g n a ∧∀ {F:InkD f}{h b:ℝ}, PressB P X F h b →∀ k:Finset (Dwell f)→ℝ,(∀ i,0 ≤ k i) → (∀ U,BedP P U F X k)→∀ x y:Rock f, Cube.node x.1∈ X.val.2→ Cube.node y.1∈ X.val.2→∀ i l:SU.Slot, Signs B (S.ratio.parent X.val.1) (fun w=>crib F x y i l (Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w)))-crib F x y i l 1) (C*(L.val:ℝ)⁻¹^2*crack k x y):=by
 obtain ⟨K,hK,H⟩:=cent n (by omega); obtain ⟨M,hM,h'⟩:=oracle n p u ht; let C:= Fintype.card SU.Slot
 let Q:= (C:ℝ)*C*carrot n K (2*M); refine ⟨max 1 Q,le_max_left ..,@fun c f S T V P B X Y U L ℓ a l hx hn hB hh=>?_⟩
 obtain ⟨κ,hE,g,hg,W,Θ,hQ,hT,hv⟩:= l; refine ⟨g,hg,@fun F h b hp k h0 ht x y p1 p2 i j=>?_⟩
 let r:=(L.val:ℝ)⁻¹; have hr: 0<r:=by unfold r; positivity
 have hu:r ≤ 1:=inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr L.property)
 let e:=crack k x y; have hp':0 ≤ e:=sum_nonneg fun i _=>sum_nonneg fun i _=>h0 _
 refine high (v:=(C:ℝ)*(C*(carrot n K (2*M)*r^2*e))) (wept hK (show 1 ≤ 2*M by linarith) (@fun c f=>@H c f) W Θ g hp (B:=B) (S:=S) hT hv x y _ le_rfl hr.le hu hB ?_ (fun i j=>?_ ) i j) ?_
 · intro i j; have he:=h' P X.val.2 X.val.1 W (fun V=>crib F x y i j V-crib F x y i j 1) (2*e) r (B.dirBound (S.ratio.parent X.val.1)) 0 hx hn hh (esther X x y i j k hp h0 ht hx hh p1 p2 κ) hr.le hu hQ
   refine ⟨by positivity,hB.symm ▸ he.1,fun j l v u=> (he.2 _ (l.trans_eq hB) v u).trans_eq ?_⟩; ring -- tune
 · have hv:=sig0 (sent 1 k x y (ht 1) (ping_f P X.val.2) h0 i j); simpa using hv
 apply le_trans (b:=Q*r^2*e) _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)) hp'); unfold Q; ring_nf; rfl
end YM.CF.Prism
