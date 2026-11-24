import YM.CF.Tale.Fee
import YM.CF.Siete.Cloud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Cube Fock Pastry Tulip
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n l:ℕ}{K C Q R v ε d r η t x:ℝ}{c f: Side}{L:Side}
local notation "G"=> SU.group
lemma romant (k:ℕ)(hp:4≤k)(u:ℝ)(p:1≤u): ∃ C:ℝ,1≤C∧∀ {c f:Side}{E:BudgetPoint}{S: StepData (More c) (More f)}{T:Tube G S}{B: BudgetPoint}{X: Support (More f)} {Y:Support (More c)}{o:Seat f} {V:Pane c}{v:Pane c → Pane f}{L:Side}, Glow E B T u k X Y o V v L→ Nonwrapping X o → k≤ B.order → E.order=k→ 4≤(More f).val→∀ {F:Pane f→ℂ}{Q:ℝ}, MotionB B X o F Q → Signs E (S.ratio.parent o) ((F∘ v) ∘ increment V) (C*(L.val:ℝ)⁻¹^4*Q):=by
 obtain ⟨A,g,h⟩:= wave_v k hp u p; obtain ⟨C,w,hT⟩:=factorial k; refine ⟨C*A,one_le_mul_of_one_le_of_one_le w g,@fun c f P S T B X Y o V v L p ht hh he hN F Q e=>?_⟩
 obtain ⟨Z,t,H⟩:=p.rights; have hy: ((F ∘ v) ∘ increment V)=ᶠ[𝓝 (0:tangD c)] (F∘ increment 1) ∘ Z:= H.mono fun i ⟨g,hg⟩=> by
    change F _=F _; rw [e.depends _ _ (agrees_mono hg (fun x hx=>Finset.mem_union_left _ hx)), e.gaugeV]
 let r:=(L.val:ℝ)⁻¹; have hg:0 ≤ r:=by unfold r; positivity
 have hr:r≤1:= inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr L.property)
 have hv:pingS B.threshold X (increment 1 (Z 0)):=by simpa using t.sails 1 (by simp)
 have hf : ContDiffAt ℝ (k:ℕ∞ω) (F∘ increment 1) (Z 0):=(stirring (1:Pane f) (Z 0) e.depends _ (e.track _ hv)).of_le (Nat.cast_le.mpr hh)
 have hK:0 ≤ Q:=(e.track _ hv).grade; refine ⟨by positivity,he.symm ▸ (hf.comp _ t.flow).congr_of_eventuallyEq hy,fun m b v hz=>?_⟩ -- rewrite dependent he tune
 rw [(hy.iteratedFDeriv ℝ m).eq_of_nhds]; have ha:=b.trans_eq he; let X': Fin 0→tangD c:= fun i=> Fin.elim0 i
 have ht': Promise 2 u r B o X (Z 0):=by simpa using t.grade 0 (by omega) X' (fun i=>Fin.elim0 i)
 refine (advances k _ _ _ hf t.flow (h f X B o (Z 0) F Q r ht hh hN e ht' hg hr t.mark t.sails) _ (fun i _ b=> t.grade i b) m ha v hz).trans ?_
 change _ ≤ C*A*r^4*_; rw [show C*A*r^4*Q=C*(A*r^4*Q) by ring]; exact mul_le_mul_of_nonneg_right (hT _ ha) (by positivity)
end YM.CF.Siete
