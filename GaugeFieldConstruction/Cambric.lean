import GaugeFieldConstruction.Sync
import YM.CF.Muse.Hours
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
variable {c:Side}{E:Type}[MeasurableSpace E] {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D]
-- common Screen currency.Turn
structure JasperEq(μ:Measure E)(F:E→D→ℂ)(G:D→ℂ)(n:ℕ):Prop where
 lip :∀ t,ContDiffAt ℝ (↑n:ℕ∞ω) (F t) 0
 wall : ContDiffAt ℝ (↑n:ℕ∞ω) G 0
 rides :∀ i≤ n, ∀ z:Fin i → D,Integrable (fun t=> iteratedFDeriv ℝ i (F t) 0 z) μ ∧ iteratedFDeriv ℝ i G 0 z =∫ t, iteratedFDeriv ℝ i (F t) 0 z ∂μ
variable {μ:Measure E}{n:ℕ} {F X:E→ D → ℂ}{G Y:D→ℂ}
namespace JasperEq
lemma tally (v:JasperEq μ F G n)(p:JasperEq μ X Y n): JasperEq μ (F+X) (G+Y) n:=by
 refine ⟨fun i=> (v.lip i).add (p.lip i),v.wall.add p.wall,fun i h z=>?_⟩
 let H:= fun i':E=>iteratedFDeriv ℝ i (F i') 0 z; let K:= fun i':E=>iteratedFDeriv ℝ i (X i') 0 z; have hk:(i:ℕ∞ω) ≤ (n:ℕ∞ω):= Nat.cast_le.mpr h
 obtain ⟨wf,hf⟩:= v.rides i h z; obtain ⟨wg,hg⟩:=p.rides i h z
 have hh (t:E): iteratedFDeriv ℝ i ((F+X) t) 0 z= H t+K t:=by rw [Pi.add_apply,iteratedFDeriv_add_apply ((v.lip t).of_le hk) ((p.lip t).of_le hk)]; rfl
 simp_rw [hh]; refine ⟨wf.add wg,?_⟩; rw [iteratedFDeriv_add_apply (v.wall.of_le hk) (p.wall.of_le hk)]; change iteratedFDeriv ℝ i G 0 z+ iteratedFDeriv ℝ i Y 0 z=_; rw [hf,hg,integral_add wf wg]
lemma zeroP (μ:Measure E)[IsFiniteMeasure μ]: JasperEq μ 0 (0:D→ℂ) n:=by
 refine ⟨fun _=>contDiffAt_const,contDiffAt_const,fun i h t=>?_⟩; have he(i): iteratedFDeriv ℝ i (fun _:D=> (0:ℂ)) 0=0:=by
    by_cases hp:i=0; · subst i; exact ContinuousMultilinearMap.ext fun i=>by simp
    rw [iteratedFDeriv_const_of_ne hp]; rfl
 simp_rw [Pi.zero_apply]; change Integrable (fun _=> iteratedFDeriv ℝ i (fun _:D=> (0:ℂ)) 0 t) μ∧iteratedFDeriv ℝ i (fun _:D=> (0:ℂ)) 0 t= ∫ a:E, iteratedFDeriv ℝ i (fun _:D=> (0:ℂ)) 0 t∂μ; rw [he]; simp
lemma sums {I:Type*}(p:I→E→D→ℂ)(q:I→ D →ℂ)[IsFiniteMeasure μ](T:Finset I)(h:∀i∈T,JasperEq μ (p i) (q i) n): JasperEq μ (∑ i∈T,p i) (∑ i∈T,q i) n:=by
 induction T using Finset.induction_on with
 | empty=>simp_rw [sum_empty]; exact zeroP _
 | insert _ _ H ih=> rw [sum_insert H,sum_insert H]; exact (h _ (mem_insert_self ..)).tally (ih fun i p=> h _ (mem_insert_of_mem p))
lemma prepW [IsFiniteMeasure μ](v:JasperEq μ F G n)(p:ℝ)(hp:0 ≤ p)(h:∀ᵐ i∂μ,Allows n (F i) 0 p)(u:μ Set.univ ≤1): Allows n G 0 p:=by
 refine ⟨v.wall,fun i k=>ContinuousMultilinearMap.opNorm_le_bound hp (fun t=> ?_)⟩
 let P:=∏ i:Fin i,‖t i‖; have hP:0≤P:=Finset.prod_nonneg fun i _=> norm_nonneg _
 obtain ⟨W,H⟩:= v.rides i k t; rw [H]; refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae W.norm (integrable_const (p*P)) ?_).trans ?_)
 · filter_upwards [h] with i' v; exact ((iteratedFDeriv ℝ i (F i') 0).le_opNorm t).trans (mul_le_mul_of_nonneg_right (v.norm_le _ k) hP)
 rw [MeasureTheory.integral_const, smul_eq_mul]; apply mul_le_of_le_one_left (mul_nonneg hp hP); exact (ENNReal.toReal_mono (by simp) u).trans_eq ENNReal.toReal_one
end JasperEq
end YM.CF.Oath
end
