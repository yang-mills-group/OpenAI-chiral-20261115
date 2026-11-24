import YM.CF.Pso.Velt
import YM.CF.Plume.Roll
import YM.CF.Pso.Dual
import YM.CF.Plume.Cord
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open scoped Classical ENNReal NNReal
open Girt
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
local notation "d₀"=> Directions SU.group (Domain P B)
open Measure
variable {v t:ℝ} (h:0<v)
local notation "μ"=> (plummy S v)
local instance :IsProbabilityMeasure (Girt.suit S):=by unfold Girt.suit; infer_instance
abbrev Ck (s w:ℝ)(X:Cord S):ℝ≥0∞:= ENNReal.ofReal (w^(Module.finrank ℝ (Directions SU.group (Domain P B)))) * riceK s (w • X.2.1.2)
lemma formD (s w:ℝ): Measurable (Ck S s w):= measurable_const.mul ((rice_m _).comp ((measurable_snd.fst.snd).const_smul w))
variable {w:ℝ}(p:0<w)
local notation "M"=> stem_c S
local notation "δ"=> Ck S v w
include p h
lemma stalk_e: MeasurePreserving (dilC S p) ((stem_c S).withDensity (Ck S v w)) (plummy S v):=by
 let V:=dilC S p; let A(x:Cord S):=riceK v x.2.1.2; let W:ℝ≥0∞:=ENNReal.ofReal (w^(Module.finrank ℝ (Directions SU.group (Domain P B)))); have hm:Measurable A:=(rice_m _).comp (measurable_snd.fst.snd); let f(z:Cord S):= V z; have hh(a:Cord S): δ a=W*A (V a):=rfl
 suffices H:MeasurePreserving V.symm (plummy S v) ((M).withDensity δ) from H.symm
 refine ⟨V.symm.measurable,?_⟩; rw [seal_F S h]; change ((M).withDensity A).map V.symm=(M).withDensity δ
 let X:= (M).map V.symm
 ext s hs; rw [Measure.map_apply V.symm.measurable hs, withDensity_apply _ (V.symm.measurable hs)]
 have he: (M).map V.symm=W • M:=dial_p S p
 rw [funext hh, show (fun x:Cord S=>W*A (V x))=W • (A∘ V) from rfl, withDensity_smul W (hm.comp V.measurable),← withDensity_smul_measure,←he,withDensity_apply _ hs, setLIntegral_map hs (hm.comp V.measurable) V.symm.measurable]; simp -- tune
lemma zed_l (z:Cord S): Ck S v w z<⊤:=ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by unfold riceK; split; exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (grain_pos _ h).ne'))) ENNReal.ofReal_lt_top; norm_num)
omit h p
abbrev nest_v (g:ℝ):Set (Cord S):={i|‖i.2.1.2‖≤g}
lemma pure_m(g:ℝ):MeasurableSet (nest_v S g):= measurableSet_le (measurable_snd.fst.snd).norm measurable_const
lemma loot_m (U:Set (Directions SU.group (Domain P B))): M ((fun i:Cord S=>i.2.1.2)⁻¹' U)= volume U:=by
 let Y:=TeamY (mid P B); unfold stem_c silk; rw [show ((fun i:Cord S=>_)⁻¹' U)= Set.univ ×ˢ ((Set.univ ×ˢ U) ×ˢ Set.univ) from ?_]; swap; · ext; simp
 rw [Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,measure_univ,measure_univ, measure_univ]; simp
lemma aero(g:ℝ): M (nest_v S g)<⊤:=by
 rw [show nest_v S g=(fun i:Cord S=>i.2.1.2)⁻¹' closedBall 0 g from Set.ext fun i=> mem_closedBall_zero_iff.symm,loot_m]; exact measure_closedBall_lt_top
lemma omni_l (g:ℝ)(p:0<g):∀ᵐ x:Cord S∂stem_c S, ‖x.2.1.2‖ ≠ g:=by
 let S':=sphere (0:Directions SU.group (Domain P B)) g; have he: M ((fun i:Cord S=>i.2.1.2)⁻¹' S')=0:=by rw [loot_m]; exact addHaar_sphere_of_ne_zero _ _ p.ne'
 filter_upwards [compl_mem_ae_iff.mpr he] with x h; exact fun i=> h (mem_sphere_zero_iff_norm.mpr i)
include p h
lemma mintF {C:Type}[NormedAddCommGroup C][NormedSpace ℝ C](f:Cord S→C)(hg:Integrable f (plummy S v))(D:ℝ)(hd:∀ᵐ t:Cord S∂ plummy S v,‖f t‖ ≤ D) : let g(x:Cord S):= f (dilC S p x)
 let F(x:Cord S):=(Ck S v w x).toReal • g x
 Integrable F (stem_c S)∧ (∫ i,F i ∂stem_c S)=∫ i,f i∂plummy S v∧ ∀ᵐ i∂ stem_c S, ‖F i‖≤ (Ck S v w i).toReal * D :=by
 intro g F; let hk:= stalk_e S h p; let I:= hk.integrable_comp_emb (dilC S p).measurableEmbedding|>.mpr hg; have hi: Integrable g ((M).withDensity δ):= I
 let vC:= formD S v w; have hv:∀ᵐ i∂M,δ i < ⊤:= Eventually.of_forall (zed_l S h p); have hE: Integrable F M:=(integrable_withDensity_iff_integrable_smul' vC hv).mp hi; refine ⟨hE,(integral_withDensity_eq_integral_toReal_smul vC hv g).symm.trans (hk.integral_comp (dilC S p).measurableEmbedding f),?_⟩
 filter_upwards [(ae_withDensity_iff vC).mp (hk.quasiMeasurePreserving.ae hd)] with i t; by_cases e:δ i=0; · simp only [F,e]; simp
 unfold F; rw [norm_smul,Real.norm_of_nonneg ENNReal.toReal_nonneg]; exact mul_le_mul_of_nonneg_left (t e) ENNReal.toReal_nonneg
end YM.CF.Plume
