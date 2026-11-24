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
def dilC {t:ℝ}(p:0<t):Cord S≃ᵐ Cord S:= let V:= (dialK t p.ne' (Directions G₀ (Domain P B))).toHomeomorph.toMeasurableEquiv; (MeasurableEquiv.refl (Arena.Tab S)).prodCongr (((MeasurableEquiv.refl (Config G₀ (Domain P B))).prodCongr V).prodCongr (MeasurableEquiv.refl (Ids (mid P B)))) -- tune
local notation "μ"=> (plummy S v)
-- density V at radius; under dilation
abbrev silk(S:StepData (Domain N B) (Domain P B))(ν:Measure (Directions SU.group (Domain P B))):Measure (Cord S):= (paperMeas (Arena.Tab S)).prod (((suit S).prod ν).prod (depot _))
abbrev stem_c := silk S volume
abbrev yardK (i:Side)(v:ℝ):=(grainS SU.group v)^Fintype.card (Bond i)
abbrev balm_c(y:Directions SU.group (Domain P B)):ℝ:= ∏ i,peakG SU.group (y i)
def riceK (oN:ℝ)(y:Directions SU.group (Domain P B)):ℝ≥0∞:=if ‖y‖ ≤ oN then (yardK (Domain P B) oN)⁻¹ * ENNReal.ofReal (balm_c y) else 0 -- tune side ambiguity
-- chart density `.prod`.
local instance :SigmaFinite (Girt.suit S):=by unfold Girt.suit; infer_instance
instance crown_l :SigmaFinite (stem_c S):=by unfold stem_c silk; infer_instance
include h
lemma earn_s: tableG G₀ (Bond (Domain P B)) v=(volume:Measure (Directions G₀ (Domain P B))).withDensity (riceK v):=by
 let D:= Bond (Domain P B); let F':=yardK (Domain P B) v
 have hF:F' ≠ 0:= pow_ne_zero _ (grain_pos _ h).ne'; have hp:F'≠⊤:= ENNReal.pow_ne_top (measure_ne_top (rice SU.group) _)
 let Z:= tableG G₀ D v; let K:= rice G₀; let Bπ:= Measure.pi (fun _:D=>K); have he:F' • Z= Bπ.restrict (closedBall (0:Directions SU.group (Domain P B)) v):=by
    rw [meal SU.group h,show Appel.surface SU.group D v=closedBall 0 v from ?_]; ext i; rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg h.le]; simp [Appel.surface,Set.mem_pi,mem_closedBall_zero_iff]
 let A(w:SU.group.Color):= ENNReal.ofReal (peakG SU.group w); let L:= (volume:Measure SU.group.Color); have hm:Measurable A:=by unfold A peakG; fun_prop
 let g(w:Directions SU.group (Domain P B)):= ENNReal.ofReal (balm_c w); have hh:Bπ= volume.withDensity g:=by
    have hf: K= L.withDensity A:=perk SU.group; haveI : SigmaFinite (L.withDensity A):=hf ▸ inferInstanceAs (SigmaFinite (rice SU.group)); haveI :∀ _ : D,SigmaFinite (L.withDensity A) :=fun _=>inferInstance
    unfold Bπ; rw [hf,← Work.F05.piDensity _ (fun (_:D)=> A) (fun _=>hm)]; congr 1 -- tune
    funext W; unfold g balm_c; rw [ENNReal.ofReal_prod_of_nonneg]; intro i _; exact mul_nonneg (inv_nonneg.mpr Next.SectorChange.Gaussian.dome_pos.le) (Real.exp_pos _).le
 let B':=closedBall (0:Directions SU.group (Domain P B)) v; have hE:Z=F'⁻¹ • (F' • Z):=by rw [smul_smul,ENNReal.inv_mul_cancel hF hp,one_smul]
 change Z=_; rw [hE,he,hh, restrict_withDensity ?_, ←withDensity_indicator isClosed_closedBall.measurableSet,←withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hF)] -- signature tune
 congr 1; funext i; unfold riceK; by_cases p: ‖i‖ ≤ v
 · rw [Pi.smul_apply, Set.indicator_of_mem (mem_closedBall_zero_iff.mpr p),if_pos p]; rfl
 rw [if_neg p,Pi.smul_apply, Set.indicator_of_notMem (mt mem_closedBall_zero_iff.mp p),smul_zero]
 exact isClosed_closedBall.measurableSet
omit h
lemma balm_t:Continuous (balm_c (P:=P) (B:=B)):=by unfold balm_c peakG; fun_prop
lemma rice_m(v:ℝ): Measurable (riceK (P:=P) (B:=B) v):= by unfold riceK; exact Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const) (measurable_const.mul (balm_t.measurable.ennreal_ofReal)) measurable_const -- tune
local notation "δ"=> riceK (P:=P) (B:=B)
include h S N P B
lemma seal_F: plummy S v= (stem_c S).withDensity (fun x : Cord S=>riceK v x.2.1.2):=by
 let f(p : Config G₀ (Domain P B) × Directions G₀ (Domain P B)):= δ v p.2; have he:Measurable f:= (rice_m _).comp measurable_snd
 unfold plummy stem_c springT silk; rw [earn_s (P:=P) (B:=B) h, prod_withDensity_right (rice_m _),prod_withDensity_left he]; exact prod_withDensity_right (he.comp measurable_fst) -- probe argu
omit h
lemma dial_p (h:0<t): Measure.map (dilC S h).symm (stem_c S)= ENNReal.ofReal (t^(Module.finrank ℝ (Directions SU.group (Domain P B)))) • stem_c S:=by
 let V:= (dialK t h.ne' (Directions SU.group (Domain P B))).toHomeomorph.toMeasurableEquiv; let X:=volume (α:=Directions SU.group (Domain P B)); let σ:= ENNReal.ofReal (t^(Module.finrank ℝ (Directions SU.group (Domain P B))))
 have ht: X.map V.symm=σ • X:=by
    rw [show ((V.symm:Directions G₀ (Domain P B)→ _) )= (fun i=> t⁻¹ • i) from rfl,map_addHaar_smul X (inv_pos.mpr h).ne', abs_inv,inv_pow]
    unfold σ; rw [abs_inv, inv_inv,abs_of_nonneg (by positivity)] -- orientation
 -- generic lift.prod
 have hf: Measure.map (dilC S h).symm (stem_c S)=silk S (X.map V.symm):=by
    unfold stem_c silk; let w:= Girt.suit S; let Z:= depot (mid P B); let M:=paperMeas (Arena.Tab S)
    change Measure.map (Prod.map id (Prod.map (Prod.map id V.symm) id)) (M.prod ((w.prod X).prod Z))=M.prod ((w.prod (X.map V.symm)).prod Z)
    rw [← map_prod_map _ _ measurable_id ((measurable_id.prodMap V.symm.measurable).prodMap measurable_id),← map_prod_map _ _ (measurable_id.prodMap V.symm.measurable) measurable_id,←map_prod_map w X measurable_id V.symm.measurable]; simp
 rw [hf,ht]; unfold silk stem_c; rw [Measure.prod_smul_right,Measure.prod_smul_left,Measure.prod_smul_right] -- tune
end YM.CF.Plume
