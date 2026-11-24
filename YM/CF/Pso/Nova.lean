import YM.CF.Pso.Book
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
variable {C E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][TopologicalSpace C][FirstCountableTopology C]
include h
lemma room_a:∃ k:ℝ,0≤k ∧∀ y:Directions SU.group (Domain P B),(riceK v y).toReal ≤ k:=by
 let c:=closedBall (0:Directions SU.group (Domain P B)) v; obtain ⟨x,p,hx⟩:= (isCompact_closedBall _ v).exists_isMaxOn (show Set.Nonempty c from ⟨0,mem_closedBall_self h.le⟩) balm_t.continuousOn
 let a:=yardK (Domain P B) v; refine ⟨(a⁻¹* ENNReal.ofReal (balm_c x)).toReal,ENNReal.toReal_nonneg,fun y=>?_⟩ ; unfold riceK; split; rename_i hg; swap; · rw [ENNReal.toReal_zero]; exact ENNReal.toReal_nonneg
 refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (grain_pos _ h).ne')) ENNReal.ofReal_ne_top) (mul_le_mul_left' (ENNReal.ofReal_le_ofReal (hx (mem_closedBall_zero_iff.mpr hg))) _) -- covariant k.
variable (F:C→ Cord S→E) (w:C→ℝ)(hw:∀ x,0<w x)(p:Continuous w)(u:∀ x,Continuous (fun z=> F z (dilC S (hw z) x))) (hc:∀ x, Integrable (F x) (plummy S v))(K:ℝ)(v_:0 ≤ K)(hp:∀ x,∀ᵐ y ∂plummy S v, ‖F x y‖≤ K)
local notation "φ" z:max=> Ck S v (w z)
include h hw p u hc hp v_
lemma oak_c : Continuous (fun z=> ∫ i,F z i ∂plummy S v):=by
 apply continuous_iff_continuousAt.mpr; intro x; let d(z:C)(i:Cord S):= (Ck S v (w z) i).toReal; let G'(z:C)(i:Cord S):E:= d z i • F z (dilC S (hw z) i)
 have hk(z:C): Integrable (G' z) (stem_c S)∧ (∫ i,G' z i ∂stem_c S)= (∫ i,F z i∂plummy S v)∧∀ᵐ i∂ stem_c S,‖G' z i‖ ≤ d z i*K:= mintF S h (hw z) (F z) (hc z) K (hp z)
 let c:= 2*w x; let k:=w x/2; let a:= v/k; have hx:= hw x; have hf:0<k:=half_pos hx; have hu:0<a:=div_pos h hf; let V:= nest_v S a; let hn(d:Cord S):=d.2.1.2; have he(z:C)(j:Cord S) : Continuous (fun z=>w z • hn j):=p.smul continuous_const
 let l:=Module.finrank ℝ (Directions G₀ (Domain P B)); obtain ⟨A,hA,Bp⟩:= room_a (P:=P) (B:=B) h; let t(x:Cord S):= V.indicator (fun _=> c^l * A * K) x; have ht: Integrable t (stem_c S):= (integrable_indicator_iff (pure_m S a)).mpr (integrableOn_const (aero S a).ne)
 rw [show (fun z=>∫ i,F z i∂plummy S v) =_ from (funext fun z=>(hk z).2.1.symm)]; refine continuousAt_of_dominated (bound:=t) (Eventually.of_forall fun z=> (hk z).1.aestronglyMeasurable) ?_ ht ?_
 · have hν: ∀ᶠ z:C in 𝓝 x, w z ∈ Set.Ioo k c:=p.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds (show w x ∈ Set.Ioo k c from ⟨half_lt_self hx,by unfold c; linarith⟩))
   filter_upwards [hν] with z vb; filter_upwards [(hk z).2.2] with i s; apply s.trans
   have hi (u:C):‖w u • hn i‖=w u * ‖hn i‖:=norm_smul_of_nonneg (hw u).le _
   unfold d Ck t; by_cases m : i∈ V
   · rw [Set.indicator_of_mem m, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (hw _).le _)]
     exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (hw _).le vb.2.le _) (Bp _) ENNReal.toReal_nonneg  (pow_nonneg ((hw z).le.trans vb.2.le) l)) v_ -- multiplication last nonneg expects D
   have hm:¬(‖w z • i.2.1.2‖≤v):=by intro p; rw [hi] at p; apply m; exact (le_div_iff₀ hf).mpr ((mul_comm ..).le.trans ((mul_le_mul_of_nonneg_right vb.1.le (norm_nonneg _)).trans p))
   rw [Set.indicator_of_notMem m, riceK,if_neg hm]; simp
 have hl:0<v/w x:=div_pos h hx; filter_upwards [omni_l S _ hl] with i hG; have hi(z):ContinuousAt (fun y=>w y • hn i) z:=(he x i).continuousAt
 let α:=yardK (Domain P B) v; have hm(z):‖w z • hn i‖=w z * ‖hn i‖:= norm_smul_of_nonneg (hw z).le _
 apply ContinuousAt.smul ?_ (u i|>.continuousAt); unfold d Ck; simp_rw [ENNReal.toReal_mul]; apply ContinuousAt.mul (((p.pow _).continuousAt).congr_of_eventuallyEq (Eventually.of_forall fun z => ENNReal.toReal_ofReal (pow_nonneg (hw z).le _))); change ContinuousAt (fun z=> (riceK v (w z • hn i)).toReal) x
 unfold riceK; obtain he'|he':=lt_or_gt_of_ne hG
 · have hg: ‖w x • hn i‖<v:=by rw [hm]; exact (mul_comm ..).trans_lt ((lt_div_iff₀ hx).mp he')
   let g(U:ℝ):= max 0 U; have ha(u:ℝ): (ENNReal.ofReal u).toReal=g u:=by
      by_cases h:0≤u; · rw [ENNReal.toReal_ofReal h]; exact (max_eq_right h).symm
      rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt (lt_of_not_ge h)), ENNReal.toReal_zero]; exact (max_eq_left (le_of_lt (lt_of_not_ge h))).symm
   apply (((continuousAt_const (y:= (α⁻¹).toReal)).mul (((show Continuous g from continuous_const.max continuous_id).continuousAt).comp (balm_t.continuousAt.comp (hi x)))).congr_of_eventuallyEq); filter_upwards [((hi x).norm).eventually (gt_mem_nhds hg)] with z y; rw [if_pos (le_of_lt y),ENNReal.toReal_mul,ha]; rfl
 have hg : v< ‖w x • hn i‖:= by rw [hm,mul_comm]; exact (div_lt_iff₀ hx).mp he'
 apply (ContinuousAt.congr_of_eventuallyEq (f:=fun _=>0) continuousAt_const _); filter_upwards [((hi x).norm).eventually (lt_mem_nhds hg)] with z y; rw [if_neg (not_le.mpr y),ENNReal.toReal_zero]
end YM.CF.Plume
