import YM.SU5.Six.ChamberCosts
import YM.SU5.Six.ReachDoors
import YM.SU5.Six.Charges
import YM.SU5.Six.Rates
import YM.SU5.Six.Elected
import YM.SU5.Six.MSplit
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
open scoped ContDiff
open Casting
-- beware namespace contention DoorCost.chamber
abbrev AlleySpace:= DoorCost.Chamber 3
abbrev starsPart : (ℝ× AlleySpace)≃ᵐ Vantage:= DoorCost.merge 3
abbrev clockR(v:Vantage):ℝ:= v (3:Axis)
abbrev skyR (v:Vantage):AlleySpace:=fun i:Fin 3=> v i.castSucc
lemma clock_stars (p:ℝ×AlleySpace): clockR (starsPart p)=p.1:= DoorCost.lastAt ..
lemma sky_stars (p:ℝ×AlleySpace): skyR (starsPart p)=p.2:= funext (fun i=>DoorCost.firstAt ..)
lemma combine_pose (p:Vantage): starsPart (clockR p, skyR p)=p:= by
 obtain ⟨q,rfl⟩:=starsPart.surjective p; rw [clock_stars,sky_stars]
abbrev birthClock (p:Vantage):ℝ≥0 := (p 3).toNNReal
lemma clockFare: Continuous birthClock:= continuous_real_toNNReal.comp (continuous_apply (3:Axis))
-- on height high enough these tests all work. Include every such density.
variable (U:Dose (DoorCost.Chamber 3)) (G:Dose ℝ)
def upperTest : SampleDose where
 val p:= G.val (p 3)* U.val (skyR p)
 smooth:= (G.smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun p:Vantage=>p 3))).mul (U.smooth.comp (contDiff_pi.mpr (fun i=>by unfold skyR; fun_prop)))
 budget:= exists_compact_iff_hasCompactSupport.mp ⟨starsPart '' (tsupport G.val ×ˢ tsupport U.val), (G.budget.prod U.budget).image (DoorCost.merge_cont ..), fun x e=> by
   apply Classical.byContradiction; intro z
   have ht:G.val (x 3)≠0∧ U.val (skyR x)≠0:= mul_ne_zero_iff.mp z
   exact e ⟨(x 3,skyR x),⟨subset_closure ht.1,subset_closure ht.2⟩, combine_pose x⟩⟩
lemma upper_width {r:ℝ}(h:tsupport G.val ⊆ Set.Ioi r) : ∀ i∈tsupport (upperTest U G).val,r< i 3:= by
  have he: tsupport (upperTest U G).val⊆ (fun i:Vantage=> i (3:Axis))⁻¹'tsupport G.val:= closure_minimal
    (fun i x=> subset_closure ((mul_ne_zero_iff.mp x).1)) ((G.budget.isClosed).preimage (continuous_apply _))
  exact fun i u=> h (he u)
lemma field_coord (x:ℝ×AlleySpace) : (upperTest U G).val (starsPart x)= G.val x.1 * U.val x.2:= by
 change G.val (clockR _)*_= _; rw [clock_stars]; change _*U.val (skyR _)=_; rw [sky_stars]
lemma upper_weight (p:U.Normalized)(g:G.Normalized): (upperTest U G).Normalized := by
 refine ⟨fun i=> mul_nonneg (g.1 (clockR i)) (p.1 (skyR i)),?_⟩
 rw [← (DoorCost.merge_cost (3:ℕ)).integral_comp' (upperTest U G).val]
 change (∫ p:ℝ× AlleySpace,(upperTest U G).val (starsPart p))=1
 simp_rw [field_coord U G]
 rw [Measure.volume_eq_prod, integral_prod_mul, p.2,g.2]; norm_num -- tune

-- relation of Clock-plane to spatial coord. radians on same Spine.
open Spectral Caino
open Spectral.Orbit.Prairie
open Boundary Boundary.Probe
open Score
open OS (Cross)
open OS.Semigroup.Balloon (tinct)
abbrev posse (p:Vantage):YM.Score.Clock:= transverse (3:Axis) (fun i=>p i.val)
@[fun_prop] lemma posse_cont : Continuous posse:=Continuous.subtype_mk (by
 apply (PiLp.continuous_toLp 2 _).comp
 apply continuous_pi; intro i; by_cases h:i=(3:Axis)
 · simp only [dif_pos h]; exact continuous_const
 simp only [dif_neg h]; exact continuous_apply i) _
-- verify overlap with Coord FLap
lemma from_plane (v:Vantage)(p:E4): Boundary.Probe.plane p (posse v).val=DoorCost.stars 3 (YM.spatial p).ofLp (skyR v):= by
 apply congrArg (fun r:ℝ=> Complex.exp ((r:ℂ)*Complex.I))
 let u:=posse v
 rw [Mink.pairing,show YM.time (posse v).val=0 from u.property,mul_zero,add_zero]; rw [PiLp.inner_apply]
 apply Finset.sum_congr rfl; intro i _
 have hv:YM.spatial u.val i=v (i.castSucc):= transverse_eyes 3 (fun y:Trans 3=> v y.val) ⟨i.castSucc,i.castSucc_lt_last.ne⟩
 change inner ℝ (YM.spatial p i) (YM.spatial u.val i)= _; rw [real_inner_comm,hv]; rfl

def heatWeight (t:ℝ≥0)(p:E4)(q:ℝ):ℝ:= G.val q*(tinct (3:Axis) q.toNNReal p-tinct 3 (q.toNNReal+t) p)
def spatialWeight (p:Space3):ℂ:= DoorCost.starbill 3 U.val p.ofLp
private lemma heatContour(p:E4)(w:ℝ): Continuous (fun v:ℝ≥0=> tinct (3:Axis) v p) := by unfold tinct; fun_prop
lemma heat_integrable (t:ℝ≥0)(p:E4) : Integrable (heatWeight G t p) := by
 have he := ((heatContour p 0).comp continuous_real_toNNReal).sub ((heatContour p 0).comp (continuous_real_toNNReal.add (continuous_const (y:=t))))
 exact (G.smooth.continuous.mul he |>.integrable_of_hasCompactSupport G.budget.mul_right)
lemma transform_gain (t:ℝ≥0)(p:E4) : (∫ z:Vantage,YM.Score.gain (upperTest U G).val posse birthClock t z p)= ↑(∫ z,heatWeight G t p z)*spatialWeight U (YM.spatial p) := by
 rw [← (DoorCost.merge_cost (3:ℕ)).integral_comp' (fun z=>YM.Score.gain (upperTest U G).val posse birthClock t z p)]
 let V:=starsPart; let f(q:AlleySpace):= U.val q*(DoorCost.stars 3 (YM.spatial p).ofLp q); let K(u:Vantage):= YM.Score.gain (upperTest U G).val posse birthClock t u p; let g(z:ℝ):ℂ:= ↑(heatWeight G t p z)
 have he(x:ℝ × AlleySpace): K (V x)=g x.1*f x.2:= by
   unfold K g f; unfold  YM.Score.gain Score.vote Score.lens; simp_rw [from_plane];
   rw [field_coord U G x, sky_stars]
   rw [show birthClock (V x)=x.1.toNNReal from congrArg Real.toNNReal (clock_stars x)]
   unfold heatWeight; push_cast; ring
 change (∫ p:ℝ× AlleySpace,K (V p))=_
 simp_rw [he]; rw [Measure.volume_eq_prod, integral_prod_mul, show g=fun z=>(heatWeight G t p z:ℂ) from rfl, integral_complex_ofReal]; rfl
lemma heatWeight_pos (g:G.Normalized)(t:ℝ≥0)(q:0<t)(p:E4)(v:0< YM.time p): 0<∫ z,heatWeight G t p z:= by
 have hp (z:ℝ): tinct (3:Axis) (z.toNNReal+t) p < tinct (3:Axis) z.toNNReal p:= by
   unfold tinct; apply Real.exp_lt_exp.mpr; simp only [NNReal.coe_add]; apply neg_lt_neg; exact mul_lt_mul_of_pos_right (lt_add_of_pos_right _ q) v
 apply (integral_pos_iff_support_of_nonneg (f:=heatWeight G t p) (fun i=> mul_nonneg (g.1 i) (sub_nonneg.mpr (hp i).le)) (heat_integrable G t p)).2
 have ht:0<volume (Function.support G.val) := (integral_pos_iff_support_of_nonneg g.1 (G.smooth.continuous.integrable_of_hasCompactSupport (μ:=volume) G.budget)).1 (by rw [g.2]; exact zero_lt_one)
 exact lt_of_lt_of_le ht (measure_mono (fun i x=> mul_ne_zero x (sub_ne_zero.mpr (hp i).ne')))
lemma spatialWeight_paid (q:U.Normalized):∀ᵐ w:Space3,spatialWeight U w≠0:= by
 let f: AlleySpace→Space3:= WithLp.toLp 2
 have he: MeasurePreserving f := PiLp.volume_preserving_toLp (Fin 3)
 have hx: Continuous (spatialWeight U):= (DoorCost.sums_slip 3 U.val U.smooth.continuous U.budget).comp (PiLp.continuous_ofLp ..)
 rw [←he.map_eq]; exact (ae_map_iff he.measurable.aemeasurable ((isOpen_ne (x:=(0:ℂ))).preimage hx|>.measurableSet)).2 (DoorCost.starbill_live 3 U.val U.smooth.continuous U.budget q.2) -- norm
local notation "τ"=> terrain tracks3
variable {P:Spine}{x:P.Spectrum0 3} (T:Summit x)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "μ"=> (S).ℚmeasure.diagonal
local notation "π'"=> (S).ℚmeasure.region
local notation "D"=> notice 3 x tracks3
-- log scope bug! avoid notation in variable header. e.g. `a:P.ManyF ...`
include T
lemma billsPaid (W:Set E4)(hW:MeasurableSet W)(b:Fin 3→Bool)
   (p:W⊆ terrain tracks3 ⁻¹' (alley b))(x':P.ManyF 3 (P.otherSpectrum 3 3 x))(u:U.Normalized):
   ∀ᵐ v∂ μ (π' W x'), spatialWeight U (terrain tracks3 v)≠0:= by
 let y: H:= π' W x'; let X:= alley b; let L:=(μ y); let K:=terrain tracks3; let Y:=(D).diagonal y
 have hv:IsOpen X:=alley_open b
 have he: ∀ᵐ v∂L,K v∈ X:= by
   have hl:L=(μ x').restrict W:= bill_in_zone H (S).ℚmeasure hW x'
   rw [hl]; exact (ae_restrict_mem hW).mono (fun v e=> p e)
 have hs:Continuous K:= terrain_cont tracks3
 have ht:Y=L.map K:=rfl
 have hf: ∀ᵐ p∂Y,p∈ X:= by rw [ht]; exact (ae_map_iff hs.aemeasurable hv.measurableSet).2 he
 have hp: ∀ᵐ v∂Y.restrict X, spatialWeight U v≠0:= (T.footprint (Fin 3) tracks3 (3:Axis) axleS b y).ae_le (MeasureTheory.ae_restrict_le (spatialWeight_paid U u)) -- `MeasureTheory` namespace?
 rw [Measure.restrict_eq_self_of_ae_mem hf,ht] at hp
 exact ae_of_ae_map hs.aemeasurable hp -- tune
lemma gain_live (W:Set E4)(hW:MeasurableSet W)(v: W⊆ Mink.inside)(b:Fin 3→Bool)
   (p:W⊆ terrain tracks3 ⁻¹' alley b)(t:ℝ≥0)(h:0<t)(y:P.ManyF 3 (P.otherSpectrum 3 3 x)) (u:U.Normalized)(g:G.Normalized) :
   ∀ᵐ q∂μ (π' W y), (∫ z:Vantage,YM.Score.gain (upperTest U G).val posse birthClock t z q) ≠ 0:= by
 let x':= π' W y; have he:∀ᵐ q∂ μ x', q∈W:= by rw [show μ x'=(μ y).restrict W from bill_in_zone H (S).ℚmeasure hW y]; exact ae_restrict_mem hW
 filter_upwards [he,billsPaid U T W hW b p y u] with q e t'
 rw [transform_gain]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (heatWeight_pos G g t h q ((Mink.strict_self _).1 (v e)).1).ne') t'
omit T
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
