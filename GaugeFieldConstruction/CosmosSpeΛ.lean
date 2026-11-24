import GaugeFieldConstruction.BrambleEarthL

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)

-- Any axis true cone for the STRICT ordering claim all Villas.After rotation can use spectrum calibration Sχ already earned. Confirm analytic measure rotation.REAL plates.
variable (K:SunlitL Cw R G)(uF:SurfCheckL.boisterL t G){g:SO}{b:Axis}(e:suitAxL g a b)
variable (L:E4) (χ:P.Spectrum0 3)
-- analytic abstraction LIGHT labels kept
-- using h: E determination same heat continuation
section dset
variable {X Y:Hilbert}(u:X)(v':X)(p':Y)(q':Y)(U:NSF.OS.Semigroup X a)(V:NSF.OS.Semigroup Y b)

lemma moteSpeΛ (h:∀ d:ℝ≥0, inner ℂ u (U.E d v')= inner ℂ p' (V.E d q')) (t:ℝ): inner ℂ u (U.edge t v')=inner ℂ p' (V.edge t q'):=by
 let S:ℂ→ℂ:= (innerSL ℂ u) ∘ (ContinuousLinearMap.apply ℂ X.space v') ∘ U.F
 let F:ℂ→ℂ:= (innerSL ℂ p') ∘ (ContinuousLinearMap.apply ℂ Y.space q') ∘ V.F
 have He(q:ℝ≥0)(hq:0<q): S (duration q)= F (duration q):= by change inner ℂ _ (U.F _ _) = inner ℂ _ (V.F _ _); rw[U.roots_heat hq,V.roots_heat hq]; exact h q
 have Hw: Set.EqOn (fun w:ℂ=> S w-F w) 0 NSF.OS.Semigroup.inside:=by
    have Hl(z)(hz:z∈ NSF.OS.Semigroup.inside): AnalyticAt ℂ (fun z=>S z-F z) z:= (((innerSL ℂ u).analyticAt _).comp (((ContinuousLinearMap.apply ℂ X.space v').analyticAt _).comp (U.localHeat z hz))).sub (((innerSL ℂ p').analyticAt _).comp (((ContinuousLinearMap.apply ℂ Y.space q').analyticAt _).comp (V.localHeat z hz)))
    apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (show AnalyticOnNhd ℂ _ _ from Hl) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (dur.mpr (zero_lt_one : 0 < (1:ℝ≥0)))
    intro hn
    have hy:Tendsto duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] duration 1):=by
       apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
       · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
       filter_upwards [self_mem_nhdsWithin] with i hi; have hI := Set.mem_Ioi.mp hi; change ¬duration i=duration 1; exact fun e=>hI.ne' (Subtype.ext (Complex.ofReal_injective e))
    obtain ⟨i,w,u⟩:= ((hy.eventually hn).and self_mem_nhdsWithin).exists
    exact w (sub_eq_zero.mpr (He i (lt_trans (zero_lt_one) (Set.mem_Ioi.mp u))))
 have Hi(q:ℝ≥0)(x:0<q): inner ℂ u (U.edge t (U.E q v'))= inner ℂ p' (V.edge t (V.E q q')):=by
    rw [← U.roots_heat x, ← V.roots_heat x,← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, U.along (dur.mpr x),V.along (dur.mpr x)]; exact sub_eq_zero.mp (Hw (NSF.OS.Semigroup.length.mpr x))
 let Y :Filter ℝ≥0:= 𝓝[>] (0:ℝ≥0)
 haveI : Y.NeBot:= by unfold Y; infer_instance
 have hm : Filter.EventuallyEq Y (fun q=> inner ℂ u (U.edge t (U.E q v'))) (fun q=>inner ℂ p' (V.edge t (V.E q q'))):= by filter_upwards [self_mem_nhdsWithin]; intro q p; exact Hi _ p
 let Z:= (innerSL ℂ u).continuous.comp ((U.edge t).continuous.comp (U.continuousE v'))
 let W:= (innerSL ℂ p').continuous.comp ((V.edge t).continuous.comp (V.continuousE q'))
 have hu:= tendsto_nhds_unique_of_eventuallyEq ((Z.tendsto 0).mono_left (show Y≤ _ from nhdsWithin_le_nhds)) ((W.tendsto 0).mono_left nhdsWithin_le_nhds) hm
 change inner ℂ _ (U.edge t (U.E 0 _))= inner ℂ _ (V.edge t (V.E 0 _)) at hu
 rw[U.eZero,V.eZero] at hu; exact hu
end dset

variable (s:StallLeadMars b (motionMoonMars g p) P)
local notation "Π" j => LightLiftL (Cw j)
local notation "φX"=> RiverBoreL Cw R a F p J
local notation "φY"=> RiverBoreL Cw R b (compassPiMars t g ∘ F) (motionMoonMars g p) s
include K uF
lemma polarSpeΛ (z:OS.Cross a)(w:ℝ) : inner ℂ φX ((LightLiftL (Cw a)).edge w ((Π a).U z φX))= inner ℂ φY ((LightLiftL (Cw b)).edge w ((Π b).U (PlissCL e z) φY)):=by
 apply moteSpeΛ; intro m; rw[show (Π a).U z=(Cw a).BrightHab.U z from rfl,show (Π b).U (PlissCL e z)=(Cw b).BrightHab.U (PlissCL e z) from rfl,ReefRealL Cw R K.toCheckΩL F F a, ReefRealL Cw R K.toCheckΩL _ _ b, OroLineL Cw R G t K uF J (ReefShedsL p J m z) e F F,DistantL e] -- defeq helper
omit K uF in
private lemma PlissSpeΛ (h:E4): PlissCL e (SEP a h)= SEP b (g.val.motion h):=by
 apply Subtype.ext; change g.val.motion (h- _ • _) = g.val.motion h -_ • _; rw[map_sub, LinearIsometryEquiv.map_smul, suitsPoleL e,e]
open MeasureTheory Measure
local notation "ΡcX"=> (Π a).ℚmeasure
local notation "ΡcY"=> (Π b).ℚmeasure
local notation "ΜΧ"=> (ΡcX).diagonal φX
local notation "ΜΥ"=> (ΡcY).diagonal φY
include e
lemma WagesTiltSpeΛ : ΜΥ= Measure.map (g.val.motion) ΜΧ :=by
 haveI: IsFiniteMeasure ΜΧ := (ΡcX).finite _
 haveI: IsFiniteMeasure ΜΥ := (ΡcY).finite _
 apply Measure.ext_of_charFun; ext1 v; obtain ⟨p',rfl⟩:= g.val.motion.surjective v
 have hm: charFun ΜΥ (g.val.motion p')= charFun ΜΧ p':=by
    rw [(Π b).joint,(Π a).joint]; change inner ℂ _ ((Π b).edge _ ((Π b).U (SEP b (g.val.motion p')) _))= inner ℂ _ ((Π a).edge _ ((Π a).U (SEP a p') _)); rw [e p',← PlissSpeΛ a e]; exact (polarSpeΛ Cw R G t a p F J K uF e s (SEP a p') (p' a)).symm
 rw [hm,charFun_apply,charFun_apply, integral_map g.val.motion.continuous.measurable.aemeasurable]; swap
 · exact (show Continuous (fun y:E4=>Complex.exp ((↑(inner ℝ y (g.val.motion p')):ℂ)*Complex.I)) from by fun_prop).aestronglyMeasurable
 simp_rw [LinearIsometryEquiv.inner_map_map]
-- define physical forward cone with perpendicular E4 norm explicit, no rotations in statement
abbrev SkyRootsSpeΛ(a:Axis):Set E4:={w | ‖(SEP a) w‖ ≤ w a}
omit K uF e in
lemma closedSpeΛ (b:Axis): IsClosed (SkyRootsSpeΛ b) := isClosed_le (continuous_norm.comp (SEP b).continuous) (show Continuous (fun w:E4=> w b) from by fun_prop) -- tune
omit K uF in
lemma SkyPlacSpeΛ : SkyRootsSpeΛ a=g.val.motion ⁻¹' SkyRootsSpeΛ b:=by
 ext1 x; change ‖_‖ ≤ _ ↔ ‖SEP b (g.val.motion x)‖ ≤ _; rw [e x, ← PlissSpeΛ a e]; change _ ↔ ‖g.val.motion (SEP a x).val‖ ≤ _
 rw [g.val.motion.norm_map]; rfl
include K uF e J s
lemma pShiftSpeΛ: (ΡcX).region (SkyRootsSpeΛ a)ᶜ φX=0 ↔ (ΡcY).region (SkyRootsSpeΛ b)ᶜ φY=0:=by
 rw [← (ΡcX).null_pair (closedSpeΛ a).isOpen_compl.measurableSet,← (ΡcY).null_pair (closedSpeΛ b).isOpen_compl.measurableSet, WagesTiltSpeΛ Cw R G t a p F J K uF e s, Measure.map_apply g.val.motion.continuous.measurable (closedSpeΛ b).isOpen_compl.measurableSet, SkyPlacSpeΛ a e]; rfl
#print axioms pShiftSpeΛ
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
