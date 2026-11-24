import GaugeFieldConstruction.SparkDewL
import GaugeFieldConstruction.EuniceS
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
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
open Set Complex
variable (J0: SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (E:∀ᵐ x∂P.pillars 3,P.lodestar 3 x) (Z:∀ᵐ x∂P.pillars 3, CriteriaL (P.privateH x) R)
open PlaneL
-- robust continuity through *all* Conf, no overlap only, default defined everywhere
noncomputable def pickΘL {n:ℕ}(p:Points n)(h:p∈ conf n):= (denseQuiverL timeAxis p h).choose
lemma pickθL (p:Points n)(h:p∈conf n): motionMoonMars (pickΘL p h) p∈blueL n:= westBlueL _ (denseQuiverL _ p h).choose_spec
noncomputable def GlobeLightL : CloudsL:=fun n x=> if h:x∈conf n then let s:=pickΘL x h; (AtlasCoralL Cw R U _ (motionMoonMars s x) (pickθL x h)).compLinearMap (fun _=> compassPiMars t s) else 0
noncomputable abbrev tessL {n:ℕ}(F:Fin n→ΧiMars)(x:Points n):= GlobeLightL Cw R t U n x F
abbrev PurePC_L :Prop:=∀ s:SO,PureCovL Cw R t s
include U
lemma TessPickL (p:Points n)(h:p∈conf n): let s:=pickΘL p h; tessL Cw R t U F p= CoralL Cw R (compassPiMars t s ∘ F) (motionMoonMars s p):=by dsimp only; rw[tessL,GlobeLightL,dif_pos h]; rfl
variable (W:PurePC_L Cw R t)
include W
lemma TessAuraL (s:SO) (p:Points n)(h:p∈conf n)(v:motionMoonMars s p∈blueL n): tessL Cw R t U F p= CoralL Cw R (compassPiMars t s ∘ F) (motionMoonMars s p):=by
 let a:= pickΘL p h; let x:= motionMoonMars a p; let z:= compassPiMars t a ∘ F
 let T':=s*a⁻¹; have e:motionMoonMars T' x∈blueL n:=by unfold x; rw[←WindyMissionMars, show T'*a=s by unfold T'; group]; exact v
 have he:=W T' _ x z (show x∈ feasibleL T' _ from ⟨pickθL p h,e⟩); rw[show compassPiMars t T' ∘ z=compassPiMars t s ∘ F from ?_,show motionMoonMars T' x= motionMoonMars s p from (by unfold x; rw[←WindyMissionMars,show T'*a=s from by unfold T'; group])] at he
 · rw[TessPickL Cw R t F U p h]; exact he.symm
 ext1 i; dsimp only [Function.comp_apply,z]; rw[←sailMulMars,show T'*a=s from by unfold T'; group]
omit W U
lemma blueConfL (x:Points n)(t:x∈blueL n): x∈ conf n:=by obtain ⟨a,h⟩:= Set.mem_iUnion.mp (show ΦplanR n x∈CardsR _ from t); exact fun i j q=> h (congrArg (fun z:E4=>z a) q)
include W U
lemma TessBlueL (p:Points n)(v:p∈blueL n): tessL Cw R t U F p=CoralL Cw R F p:=by
 have hm:motionMoonMars 1 p=p:= calend_oneMars p
 rw[TessAuraL Cw R t F U W 1 p (blueConfL p v) (hm.symm ▸ v),hm,show compassPiMars t 1 ∘ F=F from funext fun i=> sailOneMars t _]
lemma TessCovL (s:SO)(p:Points n)(h:p∈conf n): tessL Cw R t U (compassPiMars t s ∘ F) (motionMoonMars s p)=tessL Cw R t U F p:=by
 let a:= pickΘL (motionMoonMars s p) (NSF.Points.move_in _ h); have v:motionMoonMars (a*s) p∈blueL n:= by rw [WindyMissionMars]; exact pickθL _ _
 rw [TessPickL Cw R t _ U _ (NSF.Points.move_in _ h), TessAuraL Cw R t F U W (a*s) p h v,WindyMissionMars,show compassPiMars t (a*s) ∘ F=compassPiMars t a ∘ (compassPiMars t s ∘ F) from funext fun i=> sailMulMars t _ _ _]
lemma TessLightL (v:p∈conf n): ContinuousAt (tessL Cw R t U F) p:=by
 let g:=pickΘL p v; let A:= motionMoonMars (n:=n) g
 let H:= CoralL Cw R (compassPiMars t g ∘ F)
 have hp:= (BlueAtL Cw R (A p) (compassPiMars t g ∘ F) U (pickθL p v)).tendsto.comp ((motionθL g).tendsto p)
 apply (show ContinuousAt (H ∘ A) p from hp).congr
 filter_upwards [(conf_open n).eventually_mem v, (motionθL (n:=n) g).continuousAt.tendsto.eventually ((clearL n).mem_nhds (pickθL p v))] with x v h; exact (TessAuraL Cw R t F U W g x v h).symm
-- charge and translation extend via density without proving individual label transports on scalar. Cleaner.
omit W U
lemma WorldUniteL (f g:Points n→ℂ)(p:Points n)(h:p∈conf n)(u:ContinuousAt f p)(v:ContinuousAt g p)(t: EqOn f g (blueL n)): f p=g p:=by haveI:= mem_closure_iff_nhdsWithin_neBot.mp (lensBlueL _ p); exact tendsto_nhds_unique_of_eventuallyEq (u.continuousWithinAt (s:=blueL n)) (v.continuousWithinAt) (t.eventuallyEq_of_mem self_mem_nhdsWithin)
lemma AcrossSkyL (p:Points n)(s:E4)(e:p∈blueL n): NSF.Points.across s p ∈ blueL n:=by obtain ⟨i,b⟩:= Set.mem_iUnion.mp (show ΦplanR n p∈CardsR _ from e); exact westBlueL i ((basicWestL p i s).mpr b)
lemma PermSkyL (p:Points n)(s:Equiv.Perm (Fin n))(e:p∈blueL n):NSF.Points.rearrange s p∈ blueL n:=by obtain ⟨i,b⟩:= Set.mem_iUnion.mp (show ΦplanR n p∈CardsR _ from e); exact westBlueL i (constWestL p s i b)
lemma CalendarUL (a:Axis)(n:ℕ): Continuous (MirrorPoseL a (n:=n)):=by
 let u:=Signed.reflect a; let h(y:Points n)(i:Fin n):= u.motion (y i); exact (PiLp.continuous_toLp 2 _).comp (show Continuous h from continuous_pi (fun k=> u.motion.continuous.comp (show Continuous (fun y:Points n=> y k) by fun_prop)))
lemma calendarSureL (s:E4)(n:ℕ): Continuous (NSF.Points.across (n:=n) s):=by
 let h(y:Points n)(i:Fin n):= y i+s; exact (PiLp.continuous_toLp 2 _).comp (show Continuous h from continuous_pi (fun i=> Continuous.add (show Continuous (fun y:Points n=> y i) by fun_prop) continuous_const))
lemma RearSureL (s:Equiv.Perm (Fin n)):Continuous (NSF.Points.rearrange s):=by
 let h(y:Points n)(i:Fin n):= y (s i); exact (PiLp.continuous_toLp 2 _).comp (show Continuous h from continuous_pi fun i=> show Continuous (fun y:Points n=> y (s i)) by fun_prop)
include W U
lemma WorldLaceL (h:p∈conf n)(s: E4): tessL Cw R t U F (NSF.Points.across s p)=tessL Cw R t U F p:=by
 exact WorldUniteL (tessL Cw R t U F ∘ NSF.Points.across s) _ p h ((TessLightL Cw R t _ F U W (NSF.Points.across_in s h)).tendsto.comp ((calendarSureL s n).tendsto p)) (TessLightL Cw R t _ F U W h) (fun z hp=>by unfold Function.comp; rw[TessBlueL Cw R t F U W _ (AcrossSkyL z s hp),TessBlueL Cw R t F U W _ hp]; exact CoralAcrossL Cw R z F U hp s)
lemma WorldMixL(h:p∈conf n)(s:Equiv.Perm (Fin n)): tessL Cw R t U (F ∘ s) (NSF.Points.rearrange s p)=tessL Cw R t U F p:=by
 apply WorldUniteL (_ ∘ NSF.Points.rearrange s) _ p h ((TessLightL Cw R t _ (F ∘ s) U W (NSF.Points.rearrange_in s h)).tendsto.comp ((RearSureL s).tendsto p)) (TessLightL Cw R t _ F U W h)
 intro z p; simp only [Function.comp_apply]; rw [TessBlueL Cw R t _ U W _ (PermSkyL z s p), TessBlueL Cw R t _ U W _ p]; exact CoralCardsL Cw R F U s z p -- tune apply defeq
lemma WorldNightL(h:p∈conf n): tessL Cw R t U (TurnupMars a ∘ F) (MirrorPoseL a p)= Star.star (tessL Cw R t U F p):=by
 let z:=Star.star ∘ tessL Cw R t U F
 refine WorldUniteL (tessL Cw R t U (TurnupMars a ∘ F) ∘ MirrorPoseL a) z p h ((TessLightL Cw R t _ _ U W (NSF.Points.move_in (Signed.reflect a) h)).tendsto.comp ((CalendarUL a n).tendsto p)) ((TessLightL Cw R t _ F U W h).star) ?_
 intro v h; unfold z; simp only [Function.comp_apply]; rw [TessBlueL Cw R t _ U W _ (miresL a v h),TessBlueL Cw R t _ U W _ h]; exact PearlMirL Cw R a v F U h
lemma WorldCoinL (F: Fin n→ΧiMars)(hX:EqOn (tessL Cw R t U (Fathom.add (Empire.one four) F)) ((tessL Cw R t U F) ∘ YM.Points.tail) (blueL (n+1))): EqOn (tessL Cw R t U (Fathom.add (Empire.one four) F)) ((tessL Cw R t U F) ∘ YM.Points.tail) (conf (n+1)):= by
 have hp:Continuous (YM.Points.tail (n:=n)):=by
    let h(y:Points (n+1))(i:Fin n):= y i.succ; exact (PiLp.continuous_toLp 2 _).comp (show Continuous h from continuous_pi fun i=> show Continuous (fun y:Points (n+1)=> y i.succ) by fun_prop)
 exact fun x p=> WorldUniteL _ _ x p (TessLightL Cw R t _ _ U W p) ((TessLightL Cw R t _ F U W (NSF.Points.tail_in p)).tendsto.comp (hp.tendsto x)) hX -- tune ns names
omit W
lemma TessCarbonL (v:p∈conf n) : StronglyMeasurable (fun x:P.Spectrum0 3=> tessL (P.privateH x) R t U F p):=by
 simp_rw [show ∀ x:P.Spectrum0 3,tessL (P.privateH x) R t U F p=_ from fun x=> TessPickL (P.privateH x) R t F U p v]; exact (BronteR _ (fun i=> U.showL _) _).1 -- tune
include f J0
lemma meanVinesL (v:p∈conf n): G n p F= ∫ x,tessL (P.privateH x) R t U F p∂P.pillars 3:=by
 let s:=pickΘL p v; let y:= motionMoonMars s p; let F':= compassPiMars t s ∘ F
 rw [← f n F p v s,J0.invoice n F' y (pickθL p v)]; simp_rw [show ∀ x:P.Spectrum0 3,tessL (P.privateH x) R t U F p= CoralL (P.privateH x) R F' y from fun x=> TessPickL (P.privateH x) R t F U p v]; exact (BronteR _ (fun i=>U.showL _) _).2
#print axioms meanVinesL
#print axioms WorldMixL
#print axioms WorldNightL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
