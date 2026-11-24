import GaugeFieldConstruction.OrchardFastYL
import GaugeFieldConstruction.ReactorTagsYL
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
variable {m:ℕ}
-- project translated distant spectator onto POS adapted axes. first cluster shift c; second e, total c; leftover space goes also to infinity and need no decay there.
abbrev plazaYL (s:SO)(c:E4)(x:Points n):= NSF.Points.across c (motionMoonMars s x)
abbrev pitaYL (a:Axis)(s:SO)(c:E4)(x:Points n):= MirrorPoseL a (plazaYL s c x)
noncomputable abbrev zodiacYL (s:SO)(c e:E4)(i:ℕ):= s.val.motion (EarYL i) + c -e
noncomputable abbrev SailHYL (s:SO)(c e:E4)(a:Axis)(i:ℕ):ℝ≥0:= (zodiacYL s c e i a).toNNReal
noncomputable abbrev SailUYL (s:SO)(c e:E4)(a:Axis)(i:ℕ):OS.Cross a:=NSF.OS.Semigroup.SEP a (zodiacYL s c e i)
noncomputable abbrev FlyWYL (s:SO)(a:Axis)(F:Fin n→ΧiMars): Fin n→ΧiMars:=TurnupMars a ∘ (compassPiMars t s ∘ F)
variable (s:SO)(c e:E4)
lemma pitaPrimeYL (h:motionMoonMars s p∈westL n a):∃ c:E4,Nonempty (StallLeadMars a (pitaYL a s c p) P):=by
 have he:= mirWideL a _ a h
 obtain ⟨q,v⟩:=spikeWestL (P:=P) a _ he
 let V:=(Signed.reflect a).motion
 obtain ⟨c,e⟩:= V.surjective q
 refine ⟨c,?_⟩; unfold pitaYL plazaYL; rw [MirTravelsL,show (Signed.reflect a).motion c=q from e]; exact v
lemma accelsYL (h: 0<s.val.motion (basis timeAxis) a) : Tendsto (fun i:ℕ=>zodiacYL s c e i a) atTop atTop:=by
 have he:Tendsto (fun i:ℕ=>(i:ℝ)*s.val.motion (basis timeAxis) a) atTop atTop:= tendsto_natCast_atTop_atTop.atTop_mul_const h
 refine tendsto_atTop.mpr fun b=>?_ ; filter_upwards [he.eventually (eventually_ge_atTop (b+e a-c a))] with i k
 unfold zodiacYL EarYL; rw [LinearIsometryEquiv.map_smul]; change b≤ (i:ℝ)* s.val.motion (basis timeAxis) a+c a-e a; linarith
lemma uppersYL (h: 0<s.val.motion (basis timeAxis) a) : Tendsto (SailHYL s c e a) atTop atTop:=by
 have he:= accelsYL a s c e h
 refine tendsto_atTop.mpr fun b=>?_ ; filter_upwards [he.eventually (eventually_ge_atTop (b:ℝ))] with i k; change (b:ℝ)≤ ((SailHYL s c e a i):ℝ); rw [SailHYL,Real.coe_toNNReal _ (b.coe_nonneg.trans k)]; exact k -- tune rw signature
lemma ShipTimeYL (i:ℕ)(h:0≤zodiacYL s c e i a):ReefOutL (SailHYL s c e a i) (SailUYL s c e a i)=zodiacYL s c e i:=by unfold ReefOutL; rw [SailHYL,Real.coe_toNNReal _ h]; change _ • basis _+(_ - _ • basis _)=_; abel
lemma Turn2YL: Signed.mirror a * Signed.mirror a=1:=by nth_rw 1 [←Signed.mirror_inv a]; exact inv_mul_cancel _
lemma Turn2AxYL (x:ΧiMars): TurnupMars a (TurnupMars a x)=x:=by unfold TurnupMars; rw [Calibration.comp_s,Calibration.clear,←Module.End.mul_apply,←map_mul,Turn2YL,map_one]; rfl
lemma Turn2PoseYL (x:E4): (Signed.reflect a).motion ((Signed.reflect a).motion x)=x:=by change Ortho.move _ (Ortho.move _ _)=_; rw [←Ortho.move_mul]; change Ortho.move (Signed.inclusionO _* Signed.inclusionO _) _=_; rw[←map_mul,Turn2YL,map_one]; exact Ortho.move_one _
lemma GustSailYL (p:Points n)(y:Points m)(i:ℕ)(h:0≤zodiacYL s c e i a): closedUp a (pitaYL a s c p) (ReefMapL (SailHYL s c e a i) (SailUYL s c e a i) (plazaYL s e y))= plazaYL s c (apartYL (EarYL i) p y) :=by
 ext1 j; refine Fin.addCases ?_ ?_ j
 · intro j; rw [NSF.Table.Pairing.enter]; change (Signed.reflect a).motion ((Signed.reflect a).motion _) = s.val.motion (gluedYL _ _ _)+c; rw [Turn2PoseYL, brightLYL]; rfl
 intro j; rw[NSF.Table.Pairing.leave]; change _+ReefOutL _ _=s.val.motion (gluedYL _ _ _) + c; rw [brightRYL, ShipTimeYL a s c e _ h]; change s.val.motion (y j)+e+ (s.val.motion _+c-e)=s.val.motion (y j+ _)+c; rw[map_add]; abel
lemma CompassJoinYL (S:Fin m→ΧiMars): compassPiMars t s ∘ (Fin.append F S)=Fin.append (TurnupMars a∘ FlyWYL t s a F) (compassPiMars t s ∘ S):=by ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [FlyWYL,Turn2AxYL]
lemma fromPlazaYL (x:Points n)(e:plazaYL s c x∈conf n):x∈conf n:=fun i j h=>e (by change s.val.motion _ + c=s.val.motion _ +c; rw[h])
-- Exact equality to real chronological price for distant cluster on any Good χ
include U
variable (x:Points n)(y:Points m)(V: Fin m→ ΧiMars)(T:StallLeadMars a (pitaYL a s c x) P)(B:StallLeadMars a (plazaYL s e y) P)
include T B
lemma ComposedYL (W:PurePC_L (P.privateH χ) R t)(i:ℕ)(h:0≤zodiacYL s c e i a): tessL (P.privateH χ) R t U (Fin.append F V) (apartYL (EarYL i) x y)= BerryEarthL R a (SailHYL s c e a i) (SailUYL s c e a i) (FlyWYL t s a F) (compassPiMars t s∘ V) (pitaYL a s c x) (plazaYL s e y) χ :=by
 let κ:= P.privateH χ; let A:=apartYL (EarYL i) x y; let p':=Fin.append F V; let T':= compassPiMars t s ∘ p'
 have he:plazaYL s c A∈blueL (n+m):=by unfold A; rw [←GustSailYL a s c e _ _ i h]; exact westBlueL _ (WrapL T (ReefShedsL _ B _ _))
 have hp:=fromPlazaYL s c A (blueConfL _ he)
 rw [← TessCovL κ R t p' U W s A hp,← WorldLaceL κ R t _ T' U W (NSF.Points.move_in _ hp) c,TessBlueL κ R t T' U W _ he]; change CoralL _ _ ( _ ∘ (Fin.append F V)) (plazaYL s c (apartYL _ _ _))=_; rw [CompassJoinYL t a F s V,← GustSailYL a s c e x y i h]; rfl -- order tune
lemma LightExitYL(W:PurePC_L (P.privateH χ) R t)(u:0<s.val.motion (basis timeAxis) a)(Z:CriteriaL (P.privateH χ) R)(E:P.lodestar 3 χ)(h:x∈conf n)(v:y∈conf m): Tendsto (fun i:ℕ=>tessL (P.privateH χ) R t U (Fin.append F V) (apartYL (EarYL i) x y)) atTop (𝓝 (tessL (P.privateH χ) R t U F x*tessL (P.privateH χ) R t U V y)):=by
 let κ:= P.privateH χ; let T':=FlyWYL t s a F; let L:=compassPiMars t s ∘ F; let p':=pitaYL a s c x; let q:=plazaYL s e y; let P':=compassPiMars t s ∘ V
 have hu:=SanctuaryYL R a χ U Z E T' P' p' q T B (SailUYL s c e a) (SailHYL s c e a) (uppersYL a s c e u)
 have ht:pearlL R χ T' p'= Star.star (tessL κ R t U F x):=by
   change CoralL _ _ _ _= _; rw[←TessBlueL κ R t T' U W p' (westBlueL _ (StallWestYL a _ T)),show tessL κ R t U T' p'= Star.star _ from WorldNightL κ R t a (plazaYL s c x) L U W (NSF.Points.across_in _ (NSF.Points.move_in _ h)), show tessL κ R t U L (plazaYL s c x)=_ from (WorldLaceL κ R t _ L U W (NSF.Points.move_in _ h) c).trans (TessCovL κ R t F U W _ _ h)]
 rw [ht,star_star,show pearlL R χ P' q= tessL κ R t U V y from (((TessBlueL κ R t P' U W q (westBlueL _ (StallWestYL a _ B))).symm.trans (WorldLaceL κ R t _ P' U W (NSF.Points.move_in _ v) e)).trans (TessCovL κ R t V U W _ _ v))] at hu
 refine hu.congr' ?_; filter_upwards [(accelsYL a s c e u).eventually (eventually_ge_atTop 0)] with i he using (ComposedYL R t a F χ U s c e x y V T B W i he).symm -- tune
omit T B
lemma HighFactorYL (W:PurePC_L (P.privateH χ) R t)(Z:CriteriaL (P.privateH χ) R)(E:P.lodestar 3 χ)(h:x∈conf n)(v:y∈conf m): Tendsto (fun i:ℕ=>tessL (P.privateH χ) R t U (Fin.append F V) (apartYL (EarYL i) x y)) atTop (𝓝 (tessL (P.privateH χ) R t U F x*tessL (P.privateH χ) R t U V y)):=by
 obtain ⟨s,H,I,u⟩:=OasisYL timeAxis x y h v; obtain ⟨c,⟨T⟩⟩:=pitaPrimeYL (P:=P) timeAxis x s H; obtain ⟨e,⟨B⟩⟩:= spikeWestL (P:=P) timeAxis _ I; exact LightExitYL R t _ F χ U s c e x y V T B W u Z E h v
#print axioms HighFactorYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
