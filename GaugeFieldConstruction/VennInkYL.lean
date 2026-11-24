import GaugeFieldConstruction.KilmerStageYL
import GaugeFieldConstruction.NeronYL
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
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Fathom Points Bulb
variable {m:ℕ}(y:Points m)(V: Fin m→ΧiMars)(k: Fin n)(b:Fathom.Bulb)(r:ℝ)
-- signals
noncomputable abbrev MeterA_YL (b:Fathom.Bulb)(i:Axis)(p:Points n)(F:Fin (n+1)→ΧiMars): ChartOpYL:= fun C=> raysCostYL b i (C _ F) p
noncomputable abbrev SoundQYL (a:Axis)(p:Points n)(k:Fin n)(b:Fathom.Bulb)(i:Axis)(r:ℝ)(F:Fin (n+1)→ ΧiMars):ChartOpYL:= fun C=> ScrollOpYL a p b i k r (C _ F)
noncomputable abbrev TopNoteYL (k:Fin n)(b:Fathom.Bulb)(a:Axis)(p:Points n)(F:Fin n→ΧiMars)(r:ℝ):ChartOpYL:= fun C=> C _ F (ledgeYL k a r p 1)- (C n F p + r • ∑ i:Axis, SoundQYL a p k b i r (Fin.cons (TotalStarsMars t i a) F) C)
noncomputable abbrev AnthemYL (k:Fin n)(b:Fathom.Bulb)(a:Axis)(p:Points n)(F:Fin n→ΧiMars):ChartOpYL:=fun C=>∑ j:Axis,∑ i:Axis, MeterA_YL b i p (Fin.cons (TotalStarsMars t i j) (Function.update F k (TotalStarsMars t j a))) C
variable (U2:∀ n (F: Fin n→ ΧiMars),ContinuousOn (fun p=>G n p F) (conf n))
include J0 U E Z f U2
lemma asAtlasPYL (i:Axis)(T:Fin (n+1)→ΧiMars)(h:BreatherMars b k p):AtlasYL R G t U (MeterA_YL b i p T):=by
 haveI := vestFinYL i b; haveI:CompactSpace (VestHYL b i):= isCompact_iff_compactSpace.mp (vestKYL i b)
 let A(v:VestHYL b i):= YM.Points.cons v.val p; let W(v:VestHYL b i):= DimYL b i v.val
 rw[show MeterA_YL b i p T= AtlasOpYL T (landRentYL _) A W from funext fun C=> raysVisitYL i p b _]; exact CharterAtlasYL R G t T U J0 f E Z (landRentYL _) A W ((beamInkYL i b).comp continuous_subtype_val) (alabasterYL.comp (continuous_subtype_val.prodMk continuous_const)) (fun v=> RoomMars _ _ _ h _ (Bulb.cone b i v.2)) U2
lemma asAtlasQYL (i:Axis)(T:Fin (n+1)→ ΧiMars)(h:calmYL k a r p b):AtlasYL R G t U (SoundQYL a p k b i r T):=by
 haveI:= RΦayComYL b i; haveI:= RΦayCanYL b i
 exact CharterAtlasYL R G t T U J0 f E Z (rayonZYL b i) (rayMoveYL a p k r b i) _ (RΦayPriceYL b i) (RΦayMotionYL a p b i k r) (RΦayHappyYL a p b i k r h) U2
lemma asAtlasTYL (h:calmYL k a r p b):AtlasYL R G t U (TopNoteYL t k b a p F r):=by
 let M(i:Axis):= SoundQYL a p k b i r (Fin.cons (TotalStarsMars t i a) F)
 have P:AtlasYL R G t U (fun C=> ∑ i:Axis,M i C):=fiatAtlasYL R G t U J0 f E Z Finset.univ M (fun i=>asAtlasQYL R G t a p U J0 f E Z k b r U2 i _ h) -- tune argument P.s
 have he:= plusAtlasYL R G t U J0 f E Z (focusAtlasYL R G t p F U J0 f E Z (calm0_YL k p b a r h).bounds) (scalAtlasYL R G t U r P)
 have hu:= plusAtlasYL R G t U J0 f E Z (focusAtlasYL R G t _ F U J0 f E Z (calm1_YL k p b a r h).bounds) (scalAtlasYL R G t U (-1) he)
 convert hu using 1; ext C; change _- (_ + r • _) = C n F _+ _; rw [neg_one_mul,Complex.real_smul,sub_eq_add_neg]; -- rfl?
lemma asAtlasAYL (h:BreatherMars b k p): AtlasYL R G t U (AnthemYL t k b a p F):= fiatAtlasYL R G t U J0 f E Z _ _ (fun j=>fiatAtlasYL R G t U J0 f E Z _ _ fun i=>asAtlasPYL R G t p U J0 f E Z k b U2 i _ h)
omit J0 U E Z f U2
variable {t}
variable {Y:Ember.Hulse.AreaQc S}(H:FirstPackMars t Y) (W:NSF.Table.Hierarchy (BellTableMars t Y))
include H W
lemma VotesTYL (q:y∈conf m)(h:calmYL k a r p b): ∀ᶠ i in atTop, TopNoteYL t k b a p F r (DistantC_YL (CloudMeanL t Y) m V y i)=0 :=by
 filter_upwards [calmPathYL y k b _ (ledgeSureYL a p k r) h q] with i hp
 let G:=CloudMeanL t Y; let N:= apartYL (EarYL i) p y; let V':= Fin.append F V; let X:= DistantC_YL (CloudMeanL t Y) m V y i; let k':= k.castAdd m
 have hz(u:ℝ):ledgeYL k' a r N u= apartYL (EarYL i) (ledgeYL k a r p u) y:= ledgeUpYL a p k r _ _ _
 have ht:calmYL k' a r N b:=fun u v=>hz u |>.symm ▸ hp _ v
 apply sub_eq_zero.mpr; change habYL t Y V' _=_; rw [←hz, PromiseYL H W k' V' N b a r ht]; change _+ r • _= habYL t Y V' N + r • _
 congr 2; refine Finset.sum_congr rfl fun j _=>?_ ; unfold SoundQYL ScrollOpYL; apply integral_congr_ae; refine Eventually.of_forall fun z=>congrArg (rayPenYL b j z *·) ?_
 change G _ (YM.Points.cons _ (ledgeYL _ _ _ _ _)) _= G _ (apartYL _ _ _) _; rw [hz, CrownAddYL]
omit H W
lemma InkBAppendYL {X:Type*}(f:Fin n→X)(g: Fin m→X)(x:X): Function.update (Fin.append f g) (k.castAdd m) x= Fin.append (Function.update f k x) g:=by
 ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
 · by_cases p:i=k
   · subst k; simp
   have hv:i.castAdd m≠ k.castAdd m:=fun v=> p (by have t:=congrArg Fin.val v; exact Fin.ext t)
   simp [p,hv] -- tune
 have he: Fin.natAdd n i≠ k.castAdd m:=ne_of_gt (show k.val < n+i.val from lt_of_lt_of_le k.2 (by omega)); simp [he]
include H W
lemma VotesAYL(q:y∈conf m)(h:BreatherMars b k p):∀ᶠ i in atTop, AnthemYL t k b a p F (DistantC_YL (CloudMeanL t Y) m V y i)=0:=by
 let X:=fun _:ℝ=>p
 filter_upwards [calmPathYL y k b X continuous_const (fun _ _=>h) q] with i hp
 let N:=apartYL (EarYL i) p y; have he:BreatherMars b (k.castAdd m) N:=hp 0 (by simp [α0_YL])
 let G:=CloudMeanL t Y
 rw [←StillPointYL H W (k.castAdd m) (Fin.append F V) N b a he]; unfold AnthemYL
 apply sum_congr rfl; intro j _; apply sum_congr rfl; intro u _
 rw [InkBAppendYL k] -- unused H W if omit
 unfold MeterA_YL raysCostYL; apply integral_congr_ae; refine Eventually.of_forall fun z=>?_ ; apply congrArg (Analysis.D (basis u) b.f z • ·); exact CrownAddYL G p (Function.update F k (TotalStarsMars t j a)) y V _ z _
#print axioms VotesTYL
#print axioms VotesAYL
#print axioms asAtlasTYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
