import GaugeFieldConstruction.CosmosSpeΛ
import GaugeFieldConstruction.OrchardFastYL

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

-- real cone claim
variable (D:AllocatedL P){A:CloudsL}(V:SurfCheckL G)(H: SurfCheckL A){Z:NSF.Boundary.Waves (SurfRimL A)}{W:NSF.Boundary.Surface (SurfRimL A)}{S': Spins (SurfRimL A)}
variable (Lp:LoreL Z S' W (SurfRimL G))(c: (SurfRimL A).RealSpin)
lemma CrownSpeΛ : SkyRootsSpeΛ timeAxis=Mink.cone:=by
 ext1 x; let y:=SEP timeAxis x
 have hv : time y.val=0:= (SEP timeAxis x).property
 have hs : spatial y.val=spatial x:= by
    change spatial (x-x timeAxis • basis timeAxis)=_ ; rw[sub_eq_add_neg]; simp
 have he:‖y.val‖= ‖spatial x‖:=by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),Mink.squares,hv,hs]; simp
 change ‖y.val‖≤ _ ↔ ‖spatial x‖ ≤ _; rw [he]; rfl
include v K uF Lp c D H V
lemma supportCoreSpeΛ : ((LightLiftL (Cw a)).ℚmeasure).region (SkyRootsSpeΛ a)ᶜ (RiverBoreL Cw R a F p J)=0:=by
 obtain ⟨g,h⟩:= PlanetSuitL a timeAxis
 have hp:= DeltaEastL a p v h; obtain ⟨m⟩:= ReefBedL (P:=P) (motionMoonMars g p) hp
 rw [pShiftSpeΛ Cw R G t a p F J K uF h m, CrownSpeΛ]; exact SupportsB_L Cw R H (reefCalL Cw R G K) V D c (fun i=> le_of_eq ((H.FlagsL i).trans (V.FlagsL i).symm)) Lp _ _ hp _
omit v
lemma shineSpecΛ: ((LightLiftL (Cw a)).ℚmeasure).region (SkyRootsSpeΛ a)ᶜ (RiverBoreL Cw R a F p J)=0:=by
 let d:= Tuple.sort (fun i=> p i a); let p':=NSF.Points.rearrange d p; obtain ⟨H',e⟩:= StallRecitesYL Cw R a p F J d; rw[←e]; refine supportCoreSpeΛ Cw R G t a p' ?_ _ _ K uF D V H Lp c
 refine ⟨Monotone.strictMono_of_injective (Tuple.monotone_sort (fun k=> p k a)) (StallWestYL a p' H'),fun i=>?_⟩; exact lt_of_lt_of_le (H'.toll i) (sub_le_self _ (H'.σ i).2.le)
-- explicit canonical view of momentum H vectors.cyclic on strictly positive
omit K uF Lp c D H V in
abbrev ΧMΦSpecΛ(Cw:∀ a:Axis,Porch P cost a)(R:ΧiMars →ₗ[ℂ]ScreensJ P)(a:Axis):Set (Cw a).DegreeHab := {v | ∃ (n:ℕ)(p:Points n)(F:Fin n→ΧiMars)(J:StallLeadMars a p P), v =RiverBoreL Cw R a F p J}
omit K uF Lp c D H V in
abbrev AxFearSpeΛ :Prop:=∀ (a:Axis)(x:(Cw a).DegreeHab), x ∈ (Submodule.span ℂ (ΧMΦSpecΛ Cw R a)).topologicalClosure → ((LightLiftL (Cw a)).ℚmeasure).region (SkyRootsSpeΛ a)ᶜ x=0
lemma AxSpeΛ: AxFearSpeΛ Cw R:=by
 intro a; let U:=(LightLiftL (Cw a)).ℚmeasure.region (SkyRootsSpeΛ a)ᶜ
 have he:ΧMΦSpecΛ Cw R a ⊆ ↑U.ker:=by
    rintro i ⟨n,p,F,J,rfl⟩; exact shineSpecΛ Cw R G t a p F J K uF D V H Lp c
 intro i hi; exact (Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr he) U.isClosed_ker (show i ∈ _ from hi) : i∈ U.ker) -- method name tune
#print axioms shineSpecΛ
#print axioms AxSpeΛ
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
