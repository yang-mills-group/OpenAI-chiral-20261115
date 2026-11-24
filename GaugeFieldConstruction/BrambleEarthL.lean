import GaugeFieldConstruction.StarReefL
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
include v
lemma DeltaEastL {s:SO}{b: Axis}(h:suitAxL s a b):eastL n b (motionMoonMars s p):=by
 constructor
 · intro i j q; dsimp only; rw [show motionMoonMars s p i b=_ from h (p i), show motionMoonMars s p j b=_ from h (p j)]; exact v.1 q
 intro i; rw [show motionMoonMars s p i b=_ from h (p i)]; exact v.2 i
omit v
local notation "Ηj"=>LightLiftL (Cw a)
variable (K:SunlitL Cw R G)(f: SurfCheckL.boisterL t G)
-- norm-squared defect of translation in space AT p cluster. Expression without inf-rates.
noncomputable def MapFareL (b:Axis)(x:Points n)(F:Fin n→ΧiMars)(z: OS.Cross b)(q:ℝ≥0):ℝ:=2*((GulfPriceL Cw R F F b x (ReefMapL (q+q) 0 x (j:=b))).re - (GulfPriceL Cw R F F b x (ReefMapL (q+q) z x)).re)
local notation "φH"=> RiverBoreL Cw R a F p J
lemma mapMeshL (U:CheckΩL R) (z:OS.Cross a)(q:ℝ≥0): MapFareL Cw R a p F z q= ‖(Ηj).E q φH-(Ηj).U z ((Ηj).E q φH)‖^2:=by
 unfold MapFareL; rw [norm_sub_sq (𝕜:=ℂ),(Ηj).unitary]
 rw[←ReefRealL Cw R U F F a _ _ J J,←ReefRealL Cw R U F F a _ _ J J] -- pattern
 let x:= (Ηj).E q φH
 have hu: inner ℂ φH ((Ηj).E (q+q) φH)=inner ℂ x x :=by unfold x; rw [NSF.OS.Semigroup.time,ContinuousLinearMap.comp_apply, ← (Ηj).swing]
 have he: inner ℂ φH ((Ηj).E (q+q) ((Ηj).U z φH))=inner ℂ x ((Ηj).U z x):=by unfold x; rw [NSF.OS.Semigroup.time,ContinuousLinearMap.comp_apply,←ContinuousLinearMap.comp_apply ((Ηj).E q) ((Ηj).U z), (Ηj).independent,← (Ηj).swing]; rfl
 rw[(Cw a).BrightHab.uZero, ContinuousLinearMap.id_apply, hu,show ((Cw a).BrightHab.U z) = (Ηj).U z from rfl,he]; change 2*((inner ℂ x x).re - _) = _
 have hp : (inner ℂ x x).re= ‖x‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) x; rw [hp]; unfold x; ring_nf; try rfl
lemma tideMapL (U:CheckΩL R)(z:OS.Cross a): Tendsto (MapFareL Cw R a p F z) atTop (𝓝 (‖(Ηj).orth φH-(Ηj).U z ((Ηj).orth φH)‖^2)):=by
 have he:= (Ηj).emerges φH
 exact (he.sub (((Ηj).U z).continuous.continuousAt.tendsto.comp he)|>.norm|>.pow 2).congr (fun i=> (mapMeshL Cw R a p F J U z i).symm) -- local λ tune etc
-- all orientation by Proper-S. REAL clusters, no conjugation continuity assumptions
include K f J
lemma lucreL (z:OS.Cross a){s:SO}{b:Axis}(h:suitAxL s a b): MapFareL Cw R a p F z= MapFareL Cw R b (motionMoonMars s p) (compassPiMars t s ∘ F) (PlissCL h z):=by
 funext q; unfold MapFareL
 rw [OroLineL Cw R G t K f J (ReefShedsL p J (q+q) 0) h, OroLineL Cw R G t K f J (ReefShedsL p J (q+q) z) h,DistantL h,Pliss0L, DistantL h] -- pattern maybe if z local
local notation "P_λ" a:max=> LightLiftL (Cw a)
omit f J
lemma reefCalL: CalRL Cw G R:= ⟨K.toCheckΩL,fun n v x h=> K.invoice _ _ _ (Set.mem_iUnion.mpr ⟨_,h⟩)⟩
variable (A:AllocatedL P)(D:SurfCheckL G){Z:NSF.Boundary.Waves (SurfRimL G)}{W:NSF.Boundary.Surface (SurfRimL G)}{S': Spins (SurfRimL G)}
variable (g:LoreL Z S' W (SurfRimL G))(c: (SurfRimL G).RealSpin)
include f J v A D g c
lemma argentL (z:OS.Cross a): Tendsto (MapFareL Cw R a p F z) atTop (𝓝 0):=by
 obtain ⟨s,h⟩:= PlanetSuitL a timeAxis
 have he:= DeltaEastL a p v h
 let L:= ReefBedL (P:=P) (motionMoonMars s p) he
 obtain ⟨m⟩:=L
 let E:= LightLiftL (Cw timeAxis); let b:= PlissCL h z; let y:=RiverBoreL Cw R timeAxis (compassPiMars t s ∘ F) _ m
 have hp:E.ℚmeasure.region Mink.coneᶜ y=0:= SupportsB_L Cw R D (reefCalL Cw R G K) D A c (fun _=> le_rfl) g _ _ he m
 have hw:= NSF.Boundary.Ferry.seeds_free E y hp b.val
 have hm:E.U b (E.orth y)=E.orth y:=by
    change E.edge (b.val _) (E.U _ (E.orth _))=_ at hw; rw [show (b.val _) =0 from b.property, E.birth, ContinuousLinearMap.id_apply,show NSF.OS.Semigroup.SEP timeAxis b.val=b from ?_] at hw; exact hw
    apply Subtype.ext; change b.val-b.val timeAxis • basis _=_; rw [show b.val timeAxis=0 from b.property]; simp
 rw [lucreL Cw R G t a p F J K f z h]
 have ht:= tideMapL Cw R timeAxis (motionMoonMars s p) (compassPiMars t s ∘ F) m K.toCheckΩL b
 rw [show LightLiftL _=E from rfl,show RiverBoreL _ _ _ _ _ m = y from rfl, hm, sub_self] at ht; simpa using ht
#print axioms argentL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
