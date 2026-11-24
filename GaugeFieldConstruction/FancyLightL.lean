import GaugeFieldConstruction.PewMars
import GaugeFieldConstruction.MootHoldL
import GaugeFieldConstruction.TierceHaloL
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
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric NSF.Boundary
variable {n:ℕ}{cost:ℕ→P.Test→ℂ} (C:Porch P cost timeAxis)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X F:CloudsL}
open NSF.Work.C22 -- uses Types aliases in YM.Boundary need namespace qualified
local notation "Ξ"=> C.groundHab
local notation "Eχ"=> C.BrightHab.E
local notation "Uₛ"=> C.BrightHab.U
local notation "Bφ" x:max=> Small.bufferF x
variable (A:AllocatedL P) (R:ΧiMars →ₗ[ℂ]ScreensJ P)
open NSF.LD
-- purchase trace exactly across BOTH S & parts. sᵧ≠S support pre-tilt allowed uses only on-image real poses. δ-rate
variable (X) (D:SurfCheckL F)
structure CheckΩL (R:ΧiMars →ₗ[ℂ]ScreensJ P):Prop where
 showL : ∀ x:ΧiMars, AttainedR 0 (R x)
 warmL : ∀ (p:ΧiMars) (j:Axis) (v:PermWallJ P), R (TurnupMars j p) j v v= Star.star (R p j v v)
-- applies TRUE on pure expressions from cost predicate
structure CalRL (C:∀ j:Axis, Porch P cost j) (Z:CloudsL) (R:ΧiMars →ₗ[ℂ]ScreensJ P): Prop extends CheckΩL R where
 salute (n:ℕ)(F:Fin n→ΧiMars)(x:Points n)(g:ΦplanR _ x∈ VplaneR _ timeAxis): Z n x F=SπR C (fun i=>R (F i)) (ΦplanR n x)
#check TurnupMars
-- ordered real Chron
variable (Cw:∀ j:Axis, Porch P cost j)
lemma CageL {p:ℝ≥0}(hx:0<p)(x:NSF.Boundary.Heights n)(r:SpacePoints n)(u:∀ i j:Fin n,i<j→ ((p+p:ℝ≥0):ℝ)<x j-x i): ΦplanR n (place r x)∈ OpenR timeAxis (fun _=> A.pad p) (List.finRange n):=by
 have h:(List.finRange n).Pairwise (fun i j=>i<j):=List.pairwise_lt_finRange _
 apply h.imp; intro i j y; have hc:= u i j y; rw [NNReal.coe_add] at hc
 change (position _ _).ofLp timeAxis + _ < (position _ _).ofLp timeAxis - _; simp only[position, WithLp.ofLp_toLp, Fin.snoc_last]; linarith [A.cent hx]
lemma cageStampL p (y:NSF.Boundary.Heights n)(x:SpacePoints n)(w:Fin n→(SurfRimL F).Tag): let v:= stampsEL D w; let σ : Fin n→PermWallJ P:= fun _=>A.pad p
 RutterL C A R D p y x w=billActMars C σ (BodyΘ P (fun i=>R (v i)) timeAxis σ) (ΦplanR n (place x y)) (List.finRange n):=by
 dsimp only; unfold RutterL billActMars; rw [List.ofFn_eq_map]; rfl -- tune
variable (g:CalRL Cw X R)
local notation "Bψ"=> SmallRimL (Cw timeAxis) R A X D
include g
lemma pureRL: CharterL (Bψ) where
 pure {n} p y x v h hp:=by
    have he:= EchoRimL (Cw timeAxis) X A R D p y x v hp; have hz:= CageL A hp.1 y x (fun i j h=>by rw [NNReal.coe_add]; linarith [hp.2.2 i j h,p.coe_nonneg])
    let W:= ΦplanR _ (place x y); let V:= SurfRimL F; let G(i):=R (stampsEL D v i); let σ:Fin n→PermWallJ P:= fun _=> A.pad p
    have hK:PolesR (List.finRange n):=deckΦP n -- tune
    change _=(SurfRimL F).useAt _ (place x y) v
    rw[D.chartAngleL,g.salute n _ _ (char_R ⟨hK,OpenRollR hz⟩)]; rw [cageStampL (Cw timeAxis) A R D p y x v] at he
    exact he.trans (Eq.symm ((ηTenderR Cw (List.finRange n) G (fun i=>g.showL _) timeAxis σ W hK hz).trans (EarningActorMars ..)))
-- shots. C22 h.v Room.Q. pure join via Gram.Orth.
omit g
noncomputable def CompellL p (y:NSF.Boundary.Heights n)(x:SpacePoints n)(h:Room p 0 y 0)(v:0<p): StallLeadMars timeAxis (place x y) P where
 L:= List.finRange n
 σ i:= A.pad p
 pol:=deckΦP n
 pays:= CageL A v y x h.2
 toll i:=by have he:=h.1 i; rw [sub_zero,zero_add] at he; change 0 < YM.time (position _ _)-_; simp only [time_position]; linarith [A.cent v]
lemma traceVectorL p (y:NSF.Boundary.Heights n)(x:SpacePoints n)(w:Fin n→(SurfRimL F).Tag)(h:Room p 0 y 0)(v:0<p):
 fromRef (SmallRimL C R A X D) p 0 (iz ∘ y) x (pinned ∘ w) 0 0 = ChargeEntryMars C (CompellL A p y x h v) (fun i=>R (stampsEL D w i)):=by
 have he:=FromRawL C X A R D p 0 y x w 0 0 v h
 rw [show iz 0=0 from by simp [iz],B_OpeningL,neg_zero] at he
 have ht :(Uₛ (0:NSF.OS.Cross timeAxis))=ContinuousLinearMap.id ℂ C.DegreeHab:= C.BrightHab.uZero
 rw [ht,ContinuousLinearMap.id_apply, cageStampL C A R D] at he; rw [zero_add,NNReal.coe_zero] at he; exact he -- tune
#print axioms pureRL
#print axioms traceVectorL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
