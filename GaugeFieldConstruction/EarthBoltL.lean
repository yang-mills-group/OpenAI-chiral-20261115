import GaugeFieldConstruction.ReefActorL
import GaugeFieldConstruction.EirTorchL
import GaugeFieldConstruction.SpringBoltL
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
open Complex YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric NSF.Boundary
open NSF.Work.C22 NSF.Work.C23 NSF.LD
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n:ℕ}
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P)
noncomputable def GulfPriceL {a b:ℕ}(S: Fin a→ΧiMars)(F:Fin b→ΧiMars)(j:Axis)(x:Points a)(y:Points b):= SπR Cw (R ∘ (Fin.append (TurnupMars j ∘ S) F)) (ΦplanR _ (NSF.Table.Pairing.closedUp j x y))
noncomputable def RiverBoreL (j:Axis)(X:Fin n→ΧiMars)(x:Points n)(A:StallLeadMars j x P):= ChargeEntryMars (Cw j) A (fun i=>R (X i))
variable (u:CheckΩL R)
include u
lemma GulfSignL {a b:ℕ}(S:Fin a→ΧiMars)(F:Fin b→ ΧiMars)(j:Axis)(x:Points a)(y:Points b)(p:StallLeadMars j x P)(q:StallLeadMars j y P):
 inner ℂ (RiverBoreL Cw R j S x p) (RiverBoreL Cw R j F y q)=GulfPriceL Cw R S F j x y:=by
 let S':=R ∘ (TurnupMars j ∘ S); let F':=R ∘ F
 have he:= BookingActMars Cw (R ∘ S) F' S' x y p q (fun i=>u.warmL (S i) j) (fun i=>u.showL _) (fun i=>u.showL _)
 refine he.trans (congrArg (fun f:Fin (a+b)→ ScreensJ P=> SπR Cw f (ΦplanR _ (NSF.Table.Pairing.closedUp j x y))) ?_)
 ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp <;> rfl
lemma ReefRealL {a b:ℕ}(S:Fin a→ΧiMars)(F:Fin b→ ΧiMars)(j:Axis)(x:Points a)(y:Points b)(p:StallLeadMars j x P)(q:StallLeadMars j y P) (t:ℝ≥0)(z:OS.Cross j): inner ℂ (RiverBoreL Cw R j S x p) (((LightLiftL (Cw j)).E t) ((Cw j).BrightHab.U z (RiverBoreL Cw R j F y q)))= GulfPriceL Cw R S F j x (ReefMapL t z y) :=by rw [←GulfSignL Cw R u S F j _ _ p (ReefShedsL y q t z)]; exact congrArg (inner ℂ (RiverBoreL ..)) (TrailMovedL (Cw j) _ _ _ _ _).symm
lemma FeelRiverL (j:Axis)(X:Fin n→ΧiMars)(x:Points n)(p q:StallLeadMars j x P): RiverBoreL Cw R j X x p=RiverBoreL Cw R j X x q:=by
 apply sub_eq_zero.1; apply inner_self_eq_zero (𝕜:=ℂ) |>.1; simp_rw [inner_sub_left,inner_sub_right,GulfSignL Cw R u X X j x x]; ring
omit u
abbrev eastL (n:ℕ)(j:Axis)(x:Points n):Prop:= StrictMono (fun i=>x i j)∧ NSF.Points.allAbove j 0 x
lemma ReefBedL (x:Points n)(h:eastL n j x): Nonempty (StallLeadMars j x P):= AppointsMars j x ⟨h.1.injective,h.2⟩ P
lemma eastPadL (y:NSF.Boundary.Heights n)(h:y∈ positiveHeight n):∃ p:ℝ≥0,Small.ample p y:=by
 have hc:Continuous (fun p:ℝ≥0=>4*(p:ℝ)):=by fun_prop
 have hp:Tendsto (fun p:ℝ≥0=>4*(p:ℝ)) (𝓝[>] 0) (𝓝 0):=by simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi _))
 have he:∀ᶠ p:ℝ≥0 in 𝓝[>] 0, ∀ i j:Fin n,i<j→4*(p:ℝ)< y j-y i:=by
    apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j; by_cases v:i<j
    · filter_upwards [hp.eventually (gt_mem_nhds (sub_pos.mpr (h.1 v)))] with p e v using e
    exact Eventually.of_forall fun p q=>(v q).elim
 have hh:∀ᶠ p:ℝ≥0 in 𝓝[>] 0, ∀ i:Fin n,4*(p:ℝ)<y i:= eventually_all.mpr fun i=> hp.eventually (gt_mem_nhds (h.2 i))
 apply Filter.Eventually.exists (f:=𝓝[>] (0:ℝ≥0)); filter_upwards [he,hh,self_mem_nhdsWithin, (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with p v w z x using ⟨⟨z,x,v⟩,w⟩
variable {X F: CloudsL}(D:SurfCheckL F)
variable (V:CalRL Cw X R) (hX:SurfCheckL X) (A: AllocatedL P)
local notation "ΚHa"=> LightLiftL (Cw timeAxis)
local notation "Bψ"=> SmallRimL (Cw timeAxis) R A X D
lemma handDawnL {t:ℝ≥0} (k:NSF.Boundary.Heights n)(r:SpacePoints n)(u:Small.ample t k)(v:Fin n→ΧiMars):∃ e:Fin n→(SurfRimL F).Tag,(Bψ).shot t n (pinned∘ e) k (place r 0)= RiverBoreL Cw R timeAxis v (place r k) (CompellL A t k r (ample_room u) u.1.1):=by
 let D':= CompellL A t k r (ample_room u) u.1.1; let z(i:Fin n): (SurfRimL F).Tag:=⟨0,(D.HingeL 0).symm (v i)⟩; refine ⟨z,?_⟩
 have h:=traceVectorL (Cw timeAxis) X A R D t k r z (ample_room u) u.1.1
 rw [fromPoint]
 have hp:stampsEL D z=v:=by ext1 i; exact LinearEquiv.apply_symm_apply ..
 let b:Points n:=place r 0
 rw [hp] at h
 rw [show NSF.Boundary.shift (place r 0) k=iz ∘ k from funext fun i=> by simp [NSF.Boundary.shift,place,iz]] -- tune
 rw [show NSF.Boundary.trace b=r from funext fun i=>by simp [b,place,NSF.Boundary.trace]] -- tune
 exact h
variable {W:Surface (SurfRimL F)}{Z:NSF.Boundary.Waves (SurfRimL F)}{K:Spins (SurfRimL F)}
include V hX A D
lemma SupportsB_L (s:(SurfRimL F).RealSpin)(c:(SurfRimL X).respects (SurfRimL F))(k:LoreL Z K W (SurfRimL X))(T:Fin n→ΧiMars)(x: Points n)(h:eastL n timeAxis x)(e:StallLeadMars timeAxis x P):
    (ΚHa).ℚmeasure.region Mink.coneᶜ (RiverBoreL Cw R timeAxis T x e)=0:=by
 let yZ:NSF.Boundary.Heights n:=fun i=>x i timeAxis; let rZ:SpacePoints n:=NSF.Boundary.trace x
 rcases show ∃ (y:NSF.Boundary.Heights n)(v: SpacePoints n), x= place v y from ⟨yZ,rZ,(by ext1 i; exact (Mink.divide.symm_apply_apply (x i)).symm -- tune
 )⟩ with ⟨y,r,g⟩
 subst x
 obtain ⟨p,hp⟩:= eastPadL y (show y∈positiveHeight n from ⟨fun i j d=>h.1 d, fun i=>h.2 i⟩) -- defeq tune
 obtain ⟨v,b⟩:=handDawnL (X:=X) Cw R D A y r hp T
 have hu:= Ferry.cone_shine k.tilted k.habitat k.heat k.estimates k.joints.int Bψ (StageAnswer D.RiseFrameL (D.RiseKnownL _) D.PlannerL.toSymmetric hX.PlannerL.toSymmetric k.heat c (HullStageηL X A R D Cw V hX Z k.heat s) (D.AsterLiberL s)) (pinned∘ v) p y hp (place r 0)
 rw [b] at hu; rw [FeelRiverL Cw R V.toCheckΩL timeAxis T _ e (CompellL A p y r (ample_room hp) hp.1.1)]; exact hu
#print axioms SupportsB_L
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
