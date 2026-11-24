import GaugeFieldConstruction.FancyLightL
import GaugeFieldConstruction.BrimstoneS
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
local notation "ΦH"=> C.BrightHab
local notation "ΩH"=> C.groundHab
variable {n:ℕ}
open NSF.Table.Pairing
-- all real translations repriced; Also can shuffle labels & points by Chron sorter only.
noncomputable def ReefOutL (t:ℝ≥0)(b:OS.Cross j) :E4:= (t:ℝ) • basis j+b.val
noncomputable def ReefMapL (t:ℝ≥0)(b:OS.Cross j)(x:Points n):= NSF.Points.across (ReefOutL t b) x
lemma ReefShiftL (t:ℝ≥0)(b:OS.Cross j)(x:Points n)(i:Fin n):ΦplanR n (ReefMapL t b x) i= ΦplanR n x i+(ReefOutL t b).ofLp:=by funext z; simp [ΦplanR,ReefMapL, NSF.Points.across,ReefOutL,points, add_comm] -- tune
lemma ReefRodL (t:ℝ≥0)(b:OS.Cross j): ReefOutL t b j=(t:ℝ):=by simp [ReefOutL,show b.val.ofLp j=0 from b.property]
lemma ReefStarL (t:ℝ≥0)(b:OS.Cross j): diameter (a:=j) (ReefOutL t b).ofLp=b:=by
 apply Subtype.ext; ext1 i; by_cases p:i=j
 · subst i; exact (diameter (ReefOutL t b).ofLp).property.trans b.property.symm
 rw[diameter_at _ _ p]; simp [ReefOutL,p] -- tune
variable (x:Points n)(S:Fin n→ScreensJ P)(A:StallLeadMars j x P)
noncomputable def ReefShedsL (t:ℝ≥0)(b:OS.Cross j):StallLeadMars j (ReefMapL t b x) P where
 L:=A.L
 σ:=A.σ
 pol:=A.pol
 pays := by refine (show RollBestR _ _ from A.pays).imp fun {k i} h=>?_ ; rw[ReefShiftL, ReefShiftL, Pi.add_apply, Pi.add_apply]; linarith
 toll i:=by
    change 0< ΦplanR _ (ReefMapL t b x) i j-_ ; rw[ReefShiftL,Pi.add_apply, ReefRodL]
    have he : 0 < ΦplanR _ x i j - StallJ P (A.σ i):= A.toll i
    linarith [t.coe_nonneg]
variable {I:Type}[Fintype I][DecidableEq I](σ:I→PermWallJ P)(V:I→P.Slabs j)(T:I→Axis→ℝ)
lemma ReefGlidesL (L:List I)(R:ℝ)(t:ℝ≥0)(z:OS.Cross j): ActorMars C.BrightHab C.groundHab (some (R+t)) (billActMars C σ V (fun i=> T i +(ReefOutL t z).ofLp) L)= C.BrightHab.U z (ActorMars C.BrightHab C.groundHab (some R) (billActMars C σ V T L)):=by
 let A:= StageR σ C V; let p:=(ReefOutL t z).ofLp; let H(i:I):=T i+p
 simp_rw [←WagonMars]; change A.roadList _ H _= _; rw[←ReefStarL t z] -- tune RHS too
 -- need hH
 induction L generalizing R with
 | nil=> exact (waxSureL C _).symm
 | cons i L ih=>
    have hv:= ih (A.endline (T i) i)
    change A.gliding _ _ (H i) (A.roadList L H (some (A.endline (H i) i)))=_
    rw [show H i=T i+p from rfl,A.end_add,show p j= (t:ℝ) from ReefRodL t z,hv]
    -- trajectory
    let U:= C.BrightHab; have hy:= DFunLike.congr_fun (A.trajectory (some R) i (T i) p) (A.roadList L T (some (A.endline (T i) i))); rw [Option.map_some,show p j=(t:ℝ) from ReefRodL t z] at hy; exact hy 
lemma TrailMovedL (t:ℝ≥0)(z:OS.Cross j): ChargeEntryMars C (ReefShedsL x A t z) S= (ΦH).E t ((ΦH).U z (ChargeEntryMars C A S)):=by
 let Dn:=ReefMapL t z x; let a:=billActMars C A.σ (BodyΘ P S _ A.σ) (ΦplanR _ Dn) A.L
 have he:AheadActorMars (t:ℝ) a:=by
    intro i h; obtain ⟨k,_,rfl⟩:= List.mem_map.mp h; change _ ≤ _ - _; rw [ReefShiftL,Pi.add_apply,ReefRodL]; have hu:0 < ΦplanR _ x k j - StallJ P (A.σ k):=A.toll k; linarith
 change ActorMars _ _ _ a = _; rw [LedgeActMars C.BrightHab C.groundHab (SpireHTMars C) a 0 (t:ℝ) he t.coe_nonneg, sub_zero]; simp only [Real.toNNReal_coe]
 unfold a Dn; rw [funext (ReefShiftL t z x)]; have hd:= ReefGlidesL C A.σ (BodyΘ P S _ A.σ) (ΦplanR _ x) A.L 0 t z; rw [zero_add] at hd; rw [hd]; rfl
#print axioms TrailMovedL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
