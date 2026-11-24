import GaugeFieldConstruction.AntwerpMars
import GaugeFieldConstruction.BrigandL
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
section
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
-- Semigroup transplant E and U; only positivity used around p; coherent joint kernel Cent.
local notation "ΦH"=> C.BrightHab
noncomputable def LightLiftL : NSF.OS.Semigroup C.DegreeHab j:=⟨(ΦH).E,(ΦH).U,(ΦH).eZero,(ΦH).time,(ΦH).shrinks,(ΦH).sym,(ΦH).uZero,(ΦH).space,(ΦH).unitary,(ΦH).independent,(ΦH).continuousE,(ΦH).continuousU⟩ -- macro
lemma waxSureL t: C.BrightHab.U t C.groundHab=C.groundHab:=by
 let X:= C.BrightHab; have ht: X.unit.translation t.val C.groundHab=C.groundHab:= (SelectionAnalysis.invariant_glass C.canopy (daylight (timeMesh P.par)) C.Time C.heat_share C.groundHab).2 ?_ t.val
 · let b:= OS.Semigroup.SEP j; change X.edge (t.val j) (X.U (b t.val) C.groundHab)=_ at ht
   rw [show t.val j=0 from t.property,show b t.val=t from ?_,X.birth] at ht; exact ht
   apply Subtype.ext; change t.val-t.val j • basis j=_; rw [show t.val j=0 from t.property]; simp
 exact ⟨(SelectionAnalysis.lamp_fixed C.Time C.Ω).2 (fun t=>by rw [C.heat,C.still]), C.Ω_ready⟩
open YM.GaugeFieldConstruction.Ember.Volumetric YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember
variable (Z:CloudsL)
noncomputable def ShallowPortL:NSF.Boundary.LRoom (SurfRimL Z) j:=⟨C.DegreeHab,LightLiftL C,C.groundHab,C.normΩ,waxSureL C,SpireHTMars C⟩
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
-- portfolio in U4 fields. winding map δAN n heights, depends on H but arbitrary B p.Power q independent.Actual.
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P)
structure AllocatedL (P:Spine) where
 pad (p:ℝ≥0): PermWallJ P
 cent {p:ℝ≥0}(h:0<p): StallJ P (pad p) < (p:ℝ)
variable (A:AllocatedL P)
abbrev shadowL (p:ℝ≥0)(x:ΧiMars): P.Slabs j:= R x j (A.pad p) (A.pad p)
abbrev slitL (p:ℝ≥0):ℝ≥0:= ((p:ℝ)-StallJ P (A.pad p)).toNNReal
lemma slotPayL {p:ℝ≥0}(h:0<p):↑(slitL A p)=(p:ℝ)-StallJ P (A.pad p):=Real.coe_toNNReal _ (sub_nonneg.mpr (A.cent h).le)
local notation "γ" i:max => C.BrightHab.E i
noncomputable def RimTimeL (k:ℝ≥0) : ΧiMars →ₗ[ℂ] C.DegreeHab.Op where
 toFun x:= (γ (slitL A k)).comp ((LadderRackMars C (shadowL R A k x)).comp (γ (slitL A k)))
 map_add' x y:=by simp [LadderRackMars,shadowL,Pi.add_apply] -- tune
 map_smul' c x:=by simp [LadderRackMars,shadowL]
#print axioms RimTimeL
end
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric NSF.Boundary
variable {n:ℕ}
lemma keepingL(t w:Space3):Small.bufferF (t-w)=Small.bufferF t - Small.bufferF w:=by
 apply Subtype.ext; ext1 i; refine Fin.lastCases ?_ ?_ i
 · simp [Small.bufferF,position]
 intro i; simp [Small.bufferF, position]
lemma crossRunL (x:Space3)(t:ℝ): diameter (a:=timeAxis) ((position x t).ofLp) = Small.bufferF x :=by
 apply Subtype.ext; ext1 i; refine Fin.lastCases ?_ ?_ i
 · exact (diameter _).property.trans (Small.bufferF x).property.symm
 intro i; rw[diameter_at (a:=timeAxis) _ _ (Fin.castSucc_ne_last _)]; simp [position, Small.bufferF] -- tune
-- imaginary rip
lemma hopeτL (y t:ℝ)(p:ℝ≥0):Small.interval (NSF.Work.C22.iz y-NSF.Work.C22.iz t) p=((y-t-(p:ℝ) :ℝ):ℂ):=by unfold Small.interval NSF.Work.C22.iz NSF.OS.Semigroup.duration; apply Complex.ext <;> simp [sub_im]
variable {cost:ℕ→P.Test→ℂ} (C:Porch P cost timeAxis)
lemma flyL (X:CloudsL)(y t:ℝ)(p:ℝ≥0)(h:(p:ℝ)< y-t)(x:Space3): Small.rip (C:=ShallowPortL C X) (NSF.Work.C22.iz y-NSF.Work.C22.iz t) p x=(C.BrightHab.E ((y-t-(p:ℝ)).toNNReal)).comp (C.BrightHab.U (Small.bufferF x)):=by
 unfold Small.rip; rw [hopeτL]; let S:= (ShallowPortL C X).flow; let g :ℝ≥0:=(y-t-p).toNNReal; have hp:0<g:=Real.toNNReal_pos.mpr (sub_pos.mpr h)
 rw[show ((y-t-(p:ℝ):ℝ):ℂ)= NSF.OS.Semigroup.duration g from ?_, NSF.OS.Semigroup.roots_heat S hp]; swap
 · exact congrArg _ ((Real.coe_toNNReal _ (sub_nonneg.mpr h.le)).symm)
 rfl
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X F:CloudsL}
-- S is mean. F Eu kernels on this RT version. B calibrated to F chamber.H
noncomputable def SmallRimL (R:ΧiMars →ₗ[ℂ]ScreensJ P)(A:AllocatedL P)(X:CloudsL)(D:SurfCheckL F):Small (SurfRimL F) (ShallowPortL C X) where
 bar t:= RimTimeL C R A t ∘ₗ D.TinCanL.symm.toLinearMap
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
