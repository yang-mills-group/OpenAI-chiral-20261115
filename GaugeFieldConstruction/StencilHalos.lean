import GaugeFieldConstruction.StencilFerro
import GaugeFieldConstruction.StencilProjection
import GaugeFieldConstruction.SoulBreadNX
import GaugeFieldConstruction.AuldΘJ
import YM.SU5.Assay.RawLag
/-!
# Frames of a single character
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Set Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
namespace Discipline
open RosterJ BoonsθJ SelectionAnalysis
open OS.Semigroup
variable (P:Spine) (i:Axis)(x:P.Spectrum0 3)
local notation "ν" => P.advocate 3 x i
local notation "H"=> P.ColorHil i ν
local notation "B"=> P.ManyF i ν
local notation "J"=> P.gnsIn i ν
local notation "C"=> P.privateH x i
local notation "V"=> P.voyageF i ν
local notation "D"=> (C).DegreeHab
local notation "S"=> P.seasons i ν
local notation "T"=> (C).BrightHab
local notation "Κ"=> (C).canopy.track
local notation "μ"=> marks (timeMesh P.par)
local notation "Π"=> projectPrice P i x
local notation "Λ_"=> passFrame P i x
local notation "d"=> P.neutralSlabs i
lemma projectTax (A: P.Slabs i)(h:A∈ d)(l r:ℝ): (Π) (HeatTaxJ P i l r A)=(S).sand ((Π) A) l r:= costHeatSt P i x A h l r
lemma shadowBox (A:P.Apron)(u v:PermWallJ P)(l:A.realWidth P i≤ StallJ P u)(r:A.realWidth P i≤ StallJ P v):
    let t:=costΞJ P i 0 A.s u v A.F; CallBoxJ 0 u v i A.F t A.s ∧ (Π) t=P.base i ν A (StallJ P u) (StallJ P v):=by
 intro t; let p:=regionHeatSt P i x A u.val v.val l r; let q:=P.grantGapNX i A.s (A.u i) A.F (StallJ P u) (StallJ P v)
 have hz: CallBoxJ 0 u v i A.F q A.s:= by unfold CallBoxJ; rw [show (0:P.VMark) i=0 from rfl,zero_sub,zero_add]; exact p.1
 rw [show t=q from ℓγHeard _ _ _ _ _ hz]; exact ⟨hz,p.2⟩
lemma shadowLevelSt (UaZ:ℕ→ P.Apron)(h₀:∀ s,(UaZ s).s=s)(a b:PermWallJ P)(h:Tendsto (fun s=> (UaZ s).realWidth P i) atTop (𝓝 0)) : ∀ᶠ s in atTop, let F:= (UaZ s).F; P.HabitLevel i F s (0-a.val) (0+b.val) (costΞJ P i 0 s a b F) s:=by
 filter_upwards [shadowStallSt P i UaZ a.val b.val a.2 b.2 (by simp_rw [h₀]; exact tendsto_id) h] with s q
 rw [h₀ s] at q
 intro F; let D':= P.grantGapNX i s ((UaZ s).u i) (UaZ s).F (StallJ P a) (StallJ P b)
 rw [show costΞJ P i 0 s a b F= D' from ℓγHeard _ _ _ _ _ (by unfold CallBoxJ; simpa only [Pi.zero_apply,zero_sub,zero_add] using (show P.Habitable i F s (-a.val) b.val D' from ⟨s,q⟩)),zero_sub,zero_add]; exact q

#print axioms shadowLevelSt
#print axioms tintShadow
#print axioms shadowBox
#print axioms frameSpace
end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
