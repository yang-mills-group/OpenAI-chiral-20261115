import SU5SatinVerifiedNovember6
import ZecaShot
import ZecaWhip
import ZecaZest
set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set




open CF.Velvet CF.Pannier.Chancel
variable (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x)

local notation "Y"=> P.soldTrumpet A c r n w
local notation "Z"=>P.Honey x D F U (P.soldTrumpet A c r n w)
variable (S:P.Shell K c r x R i₀ F U A n w V g h X D)
include S
lemma framed_LocalFieldBounds :P.Honey x D F U (P.soldTrumpet A c r n w):=by
 have ep:=S.scores.incense
 have arm:=ep.2.2.2.2.2.2.2.2 w
 apply P.zecaWhip _ _ _ _ _ (P.bean ep.1 ep.2.2.2.2.2.2.1)
 · intro i
   obtain ⟨b,o,_,y⟩:=S.silver.nonzero
   have j:=o.trans (y.2 i);rw [S.silver.realW] at j
   exact norm_pos_iff.mp j
 · obtain ⟨G,_,p⟩:=S.silver.found;exact fun z=>⟨_,p z⟩
 exact arm.slender

omit S in
theorem exists_satin_sublimation :
 ∃ (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x),
    P.Shell K c r x R i₀ F U A n w V g h X D ∧
    P.Honey x D F U (P.soldTrumpet A c r n w) ∧
    P.Zest c r x F U A n w :=by
  obtain ⟨P,K,c,r,x,R,i,F,U,A,n,w,V,g,h,X,D,S⟩:=exists_disclosed_satin_fields
  exact ⟨P,K,c,r,x,R,i,F,U,A,n,w,V,g,h,X,D,S,
        framed_LocalFieldBounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S,
        zest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S⟩
#check @exists_satin_sublimation
#print axioms exists_satin_sublimation
