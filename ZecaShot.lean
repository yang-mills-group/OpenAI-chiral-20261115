import ZecaFroth
import ZecaQuorum
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000



variable (w:ℕ) (f:Fin w→Lead.Clan)
 (D:Cellz (Fin w)→Gaia) (V:Fin w→DirSpin)
variable (r:ℕ→ℕ)

lemma range_frame {m:Side} (A:Twah)(g:Lead.Clan)(R:ℕ) (h:A.traceV=[]) (x:Fields m) :
 A.groundWord R g m x=A.groundWord R g m (1,1):=by
  simp only [groundWord, coil,laps, h]
  rfl

lemma home_range {m:Side}
 (h:∀i:Fin w,D (i,false)=D (i,true)) (n:ℕ)(x:Fields m) :
  plait (homeT w D V r n) f (Twah.letters w) (r n) m x=
  plait (homeT w D V r n) f (Twah.letters w) (r n) m (1,1):=by
  generalize Twah.letters w=ℓ
  induction ℓ with
  | nil => rfl
  | cons a ℓ ih =>
    let F:=homeT w D V r n
    change (F a).groundWord (r n) (f a) m x * _ = (F a).groundWord (r n) (f a) m (1,1)*_
    have hv:(F a).traceV=[]:=by
       change Lattice.route (nodeC (discrete (r n) (D (a,false)))) (nodeC (discrete (r n) (D (a,true)))) _ =_
       rw [h,route_same]
    rw [range_frame _ _ _ hv]; exact congrArg (_ * ·) ih

lemma kettle_range (v:StrictMono r)
 (h:∀i:Fin w,D (i,false)=D (i,true)):
 ∀ᶠ n in atTop,∀m (x:Fields m),(kettle w f D V r n).craft m x=
                 (kettle w f D V r n).craft m (1,1) :=by
 filter_upwards [Twah.cottage r D v V,eventually_ge_atTop w] with n y t
 unfold kettle
 rw [dif_pos (show w ≤ n ∧ Outfit n (r n) (homeT w D V r n) from ⟨t,y⟩)]
 exact fun m=> home_range w f D V r h n
#print axioms kettle_range
