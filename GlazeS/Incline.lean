import GlazeS.Locations
import GlazeS.CastLight
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(T:RobeRoad P F C D x)
local notation "H"=> P.ColorHil 3 x
local notation "W"=> P.ManyF 3 x
local notation "U"=>P.cartage 3 x
local notation "β"=> P.wealth 3 x
local notation "A₀"=> (P.physicalEnergy 3 x).E
noncomputable def crest (P:Spine)(F:ℕ):Vantage:=fun _=> measured P F 1
noncomputable def plays (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(A:SampleDose)(s j:ℕ)(q:Vantage):P.ManyF 3 x:=
 ((A.val q:ℂ)) • P.cartage 3 x (q - crest P F) (P.wealth 3 x (outingP P F C D x (q 3) s j))
-- no clock assertion on transverse.S.CHeat. W projection.
lemma end_cont (A:SampleDose)(s j:ℕ): Continuous (plays P F C D x A s j):=by
 let f(q:Vantage):=outingP P F C D x (q 3) s j
 let z(q:Vantage):= P.wealth 3 x (f q)
 have hv:Continuous z:= (P.wealth 3 x).continuous.comp (((P.physicalEnergy 3 x).continuousE _).comp (continuous_real_toNNReal.comp ((continuous_apply _).sub continuous_const)))
 exact (Complex.continuous_ofReal.comp A.smooth.continuous).smul (P.caravan 3 x (fun i:Vantage=>i - crest P F) z ((show Continuous (id (α:=Vantage)) from continuous_id).sub continuous_const) hv)

-- Transposes compressed.Borrow reindex.Top compactness. Need invariant under time-coordinate spatially.
lemma move_eq {q p:Vantage}(e:∀ i,i ≠ (3:Axis)→p i=q i): P.cartage 3 x p=P.cartage 3 x q:= by
 unfold cartage; congr 1; exact funext fun i=>e i.val i.property
lemma abodeT (s:ℕ)(v:F ≤ s)(q:Vantage):P.cartage 3 x (q - central P F s)=P.cartage 3 x (q-crest P F):=by
 apply move_eq; intro i h; simp only [Pi.sub_apply]; rw [centerSpace P F s v h]; rfl
-- translated trajectories absolute. use argument reindex.Here X potentially other.
lemma reserve_here(s:ℕ)(v:F ≤ s)(A:SampleDose):
   let g:=recoup P F C D x s s
   (∫ p:Vantage, U p (β (((dealt A (central P F s)).val p:ℂ) • A₀ ((p 3).toNNReal) g)))=∫ q:Vantage, plays P F C D x A s s q:=by
 intro g
 rw [←integral_add_right_eq_self (plays P F C D x A s s) (central P F s)]
 apply integral_congr_ae; filter_upwards with p
 unfold plays; rw [map_smul,map_smul]; apply congrArg _ -- determine transport
 rw [←abodeT P F x s v, add_sub_cancel_right, outingP,Pi.add_apply, center3, add_sub_cancel_right]
-- to compile
#check integral_add_right_eq_self
#print axioms end_cont
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
