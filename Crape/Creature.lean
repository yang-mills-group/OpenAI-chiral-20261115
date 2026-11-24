import Crape.Arsenal
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
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(Y:RobeRoad P F C D x)
local notation "Lx"=>P.par.R.L
local notation "ω"=>P.ColorHil 3 x
local notation "e"=> (P.physicalEnergy 3 x).E
noncomputable def outingP (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(t:ℝ)(s j:ℕ):P.ColorHil 3 x:=
 (P.physicalEnergy 3 x).E (t-tidal P F j).toNNReal (recoup P F C D x s j)
lemma bless_r {s j i:ℕ}{t:ℝ}(a:F ≤ j)(b:F ≤ i)(p:j ≤ s)(v:i ≤ s)(c:tidal P F i ≤ tidal P F j)(k:tidal P F j≤t):
    outingP P F C D x t s i= outingP P F C D x t s j :=by
 have h:= align_s P F C D x a b v p c
 let Q:=P.physicalEnergy 3 x; let k1:ℝ≥0:=(t-tidal P F j).toNNReal; let k2:ℝ≥0:=⟨tidal P F j-tidal P F i, sub_nonneg.mpr c⟩
 unfold outingP; rw [h,show (t-tidal P F i).toNNReal=k1+k2 from (by ext1; rw [Real.coe_toNNReal _ (sub_nonneg.mpr (c.trans k)),NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr k)]; change _=_+(tidal P F j-tidal P F i); ring), Q.time]; rfl -- Q time notation.Y

include Y p
lemma runBorn {j:ℕ}(q:F ≤ j) (t:ℝ)(u:tidal P F j<t) :∃ y:P.ColorHil 3 x,
 (Tendsto (fun k=>outingP P F C D x t k j) atTop (𝓝 y)) ∧ Tendsto (fun k=>outingP P F C D x t k k) atTop (𝓝 y):=by
 obtain ⟨y,k⟩:= cauchySeq_tendsto_of_complete (advances P F C D x M p Y q)
 have hZ: Tendsto (fun i=> outingP P F C D x t i j) atTop (𝓝 (e (t-tidal P F j).toNNReal y)):= (e _).continuous.continuousAt.tendsto.comp k
 refine ⟨_,hZ,hZ.congr' ?_⟩
 filter_upwards [eventually_ge_atTop j,(recessVanish P F).eventually (ge_mem_nhds (tide_price P F j))] with i y h -- le_mem_nhds likely greater; want g ≤ r => ge_mem_nhds
 exact (bless_r P F C D x (j:=j) (i:=i) q (q.trans y) y le_rfl h u.le).symm
set_option linter.unusedVariables false in
theorem habit(t:ℝ)(a:0<t):∃ y:P.ColorHil 3 x,
 Tendsto (fun k=>outingP P F C D x t k k) atTop (𝓝 y):=by
 obtain ⟨j,v,q⟩:= (((recessVanish P F).eventually (gt_mem_nhds a)).and (eventually_ge_atTop F)).exists
 obtain ⟨y,_,J⟩:= runBorn P F C D x M p Y q t v; exact ⟨_,J⟩
-- semigroup for selected limits at arbitrary t>0 directly proves analytic in t. projection to S also. independent field smears via H only.

#print axioms habit
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
