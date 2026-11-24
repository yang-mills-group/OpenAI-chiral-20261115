import Nankin.Cluster
import Nankin.Beige
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
variable {α:Type*}[TopologicalSpace α]{f:ℕ→ℕ}{x:ℕ→α}{a:α}(H:StrictMono f)(h:Tendsto (x∘f) atTop (𝓝 a))
noncomputable def sprayed (x:ℕ→α)(a:α)(f:ℕ→ℕ)(i:ℕ):α:=if i∈ Set.range f then x i else a
lemma sprays (i:ℕ): sprayed x a f (f i)=x (f i):=if_pos (Set.mem_range_self _)
include h H
lemma completeSpray:Tendsto (sprayed x a f) atTop (𝓝 a):=by
 rw [Filter.tendsto_def]; intro t y
 obtain ⟨i,p⟩:=Filter.eventually_atTop.mp (h.eventually y)
 refine mem_map.mpr (Filter.eventually_atTop.mpr ⟨f i,fun j e=>?_⟩)
 change sprayed x a f j∈t; unfold sprayed; split
 next u=> obtain ⟨j,rfl⟩:=u; exact p j (H.le_iff_le.mp e)
 next=> exact mem_of_mem_nhds y
end Calico
end YM.CF.Buffered.Afterglow.Tower
