import GaugeFieldConstruction.CodaMars
import GaugeFieldConstruction.StyriaRel.YM.Ward.Motion
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set
open scoped Topology
variable {n:ℕ}(a:Axis)(p:Points n)(k:Fin n)(r:ℝ)
abbrev mirDirYL (k:Fin n)(a:Axis) := YM.NSF.Points.direction k a -- maybe ns
noncomputable abbrev ledgeYL (k:Fin n)(a:Axis)(r:ℝ)(p:Points n)(t:ℝ) := p+t • (r • mirDirYL k a)
abbrev α0_YL : Set ℝ:= Icc 0 1
abbrev calmYL(k:Fin n)(a:Axis)(r:ℝ)(x:Points n)(b:Fathom.Bulb): Prop:=∀ t:ℝ,t∈α0_YL → BreatherMars b k (ledgeYL k a r x t)
lemma stackLineYL (x:Points n)(a:Axis)(s:Fin n)(i:Fin n): (ledgeYL k a r x 1) k= x k+r • basis a:=by simp [ledgeYL,mirDirYL, NSF.Points.direction]
lemma derLedgeYL (t:ℝ): HasDerivAt (ledgeYL k a r p) (r • mirDirYL k a) t:=by
 have he := (ContinuousLinearMap.toSpanSingleton ℝ (r • mirDirYL k a)).hasDerivAt (x:=t)
 unfold ledgeYL; simpa using he.const_add p
lemma ledgeSureYL: Continuous (ledgeYL k a r p):=continuous_iff_continuousAt.mpr fun x=> (derLedgeYL a p k r x).continuousAt
end YM.GaugeFieldConstruction.Fathom
end
