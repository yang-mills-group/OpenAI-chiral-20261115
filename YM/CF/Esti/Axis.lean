/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Esti.Vie
import YM.CF.Vol.Wage
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arcus
/-! Prices for paths in Vol with all orientation and lift tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Esti
open CF.Jet
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push  Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G:Gauge}{A:Type}[NormedAddCommGroup A][NormedSpace ℝ A]
private def opPrice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
private lemma opPrice_nn {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : 0 ≤ opPrice L := norm_nonneg L

lemma adjointQ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → G.El} {w : E → G.Color} {x : E} {M C : ℝ} {n : ℕ}
    (hU : Allows n (fun z => G.mat (U z)) x M) (hw : Allows n w x C) :
    Allows n (fun z => G.adjoint (U z) (w z)) x
      (G.colorScale⁻¹*(2^n*(2^n*M*(G.colorScale*C))*M)) := by
  let L := G.projectColor.toContinuousLinearMap
  have hL : opPrice (E:=G.Mat) (F:=G.Color) L ≤ G.colorScale⁻¹ := by
    refine L.opNorm_le_bound (inv_nonneg.mpr G.colorScale_pos.le) fun u => ?_
    rw [mul_comm,← div_eq_mul_inv]; exact G.project_norm u
  let J := G.colorMat.toContinuousLinearMap
  have hJ : opPrice (E:=G.Color) (F:=G.Mat) J ≤ G.colorScale := J.opNorm_le_bound G.colorScale_pos.le (fun v => (G.colorMat_norm v).le)
  have hb {X Y : E → G.Mat} {A B : ℝ} (h : Allows n X x A) (hp : Allows n Y x B) :
      Allows n (fun z => X z * Y z) x (2^n*A*B) := by
    simpa only [mul_one,ContinuousLinearMap.mul_apply'] using h.bilinear _ hp
      (ContinuousLinearMap.opNorm_mul_le ℝ G.Mat)
  have hh := (hb (hb hU (hw.linear J hJ)) (gran hU)).linear L hL
  exact hh


lemma arc_b{U:A→G.Mat}{x:A}{n:ℕ}{M:ℝ}(h:Allows n U x M):Allows n (curvatureL G ∘ U) x (curvatureCost G*M):= h.linear (curvatureL G) le_rfl
end YM.CF.Esti
