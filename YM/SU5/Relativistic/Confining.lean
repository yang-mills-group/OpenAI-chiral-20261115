import YM.SU5.Relativistic.NeedlePacket
import YM.SU5.Relativistic.ExpandAverage
/-!
# Unprojected error when hold at a point
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Set Function Filter Metric
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace

variable {I:Type*}[Fintype I]{M:Mesh}
variable (v:I→Axis→Stamp M) (G:(I→Axis→ Stamp M)→ ℂ)
local notation "A" n:max=> (Axis→ Fin (M.L^n))
noncomputable def waveSpot (k t:ℕ)(x:I→ Axis→ Fin (M.L^t)) : I→ Axis→ Stamp M:=fun i=> (nub M (v i) k).near t (x i)
def apk (k t:ℕ): ℂ:= algMean (fun x:I→ Axis→ Fin (M.L^t)=> G (waveSpot v k t x))
lemma spot_warp (ε:ℝ)(p:0<ε): ∀ᶠ k in atTop,∀ t:ℕ,∀ x:I→ Axis→ Fin (M.L^t), dist (waveSpot v k t x) v < ε:= by
 have hh(i:I): ∀ᶠ n in atTop, ∀ x∈UBox Axis,dist ((nub M (v i) n).region x) (fun j=> (v i j:ℝ)) < ε/2 := (adjusts_mesh (M:=M) (v i)).1 (ε/2) (half_pos p)
 filter_upwards [eventually_all.mpr hh] with i k t x; refine lt_of_le_of_lt ?_ (half_lt_self p)
 apply (dist_pi_le_iff (half_pos p).le).mpr; intro a
 have ht:= (k a _ (Packet.lives (M:=M) t (x a))).le; rw [← funext ((nub M (v a) i).points_near t (x a))] at ht
 rw [dist_pi_le_iff (half_pos p).le] at ht ⊢; exact fun i=> ht i
lemma near_cost (p:ContinuousAt G v)(ε:ℝ)(h:0<ε):∀ᶠ k in atTop,∀ t:ℕ, dist (apk v G k t) (G v) < ε:=by
 obtain ⟨δ,e,v'⟩:= Metric.continuousAt_iff.mp p (ε/2) (half_pos h)
 filter_upwards [spot_warp v δ e] with i g t; refine lt_of_le_of_lt ?_ (half_lt_self h)
 haveI:=avg_lives M t
 have hx:= Average.norm_dist (f:= fun x:I→ Axis→ Fin (M.L^t)=> G (waveSpot v i t x)) fun x=> (v' (g t x)).le -- annotate g
 rw [Average.constant («A»:=I→ Axis→ Fin (M.L^t))] at hx; exact hx
lemma materializes (p:ContinuousAt G v) (D:ℕ→ℂ)(g:∀ᶠ k in atTop,Tendsto (fun x:ℕ=> apk v G k (x-k)) atTop (𝓝 (D k))):
    Tendsto D atTop (𝓝 (G v)):=by
 apply Metric.tendsto_nhds.mpr
 intro ε h; filter_upwards [near_cost v G p (ε/2) (half_pos h),g] with i hx hi
 refine (le_of_tendsto (hi.dist tendsto_const_nhds) ?_).trans_lt (half_lt_self h); exact Eventually.of_forall fun j=> (hx (j-i)).le
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.materializes
