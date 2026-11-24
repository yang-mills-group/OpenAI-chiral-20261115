import YM.SU5.Reconstruction.GiftWrap.WholeFire
import YM.SU5.Reconstruction.UVPrice.Void
import YM.SU5.Reconstruction.Vermont.Playlist
import Mathlib.Analysis.Complex.Liouville
/-! # Gram-sector reasoning yields irreducible WORLD algebra if bought global capacity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Bouy
open Function Set Filter MeasureTheory Metric OS.Semigroup Boundary Picket Ravin BridgeClub Anvil Roy ConePrice Sail Ship Waltz Lens ContinuousLinearMap
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder
-- Prove extension of heat access from ALL real accesses
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a) (N:Submodule ℂ H)
local notation "U"=> trans S
lemma heat_iff (q:IsClosed (N:Set H))(x:H)(t:ℝ≥0)(d:∀ t:ℝ,U (t•basis a) x∈ N) : S.E t x∈ N:=by
 letI:= q.completeSpace_coe; let P:= N.orthogonal; -- prove via orth hB
 rw [← show Nᗮᗮ=N from Submodule.orthogonal_orthogonal _]
 -- tune rewrite affects d P?
 intro p h
 let F(z:ℂ):= inner ℂ p (phase S z x)
 have he : EqOn F 0 (Complex.re ⁻¹' Ici 0):= by
    refine joinRoof F (continuous_const.inner (phase_cont S _ _ continuous_const continuous_id)).continuousOn (fun z v=> (((innerSL ℂ p).comp (ContinuousLinearMap.apply ℂ H.space x)).analyticAt _).comp (phase_ana S z v)) 0 1 zero_lt_one ?_
    intro y v; unfold F; rw[show (y:ℂ)*Complex.I= sideways (-y) from (by simp [sideways]),width_imaginary,← trans_time]; exact Submodule.inner_left_of_mem_orthogonal (d _) h
 have ep:=he (show (↑(t:ℝ):ℂ)∈ Complex.re ⁻¹' Ici 0 from t.property); change F _=0 at ep; unfold F at ep; rw [width_real,Real.toNNReal_coe] at ep; exact ep
variable (Ω:H)(M:Net H)
variable (hL:∀ x:E4, trans S x Ω=Ω)(hT:∀ x:E4,∀ A∈M,parcelUp S x A∈M)
local notation "X" => parish M Ω
include hL hT
lemma fidel {Z:Set H.Op}(t:Z⊆ (M:Set H.Op)){A:H.Op}{r c:ℝ≥0}(k:Script S Z A r c) : MapsTo A (parish M Ω) (parish M Ω):=by
 induction k with
 | weather s=> exact fun x h=> heat_iff S X (Submodule.isClosed_topologicalClosure _) x s (fun t=> globalWalk S Ω M hL hT _ x h)
 | now V r p e=> exact loyal Ω M V (t p)
 | link _ _ i h=> exact fun x p=> (X |> fun _=> i (h p))
 | plus _ _ i h=> exact fun x p=> (X).add_mem (i p) (h p)
 | scale _ e i=> exact fun x p=> (X).smul_mem e (i p)
 | charge _ _ i=> exact i
lemma thermallyPaid {Z:Set H.Op}(t:Z⊆ (M:Set H.Op)){A:ℕ→H.Op}{r c:ℝ≥0}{x:H}(k: ∀ i,Script S Z (A i) r c)(h:∀ y:H,Tendsto (fun i=>inner ℂ y (A i Ω)) atTop (𝓝 (inner ℂ y x))) : x∈ X:=by
 letI:(CompleteSpace ↑(parish M Ω)) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe; rw [←show Xᗮᗮ=X from Submodule.orthogonal_orthogonal _]; intro p e; exact tendsto_nhds_unique_of_eventuallyEq (h p) tendsto_const_nhds (Eventually.of_forall fun i=> Submodule.inner_left_of_mem_orthogonal (fidel S Ω M hL hT t (k i) (hub Ω M)) e)
end YM.Quartz.Bouy
