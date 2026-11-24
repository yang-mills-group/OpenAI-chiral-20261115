import YM.SU5.FiniteGaugeData.Mist.Leda
/-! # coe once per list. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills Hike
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
namespace Leda
variable {H:Hilbert}{L:Side}{a:Axis}{σ:Type}(P:Terrace H L a)(z:1<L.val)(B T:List Axis)
variable {M:Hilbert}(F:Axis→ Willow M ℝ)
local notation "V"=> CoreH (GroupR P B)
-- use scalar projection coe without reduction problems when B unfolds by scheduleL.
abbrev compass {L:Side} (x:Carousel L): E4:= (WithLp.toLp _ fun i=>((x i).val:ℝ))
lemma comb_at (x:Carousel L)(F:Axis→ Willow (CoreH (GroupR P B)) ℝ)(p:∀ b:Axis, b∈B)(t:∀ i:Axis,F i= WindR P B z (p i)) : social (GroupR P B) (Maneu P x T)=Kodiak.combT F (compass x) T:= by induction T with
 | nil=>exact social_id
 | cons i v ih=> change social (GroupR P B) (ramble P i (x i)*_)=(F i).U _ * _; refine Eq.trans (Cot.citizen (air_Group P i (x i) B)) (congrArg₂ (·*·) ?_ ih); rw [t]; exact (unitPaid P B z (p i) (x i)).symm
-- art.Paint `combT` extended cont all.
lemma music {T:Type}[TopologicalSpace T](h:∀ i v,UniformContinuous fun x:ℝ=>(F i).U x v)(x:T→E4)(y:T→ M)(c:Continuous x)(p:Continuous y): Continuous fun t=> Kodiak.combT F (x t) B (y t):= by
 refine continuous_iff_continuousAt.mpr fun v=> Metric.tendsto_nhds.mpr fun ε e=> ?_; let g(z:T):=Kodiak.combT F (x z) B; have he:Continuous fun z=> g z (y v):= (Kodiak.comb_strong F B h (y v)).comp c
 filter_upwards [Metric.tendsto_nhds.mp (he.tendsto v) (ε/2) (by positivity),Metric.tendsto_nhds.mp (p.tendsto v) (ε/2) (by positivity)] with i a b; apply lt_of_le_of_lt (dist_triangle _ (g i (y v)) _); change dist (g i (y i)) (g i (y v))+_ < _; rw [dist_eq_norm,← map_sub,show ‖g i _‖ = ‖y i-y v‖ from Kodiak.comb_price F B _ (y i-y v), ← dist_eq_norm]; linarith only [a,b]
lemma orchestra {T:Type}[TopologicalSpace T](V':OS.Semigroup M a)(h:∀ i v,UniformContinuous fun x:ℝ=>(F i).U x v)(x:T→E4)(p:T→ ℝ≥0)(c:Continuous x)(t:Continuous p)(g:T→M)(u:Continuous g): Continuous fun i=> (V'.E (p i)*Kodiak.combT F (x i) B) (g i) := steamV V' _ p t (music B F h x g c u)
-- density.Real Beam compare
include z
lemma ensures (D:Set (Grid σ ℝ))(h:IsOpen D)(p q:Grid σ ℝ→ℂ)(c:Continuous p)(t:Continuous q)(e:∀ x:Grid σ (VistaQ L),pixels L x∈ D→p (pixels L x)=q (pixels L x)) : Set.EqOn p q D:=by
 have u:= pixel_dense (σ:=σ) z; intro x hx; suffices he:x∈ closure (Set.range (Leda.pixels (σ:=σ) L) ∩ D) from closure_minimal (Set.subset_def.mpr (by rintro x ⟨⟨y,rfl⟩,hp⟩; exact e y hp)) (isClosed_eq c t) he
 apply mem_closure_iff_nhds.mpr; intro w p; obtain ⟨v,⟨t,k⟩,p'⟩:= mem_closure_iff_nhds.mp (u x) _ (Filter.inter_mem p (h.mem_nhds hx)); exact ⟨v,t,p',k⟩
end Leda
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
