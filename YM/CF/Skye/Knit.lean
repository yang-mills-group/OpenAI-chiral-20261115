/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Skye.Shoal
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Held
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{u d:ℝ}{r:ℕ}
lemma pill(q:Chi)(b:Bool)(d:ℝ)(x:E):group.lieExp (patched q d (polarT b x))=polarT b (group.lieExp (patched q d x)):=by
 cases b; rfl
 have hg (z:E):z∈firstChart group→ Reef.qG z∈firstChart group:=by
    rintro ⟨a,ha,rfl⟩; exact ⟨Reef.frolic a,by simpa [firstBall] using ha, Reef.cool_a _⟩
 by_cases h:x∈firstChart group; swap
 · have hu:polarT true x∉ firstChart group:=fun v=> h (Reef.q0 x ▸ hg _ v)
   rw [patched,Set.indicator_of_notMem hu,patched,Set.indicator_of_notMem h,Gauge.mat_lieExp_zero,map_one] -- tune
 obtain ⟨a,ha,rfl⟩:=h; have hv: Reef.frolic a∈firstBall group:= (by simpa [firstBall] using ha); rw [← show group.lieExp (Reef.frolic a)= _ from Reef.cool_a a]; unfold patched firstChart; rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hv), Set.indicator_of_mem (Set.mem_image_of_mem _ ha)]; rw [over_ball hv,over_ball ha,show Next.SectorChange.broad q d (Reef.frolic a)=Next.SectorChange.broad q d a from ?_,←map_smul]; exact Reef.cool_a _
 simp [Next.SectorChange.broad]
lemma hop(q:Chi)(ht:0<d)(hm:2*d < firstRadius group){W:Type*} [NormedAddCommGroup W][NormedSpace ℝ W]{f:W→E} {x:W}{k:ℕ∞}(h:ContDiffAt ℝ k (group.mat ∘ f) x): ContDiffAt ℝ k (patched q d ∘ f) x:=by
 let K:=group.continuous_mat.isClosedEmbedding group.mat_injective; have hx:ContinuousAt f x:=K.isEmbedding.isInducing.continuousAt_iff.mpr h.continuousAt; by_cases ht':f x ∈ firstChart group
 · have hs:=first_geom group; have he:ContDiffAt ℝ k (LocalH.snap group ∘ f) x:= ((hs.2.2.2.2.2.2 _ ht').of_le (m:=(k:WithTop ℕ∞)) le_top).comp x (f:=group.mat ∘ f) h -- tune
   refine ((((broad_smooth q d).of_le (m:=(k:WithTop ℕ∞)) (by exact_mod_cast (show k≤⊤ from le_top))).contDiffAt.comp x he).smul he).congr_of_eventuallyEq ?_
   filter_upwards [hx.tendsto.eventually (hs.1.mem_nhds ht')] with y hy; change f y∈firstChart group at hy; rw [Function.comp_apply,patched,Set.indicator_of_mem hy]; rfl
 let s := group.lieExp '' closedBall (0:group.Color) (2*d); have hv:IsClosed s:= ((isCompact_closedBall ..).image group.lieExp_cont).isClosed; have he:s⊆firstChart group:= Set.image_mono (closedBall_subset_ball hm)
 refine (contDiffAt_const (c:=(0:group.Color))).congr_of_eventuallyEq ?_; filter_upwards [hx.tendsto.eventually (hv.isOpen_compl.mem_nhds (show f x ∈ sᶜ from fun k=>ht' (he k)))] with y hy
 by_cases h':f y∈firstChart group; swap; rw [Function.comp_apply,patched,Set.indicator_of_notMem h']
 rw [Function.comp_apply,patched,Set.indicator_of_mem h']; have hl: Next.SectorChange.broad q d (LocalH.snap group (f y))=0:=by by_contra hh; exact hy ⟨_,mem_closedBall.mpr (by simpa using (broad_span q ht _ hh).le),under_ball h'⟩ -- tune
 rw [hl,zero_smul]
-- smooth stencil on links
abbrev knit(q:Chi)(d:ℝ)(x y: E):= group.lieExp (patched q d (x*y⁻¹))*y
lemma knitted(q:Chi)(d:ℝ)(g h x y:E):knit q d (g*x*h) (g*y*h)=g*knit q d x y*h:=by
 unfold knit; rw [show g*x*h*(g*y*h)⁻¹=g*(x*y⁻¹)*g⁻¹ from by group, patched_covary, Next.SectorChange.exp_adjoint]; group
lemma knitC (q:Chi)(d:ℝ)(b:Bool)(x y:E):knit q d (polarT b x) (polarT b y)=polarT b (knit q d x y):=by unfold knit; rw [←map_inv, ←map_mul, pill]; exact (map_mul ..).symm
lemma knitV (q:Chi)(d:ℝ)(x y:E): knit q d x⁻¹ y⁻¹=(knit q d x y)⁻¹:=by
 unfold knit; rw [inv_inv,show x⁻¹*y=y⁻¹*(x*y⁻¹)⁻¹*(y⁻¹)⁻¹ by group, patched_covary, exp_adjoint,patched_inv,exp_negative]; group
lemma knitHere (q:Chi)(d:ℝ)(x y:E)(p:0<d)(t:d<firstRadius group)(h: ∃ a:group.Color,‖a‖≤d∧ x=group.lieExp a*y): knit q d x y=x:=by obtain ⟨a,h,rfl⟩:=h; unfold knit; rw [mul_inv_cancel_right,patched_agrees _ p t h]
lemma knitD (q:Chi)(p:0<d)(t:2*d< firstRadius group){W:Type*} [NormedAddCommGroup W][NormedSpace ℝ W]{f g:W→E}{x:W}{k:ℕ∞}(h:ContDiffAt ℝ k (group.mat ∘ f) x)(hb:ContDiffAt ℝ k (group.mat ∘ g) x): ContDiffAt ℝ k (fun y=>group.mat (knit q d (f y) (g y))) x:=by
 have hx:ContDiffAt ℝ k (patched q d ∘ (fun y=> f y*(g y)⁻¹)) x:=by apply hop q p t; simp only [Function.comp_def,Gauge.mat_mul, Gauge.mat_inv]; exact h.mul ((starL' ℝ).contDiff.contDiffAt.comp x hb)
 simp only [knit,Gauge.mat_mul]; exact (((group.exp_jet.of_le (m:=(k:WithTop ℕ∞)) le_top).contDiffAt).comp x hx).mul hb
end YM.CF.Skye
