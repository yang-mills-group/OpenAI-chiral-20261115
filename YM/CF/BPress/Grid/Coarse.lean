import YM.CF.BPress.Grid.Skeleton
import YM.CF.BPress.Lifts
/-! First refinement of lem:B-frames. This costs before any scale threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Lattice MeasureTheory Finset Filter SU Cube
open scoped Topology BigOperators NNReal InnerProductSpace Matrix Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

lemma group_met (x y : E) : dist x y= group.colorScale*chord x y:= by
 rw [chord.scale_mul]; exact dist_eq_norm (group.mat x) (group.mat y)
lemma frames_D : ∃ D : Delivery group 3 E, D.ship=fun x y=>x*y:=by
 let κ:ℝ≥0:=⟨group.colorScale,group.colorScale_pos.le⟩
 refine ⟨⟨fun x y=>x*y,mul_one,fun _ _ _=>mul_assoc ..,fun _ _ _=>by rw [group_met,group_met,chord.right],κ,?_,continuous_fst.mul continuous_snd,?_⟩,rfl⟩
 · intro f x y; rw [group_met,chord.left]; rfl
 intro K; have d : dimH (rim 3) < 3:= lt_of_le_of_lt (rim_price 2) (by norm_num); obtain ⟨C,P⟩:= Smooth.su_extension (table_compact 3) (rim_compact 3) Set.inter_subset_left d 4 K
 have e (x y : E) : dist (SU.fund x) (SU.fund y)=dist x y:= rfl
 refine ⟨C, fun s l f h=>?_⟩; obtain ⟨g,t,v,q⟩:= P s l (fun i=> fund (f i)) (LipschitzOnWith.of_dist_le_mul (fun x hx y hy=> by rw [e]; exact h.dist_le_mul x hx y hy)) (fun x _=> (show Mesa.trueS _ from ⟨SU.fund_U _, SU.fund_det _⟩));
 let T (i : Desk 3): E:= if p:i∈table _ then (⟨⟨g i,(show Mesa.trueS _ from v p).1⟩,(show Mesa.trueS _ from v p).2⟩ : E) else 1
 have ht (x) (hx:x∈table 3): fund (T x)=g x:=by unfold T; rw [dif_pos hx]; rfl
 refine ⟨T, LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>?_ ), fun i h=> group.mat_injective ((q h).trans (ht _ (Set.inter_subset_left (l h))).symm)⟩
 rw [← e, ht _ hx, ht _ hy]; exact t.dist_le_mul x hx y hy
-- need explicit Delivery with ship = mult
variable {G : Gauge}{s:Side}{d:ℕ}{m:ℝ}
def pad (r : ℕ) (W : GaugeField G d s) : GaugeField G d s := fun i=> line W i.1 i.2 r
def arcFee (r : ℕ)(W : GaugeField G d s)(F:Fabric d s G.El)(L:ℝ):Prop:= ∀ x∈mesh r,∀ i:Fin d, chord (F x*line W x i r) (F (hop x i r)) ≤ L
lemma pad_meas (s:Side) (r d:ℕ)(G:Gauge) : Measurable (pad (G:=G) (s:=s) (d:=d) r):= measurable_pi_lambda _ fun i=> (line_cont i.1 i.2 r).measurable
-- local dependency of a refinement (for two stride inputs even without Speed).
def NearRead {X : Type}{d:ℕ}{s:Side}(r:ℕ)(v w:Fabric d s X)(L:ℕ)(o: Space d s):Prop:=∀ x∈mesh r, delta o x ≤ L → v x=w x
def NearLine {d:ℕ}{s:Side}{G:Gauge}(r:ℕ)(U V:GaugeField G d s)(L:ℕ)(o: Space d s):Prop:=∀ i: WalkEdge d s,i.1∈mesh r→ delta o i.1 ≤ L → pad r U i=pad r V i
private def prep (r:ℕ) (x:Fabric d s G.El)(i: Space d s): G.El:=if i∈mesh r then x i else 1
structure Only (r R S:ℕ)(g: GaugeField G d s × Fabric d s G.El→ Fabric d s G.El): Prop where
  see (x y) (o:Space d s) (h:o∈mesh r): NearLine r x.1 y.1 S o → NearRead R x.2 y.2 S o → g x o=g y o
  leave (x o) : o∈mesh R → g x o=x.2 o
  borel : Measurable g
-- leave actually only valid on Flat -- step Reach formula includes condition. can force globally reset on coarse grid. later dyad ok.
open Entity Delivery
theorem begin_B : ∃ C : ℝ, 0 < C ∧ ∀ (s:Side)(k:Tiling s), ∃ T, Only k.r.val k.R (6*k.R) T ∧
    ∀ (m:ℝ)(U : GaugeField group 3 s) (F : Fabric 3 s E), Flat U m → (k.R:ℝ)^2*m ≤ 1 → arcFee k.r.val U (T (U,F)) (C/k.b.val) := by
 -- choose Delivery via stronger frames_D
 obtain ⟨D,hD⟩:= frames_D
 letI : @CompactSpace E MetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace:= (inferInstance : CompactSpace E)
 letI : @BorelSpace E MetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _:= (inferInstance : BorelSpace E)
 obtain ⟨C,h,H⟩:=D.build 0 le_rfl
 refine ⟨C/group.colorScale+1,by have ht:=group.colorScale_pos; positivity,fun s k=>?_⟩; obtain ⟨T,p,t,Q⟩:= H s k
 let L:= k.R; let F:=fun x : GaugeField group 3 s × Fabric 3 s group.El=> (pad k.r.val x.1, prep k.R x.2); let w:=T univ ∅ ∘ F
 let g:=fun x : GaugeField group 3 s × Fabric 3 s group.El=> fun i=> if i∈mesh k.R then x.2 i else w x i
 have two : 3*(2*k.R)=6*k.R:=by omega
 refine ⟨g,⟨fun x y o e l Z=> ?_,fun x o h=> by simp only [g,h,↓reduceIte],?_⟩, fun m U x p' b=>?_ ⟩
 · by_cases t:o∈mesh k.R; · unfold g; rw [if_pos t,if_pos t]; exact Z o t (by simp)
   unfold g; rw [if_neg t,if_neg t]; apply Q univ ∅ univ ∅ _ _ o e (by simp); intro i p q; exact l _ p (q.trans two.le)
   intro i s u; change prep k.R x.2 i=prep k.R y.2 i; unfold prep; split; next g=> exact Z _ g (u.trans two.le)
   next g=> rfl
 · have hi: Measurable w:= (t univ ∅).comp (Measurable.prodMk ((pad_meas s k.r.val 3 group).comp measurable_fst) (measurable_pi_lambda _ ?_)); swap; · intro i; unfold prep; split; exact (measurable_pi_apply _).comp measurable_snd; exact measurable_const
   apply measurable_pi_lambda; intro i; unfold g; split; exact (measurable_pi_apply i).comp measurable_snd; exact (measurable_pi_apply i).comp hi
 obtain ⟨Y,A',V⟩:=p univ ∅ (by simp [Graded]) (by simp [Graded]) (by simp) (pad _ U) (prep k.R x) (by
   intro i _ a l u v w x y t; apply le_trans (i.flat_of_stride _ U p' rfl a l u v w x y t); have ht : 0 < (k.b.val:ℝ):=by positivity
   unfold Tiling.R at b; push_cast at b; rw [← one_div]; apply (le_div_iff₀ (by positivity)).mpr; nlinarith only [b]) (by simp)
 have v(i): g (U,x) i=w (U,x) i:=by
    unfold g; split; next h=> exact Eq.symm ((V i h).trans (if_pos h))
    next h=> rfl
 intro i e j; obtain ⟨I,a,f,T⟩:=mesh_coord k e -- tune
 rw [←f]; have ht:= Y I (mem_univ _) (by simpa using card_le_univ I.axes) a j (T j).1; unfold speed along at ht; rw [I.step_eq,hD] at ht; dsimp only at ht; rw [group_met] at ht; rw [v,v]; refine le_trans (b:=C/ group.colorScale/k.b.val) ?_ ?_; swap
 · apply div_le_div_of_nonneg_right (by linarith) (by positivity)
 apply le_trans (b:=C/k.b.val/group.colorScale) _ (Eq.le (by ring)); apply (le_div_iff₀ group.colorScale_pos).mpr; rw [mul_comm]; exact ht
end YM.CF.BPress.Grid
