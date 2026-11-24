import YM.CF.BProof.Grid.Walk

/-! Cuboid rotation hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Entity
open Lattice Function Set Finset Cube
open scoped Topology BigOperators NNReal
variable {n : ℕ} {c s : Side} (g : Ratio c s) (p : Entity n c)

/- partial face order. -/
inductive Under : Entity n c→Entity n c→Prop
 | refl (p : Entity n c) : Under p p
 | wall {p q : Entity n c} {i} (u:i∈q.axes) (b: Bool) (h:Under p (q.wall i b)): Under p q
lemma Under.trans {p q r:Entity n c}(h:Under p q)(u:Under q r):Under p r:=by induction u with | refl=>exact h|wall i b d ih=> exact .wall i b ih
lemma Under.rank {p q:Entity n c}(h:Under p q):p.dim ≤ q.dim:=by induction h with| refl=>rfl| @wall q i x b d ih=> have := q.wall_dim x b; omega
lemma Under.sites {p q:Entity n c}(h:Under p q)(hc:4≤ c.val){x}(d:p.Mem g x): q.Mem g x:=by induction h with|refl=>exact d|wall i b u ih=> exact ((mem_wall _ g hc x i b).mp ih).1

lemma chief_sub (hc:4≤ c.val)(x : Cubic n s)(h:p.Mem g x):Under (chief g x) p:= by
 suffices he : ∀ k (p:Entity n c),p.dim=k → p.Mem g x→ Under (chief g x) p from he _ _ rfl h
 intro k; induction k using Nat.strong_induction_on with
 | _ k ih=>
  intro p hp h; by_cases v:p.Proper g x; rw [p.chosen g x v]; exact .refl _
  obtain ⟨i,h,u,v⟩:=p.smaller g hc h v; exact .wall h u (ih _ ((p.wall_dim h u).trans hp |>.le) _ rfl v)

-- set parameters with pinned walls
lemma mem_exchange (hc:4≤c.val) (x y:Cubic n s) (hx:p.Mem g x)(hy:p.Mem g y)(i:Fin n) : p.Mem g (update x i (y i)):=by
 intro j; by_cases h:j=i; subst j; rw [coord,update_self]; exact hy i; rw [coord,update_of_ne h]; exact hx j
lemma near_exchange (x y:Cubic n s)(i:Fin n) : dist x (update x i (y i)) ≤ dist x y ∧ dist y (update x i (y i)) ≤ dist x y:= by
 constructor <;> apply dist_le.mpr <;> intro j
 · by_cases h:j=i; subst j; rw [update_self]; exact dist_axis ..; rw [update_of_ne h,d_id]; omega
 by_cases h:j=i; subst j; rw [update_self,d_id]; omega; rw [update_of_ne h,d_sym]; exact dist_axis ..

lemma commonPoint (hc:4≤c.val) {i j:Fin n}(v:i∈p.axes)(w:j∈p.axes){a b:Bool}(q:i≠j)(x y:Cubic n s)
    (hx:(p.wall i a).Mem g x) (hy:(p.wall j b).Mem g y) :
    ∃ z,(p.wall i a).Mem g z ∧ (p.wall j b).Mem g z ∧ dist x z ≤ dist x y ∧ dist y z≤ dist x y := by
 obtain ⟨hx,gx⟩:= (p.mem_wall g hc x v a).mp hx; obtain ⟨hy,gy⟩:= (p.mem_wall g hc y w b).mp hy
 let z:=update x j (y j); have hh : p.Mem g z:= p.mem_exchange g hc x y hx hy _
 refine ⟨z, (p.mem_wall g hc z v _).mpr ⟨hh,?_⟩, (p.mem_wall g hc z w _).mpr ⟨hh,?_⟩,near_exchange x y j⟩
 · rw [coord_update,update_of_ne q,gx];
 rw [coord_update,update_self]; exact gy
lemma tall (hc:4≤c.val){i:Fin n}(h:i∈p.axes)(x y:Cubic n s)(hx:(p.wall i true).Mem g x)(hy:(p.wall i false).Mem g y): g.count.val ≤ dist x y:=by
 obtain ⟨hx,u⟩:= (p.mem_wall g hc x h true).mp hx; obtain ⟨hy,v⟩:= (p.mem_wall g hc y h false).mp hy; apply le_trans (b:= delta1 s _ _) _ (dist_axis x y i); rw [p.local_distance g hx hy hc,u,v,len,if_pos h]; simp

-- unit embeddings. norm sup.
def chart (p:Entity n c)(x : Cubic n s) : Fin n→ℝ := fun i=> p.coord g x i/(g.count.val:ℝ)
lemma fee (hc:4≤c.val){x y}(hx:p.Mem g x)(hy:p.Mem g y)(i:Fin n): ‖p.chart g x i-p.chart g y i‖=(delta1 s (x i) (y i):ℝ)/(g.count.val:ℝ):=by
 have hp:0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
 rw [p.local_distance g hx hy hc, Real.norm_eq_abs,chart,chart,←sub_div,abs_div,abs_of_pos hp]
 rw [Nat.cast_sub (min_le_max), Nat.cast_max, Nat.cast_min, max_sub_min_eq_abs,abs_sub_comm] -- tune
lemma cost (hc:4≤ c.val){x y}(hx:p.Mem g x)(hy:p.Mem g y): Dist.dist (p.chart g x) (p.chart g y)=(dist x y:ℝ)/(g.count.val : ℝ):=by
 have hp:0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
 rw [dist_eq_norm]; apply le_antisymm
 · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; rw [Pi.sub_apply, p.fee g hc hx hy]; gcongr; exact dist_axis .. -- tune
 by_cases h:0<n
 · obtain ⟨i,-,hv⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) (f:=fun i=> delta1 s (x i) (y i)) (by haveI:Nonempty (Fin n):=⟨⟨0,h⟩⟩; exact univ_nonempty) -- tune
   rw [show Grid.dist x y= _ from hv,← p.fee g hc hx hy i]; exact norm_le_pi_norm (p.chart g x-p.chart g y) i
 rw [show dist x y=0 from Nat.eq_zero_of_le_zero (dist_le.mpr fun i=>by have:=i.isLt; omega)]; simp
lemma positions {x:Cubic n s}(hx:p.Mem g x): p.chart g x∈ Metric.closedBall 0 1:=by
 rw [Metric.mem_closedBall,dist_zero_right]; have hp: 0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
 apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; unfold chart; rw [Real.norm_of_nonneg (by positivity),div_le_one hp]; exact_mod_cast (hx i).trans (p.width g i)
lemma unique (hc:4≤c.val){x y}(hx:p.Mem g x)(hy:p.Mem g y)(he:p.chart g x=p.chart g y):x=y:=by
 have hu := cost g p hc hx hy; rw [he,_root_.dist_self] at hu; have hp:0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
 apply dist_zero; rw [eq_comm, div_eq_zero_iff,or_iff_left hp.ne',Nat.cast_eq_zero] at hu; exact hu

-- any edge in a cube. choose from left endpoint, may have to cross pos axis wall.
theorem entire (hc :4≤c.val)(x : Cubic n s)(i:Fin n) : ∃ v:Cubic n c, (mk v univ).Mem g x ∧ (mk v univ).Mem g (slide x i) := by
 let p:= mk (elder g x) Finset.univ; have he (i) : p.len g i=g.count.val:=by simp [len,p]
 have ht (i) : p.coord g x i < p.len g i := he i ▸ ((mem_tile ..).mp ((block_eq g (x i) _).mp rfl))
 exact ⟨_,fun i=> (ht i).le,(p.stepMem g i hc (fun i=> (ht i).le)).mpr (ht i)⟩
end YM.CF.BProof.Grid.Entity
