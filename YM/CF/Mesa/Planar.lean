import YM.CF.Mesa.Grid
import YM.CF.Mesa.Value
/-! Scaled patch coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side}
def angles (a:Index m) : Fin (degree m a) ≃ (os m a):= (Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; rfl))
def skull (a:Index m)(x:Site (Domain m B)) : Board (degree m a) := fun i=> ((offs a x (angles a i):ℤ):ℝ)/(B.val:ℝ)
def stoneX (B:Side)(d:ℕ):= {x:Board d | ∀ i, ∃ z:ℤ, z.natAbs≤B.val∧ x i=z/(B.val:ℝ)}
lemma skull_stone {a x}(h:x∈room m B a): skull a x∈ stoneX B (degree m a):=fun i=>⟨_,(off_cap h (angles a i)).trans (broad_le ..),rfl⟩
lemma skull_ter {a x}(h:x∈room m B a): skull a x∈ terrace _ := by
  have hp:0<(B.val:ℝ):=by positivity
  rw [mem_closedBall,dist_pi_le_iff zero_le_one]; intro i; obtain ⟨z,hz,hx⟩:= skull_stone h i; rw [hx]
  simp only [Real.dist_eq, Pi.zero_apply,sub_zero,abs_div,abs_of_nonneg hp.le,← Int.cast_abs]
  apply (div_le_iff₀ hp).mpr; rw [one_mul]
  exact_mod_cast (show |z|≤(B.val:ℤ) by rw [← Int.natCast_natAbs]; omega)
lemma skull_rim {a x}(h:x∈room m B a): Rim a x ↔ skull a x∈Peri _:=by
  have hp:0<(B.val:ℝ):=by positivity
  rw [rim_eq h]; constructor
  · rintro ⟨i,hi,he⟩; obtain ⟨j,hj⟩:= (angles a).surjective ⟨i,hi⟩; apply le_antisymm (show _ from skull_ter h)
    calc
      1= dist (skull a x j) ((0:Board (degree m a)) j) := by
        simp only [Real.dist_eq,skull,hj, Pi.zero_apply,sub_zero, abs_div,abs_of_nonneg hp.le, ← Int.cast_abs]; rw [show |offs a x i|=(B.val:ℤ) by rw [← Int.natCast_natAbs,he]]; push_cast; rw [div_self hp.ne']
      _ ≤ _:=dist_le_pi_dist _ _ _
  intro hx; by_contra! hh; exfalso
  apply (show dist (skull a x) 0 = 1 from hx).not_lt; rw [dist_pi_lt_iff zero_lt_one]; intro j
  let i := (angles a j).val; let z:=offs a x i; have he:=hh i (angles a j).property; have hk:= (off_cap h i).trans (broad_le ..)
  change dist (↑z/(B.val:ℝ)) 0<1; rw [Real.dist_eq,sub_zero,abs_div,abs_of_nonneg hp.le,div_lt_iff₀ hp,one_mul,←Int.cast_abs]; exact_mod_cast (show |z|<(B.val:ℤ) by unfold z; rw [← Int.natCast_natAbs]; omega)
lemma stone_reaches (a:Index m){v}(h:v∈ stoneX B (degree m a))(hm:2≤m.val): ∃ x:Site (Domain m B),x∈room m B a∧ skull a x=v:=by
  choose z hz q using h
  let Z:Cover:=fun i=> if hi:i∈os m a then z ((angles a).symm ⟨i,hi⟩) else 0
  have he (i:Axis): (Z i).natAbs≤broadface m B (a i):=by
    unfold Z; split
    next h => rw [broadface,if_pos (Finset.mem_filter.mp h|>.2)]; apply hz
    simp
  let x:=address m B a+wrap _ Z
  have hh:offs a x=Z:=by unfold offs x; rw [add_sub_cancel_left]; apply lift_s _ hm; intro i; have hx:=(he i).trans (broad_le ..); omega
  refine ⟨x,off_done (hh.symm ▸ he),?_⟩; funext i; simp [skull,hh,Z,← q]
lemma skull_dist {a x y} (h:x∈ room m B a)(g:y∈room m B a)(hm:2≤m.val) : dist (skull a x) (skull a y)= (separation x y:ℝ)/(B.val:ℝ) :=by
  let r:=dist (skull a x) (skull a y); have hp:0<(B.val:ℝ):=by positivity
  have hq (j:Fin (degree m a)): dist (skull a x j) (skull a y j)=((lift (x-y) (angles a j)).natAbs:ℝ)/(B.val:ℝ) :=by
    rw [off_lift h g hm]; unfold skull; rw [Real.dist_eq,←sub_div, abs_div,abs_of_nonneg hp.le,Pi.sub_apply,← Int.cast_sub,← Int.cast_abs, ← Int.natCast_natAbs]; simp only [Int.cast_natCast]
  apply le_antisymm
  · rw [dist_pi_le_iff (by positivity)]; intro j; rw [hq]; gcongr; exact component_le ..
  rw [div_le_iff₀ hp]; unfold separation pdist; -- sup cast
  by_cases e:Nonempty Axis
  · obtain ⟨i,-,hi⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) Finset.univ_nonempty (fun i:Axis=>(lift (x-y) i).natAbs)
    rw [hi]; by_cases l:i∈os m a
    · obtain ⟨j,hj⟩:= (angles a).surjective ⟨i,l⟩
      have hJ:=hq j; rw [hj] at hJ; rw [← div_le_iff₀ hp, ← hJ]; exact dist_le_pi_dist _ _ _
    have hk:¬ OddAxis m (a i):=fun H=>l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩)
    have hu:=off_cap h i; have hv:=off_cap g i; rw [broadface,if_neg hk] at hu hv
    rw [off_lift h g hm,Pi.sub_apply, show offs a x i=0 by omega, show offs a y i=0 by omega,sub_zero]; simp
  exact (e ⟨0⟩).elim
lemma skull_inj (a:Index m)(hm:2≤m.val): InjOn (skull (B:=B) a) (↑(room m B a):Set _):=by
  intro x hx y hy hg
  have he:=skull_dist hx hy hm; rw [hg,dist_self] at he
  have hb: 0<(B.val:ℝ):=by positivity
  have hv : separation x y = 0:= by exact_mod_cast (div_eq_zero_iff.mp he.symm).resolve_right hb.ne'
  funext i; exact d_equal (x i) (y i) (Nat.eq_zero_of_le_zero ((component_le (x-y) i).trans hv.le))
lemma stone_close (B:Side)(d:ℕ)(z:Board d)(hz:z ∈ Peri _): ∃ y:Board d,y∈ Peri _∧ y∈ stoneX B d∧ dist z y ≤ 1/(B.val:ℝ):=by
  have hp:0<(B.val:ℝ):=by positivity
  let u (i:Fin d):= Int.floor ((B.val:ℝ)*z i)
  let y (i:Fin d):ℝ:= u i/(B.val:ℝ)
  have hb (i:Fin d): |z i|≤1:=by simpa [Peri,mem_sphere] using (dist_pi_le_iff (f:=z) (g:=(0:Board d)) zero_le_one).mp ((show dist z 0=1 from hz).le) i
  have ht (i): (u i).natAbs ≤ B.val := by
    obtain ⟨ha,hH⟩:=abs_le.mp (hb i); have hi:-(B.val:ℤ) ≤ u i:=by
      apply Int.le_floor.mpr; push_cast; nlinarith
    have hj:= Int.floor_le ((B.val:ℝ)*z i); change (u i:ℝ)≤_ at hj
    have he:u i≤(B.val:ℤ):= by exact_mod_cast (show (u i:ℝ)≤(B.val:ℝ) by nlinarith)
    omega
  refine ⟨y,?_,fun i=>⟨_,ht i,rfl⟩,?_⟩
  · rw [mem_sphere]; apply le_antisymm ((dist_pi_le_iff zero_le_one).mpr ?_)
    · by_contra! H; apply (show dist z 0=1 from hz).not_lt
      refine (dist_pi_lt_iff zero_lt_one).mpr (fun i=>?_); have he:dist (z i) ((0:Board d) i)≤1:=by simpa using hb i
      apply lt_of_le_of_ne he; intro h
      have hi := (dist_pi_lt_iff zero_lt_one).mp H i
      rw [Pi.zero_apply,Real.dist_eq,sub_zero] at h
      rcases (le_total 0 (z i)) with hv|hv
      · rw [abs_of_nonneg hv] at h; simp [y,u,h,hp.ne'] at hi
      rw [abs_of_nonpos hv] at h; have ht:u i= -(B.val:ℤ):=by unfold u; rw [show z i= -1 by linarith,mul_neg, mul_one,show -(B.val:ℝ)=((-↑B.val:ℤ):ℝ) by norm_num]; exact Int.floor_intCast _
      simp [y,ht,hp.ne'] at hi
    intro i; rw [Pi.zero_apply,Real.dist_eq,sub_zero]
    unfold y; rw [abs_div, abs_of_nonneg hp.le, ← Int.cast_abs, div_le_iff₀ hp,one_mul]; exact_mod_cast (show |u i|≤(B.val:ℤ) from by have hv:=ht i; rw [← Int.natCast_natAbs]; omega)
  rw [dist_pi_le_iff (by positivity)]; intro i
  have ht:=Int.floor_le ((B.val:ℝ)*z i); have he:=Int.lt_floor_add_one ((B.val:ℝ)*z i); change (u i:ℝ)≤_ at ht; change _ < (u i:ℝ)+1 at he
  rw [Real.dist_eq,abs_le]; unfold y; constructor <;> (field_simp; nlinarith)
end YM.CF.Mesa
