import YM.CF.Cubes.Prism

/-! Face containment even in the minimum period. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {m B : Side}
def broadface (m B : Side) (a : Per (GridN m)) := if OddAxis m a then B.val else 0
def roomX (m B : Side) (a : Per (GridN m)) (x : Per (Domain m B)) := delta1 (Domain m B) x (high m B a) ≤ broadface m B a
instance (a x) : Decidable (roomX m B a x) := by unfold roomX; infer_instance
def room (m B : Side) (a : Index m) := univ.filter fun x:Site (Domain m B)=> ∀ i, roomX m B (a i) (x i)
@[simp] lemma room_mem (a : Index m) (x : Site (Domain m B)) : x∈room m B a ↔ ∀ i, roomX m B (a i) (x i) := by unfold room; simp only [mem_filter,mem_univ,true_and]
lemma broad_le (m B a) : broadface m B a≤B.val := by unfold broadface; split <;> omega
lemma room_e (m B a x) (h : ¬ OddAxis m a) : roomX m B a x ↔ x=high m B a := by
  unfold roomX; rw [broadface,if_neg h]; exact ⟨fun g=> d_equal _ _ (Nat.eq_zero_of_le_zero g),fun g=>by rw [g,d_id]⟩
lemma raddr (m B a) : address m B a ∈ room m B a := by rw [room_mem]; intro i; unfold roomX address; rw [high_here,d_id]; exact Nat.zero_le _
lemma full_r (m B : Side) (z : Site (Domain m B)) : ∃ a : Index m, z∈room m B a ∧ ∀ i, OddAxis m (a i) := by
  have H i : ∃ p:Per (GridN m), roomX m B p (z i) ∧ OddAxis m p := by
    obtain ⟨a,j,h,g,k⟩ := local_coords (z i)
    by_cases e:OddAxis m a
    · refine ⟨a,?_,e⟩; unfold roomX; rw [k,broadface,if_pos e,d_small _ j] <;> omega
    have he := oddAtAdd (m:=m) a|>.mpr e
    refine ⟨a+1,?_,he⟩; unfold roomX
    rw [k,show high m B a + ↑j=high m B (a+1)+(↑(j-(B.val:ℤ)):Per (Domain m B)) by rw [high_inc]; push_cast; abel,broadface,if_pos he,d_small] <;> omega
  choose a ha hu using H; exact ⟨a,(room_mem ..).mpr ha,hu⟩
lemma room_in {a c} (e : Fits m a c) : room m B a⊆room m B c := by
  intro x h; rw [room_mem] at *; intro i; rcases e i with g|⟨hf,H,K⟩
  · rw [←g]; exact h i
  unfold roomX; rw [(room_e m B (a i) _ hf).mp (h i),d_sym,d_high,broadface,if_pos H]; exact (Nat.mul_le_mul_left _ K).trans_eq (mul_one _)
lemma room_active {a x} (h : x∈room m B a) {b} (g : b∈active m B x) : Fits m b a := by
  intro i; obtain ⟨t,k⟩ := (active_iff ..).mp g; by_cases u : OddAxis m (a i)
  · by_cases e : a i=b i
    · exact Or.inl e.symm
    have ht := (room_mem ..).mp h i; unfold roomX at ht; rw [broadface,if_pos u,d_sym] at ht -- orient
    have hx := lt_of_le_of_lt (k i) (radius_lt ..); change delta1 (Domain m B) _ _ < B.val at hx
    have he : delta1 (GridN m) (a i) (b i) ≤ 1 := by
      have hg := (d_one_triangle (high m B (a i)) (x i) (high m B (b i))).trans (add_le_add ht hx.le)
      have hp := lt_of_le_of_lt (d_one_triangle (high m B (a i)) (x i) (high m B (b i))) (Nat.add_lt_add_of_le_of_lt ht hx)
      rw [d_high,←mul_two] at hp; exact Nat.le_of_lt_succ (lt_of_mul_lt_mul_left hp (Nat.zero_le _))
    right; exact ⟨fun l=> by have hp := d_even_sep (iff_of_true u l) e; omega,u,he⟩
  left; refine elect_unique (k i) ?_; unfold elect; rw [(room_e m B (a i) _ u).mp ((room_mem ..).mp h i),d_id]; exact Nat.zero_le _
lemma room_span {m B : Side} {a x} (h:x∈room m B a) : separation x (address m B a)≤B.val := by
  unfold separation pdist; apply Finset.sup_le; intro i _; change delta1 _ _ (address m B a i) ≤ B.val; unfold address; rw [high_here]; exact ((room_mem ..).mp h i).trans (broad_le ..)

-- choose face for the near-plane modification.
def scallop (B : Side) := collar B/3
def slabX (m B : Side) (a : Per (GridN m)) (x : Per (Domain m B)) := if OddAxis m a then roomX m B a x else delta1 (Domain m B) x (high m B a)≤collar B
def slab (m B : Side) (a : Index m) (x : Site (Domain m B)) := ∀ i, slabX m B (a i) (x i)
lemma one_slab (m B : Side) (x : Per (Domain m B)) : ∃ a:Per (GridN m), ∀ y, delta1 _ x y ≤ scallop B → slabX m B a y := by
  let s := scallop B; have ht : 2*s ≤ collar B := by unfold s scallop; omega
  obtain ⟨a,j,h,g,k⟩ := local_coords x
  let b := B.val
  have hx : x=high m B (a+1)+((j-(B.val:ℤ):ℤ):Per (Domain m B)) := by rw [k,high_inc]; push_cast; abel
  have hX : delta1 (Domain m B) x (high m B a)=j.natAbs := by rw [k,d_small _ j (by omega)]
  let i := j-(B.val:ℤ)
  have hY : delta1 (Domain m B) x (high m B (a+1))=i.natAbs := by rw [hx,d_small] <;> try omega -- tune
  have hu : j.natAbs+i.natAbs=B.val := by unfold i; omega
  have hd v y (l : delta1 _ x y ≤ s) : delta1 (Domain m B) y v ≤ s + delta1 (Domain m B) x v := (d_one_triangle y x v).trans (add_le_add_left ((d_sym x y).trans_le l) _)
  by_cases e:OddAxis m a
  · have H := oddAtAdd (m:=m) a
    by_cases l : i.natAbs ≤ s
    · refine ⟨a+1,?_⟩; intro y q; unfold slabX; rw [if_neg (by simp [H,e])]; have he := hd (high m B (a+1)) y q; rw [hY] at he; omega
    refine ⟨a,?_⟩; intro y q; rw [slabX,if_pos e]; unfold roomX; rw [broadface,if_pos e]; have he := hd (high m B a) y q; rw [hX] at he; omega
  have H := (oddAtAdd (m:=m) a).mpr e
  by_cases l:j.natAbs≤s
  · refine ⟨a,?_⟩; intro y q; unfold slabX; rw [if_neg e]; have he := hd (high m B a) y q; rw [hX] at he; omega
  refine ⟨a+1,?_⟩; intro y q; rw [slabX,if_pos H]; unfold roomX; rw [broadface,if_pos H]; have he := hd (high m B (a+1)) y q; rw [hY] at he; omega
lemma offered (m B : Side) (x : Site (Domain m B)) : ∃ a, ∀ y, separation x y≤scallop B→slab m B a y := by
  choose a h using fun i=>one_slab m B (x i); exact ⟨a,fun y g i=>h i (y i) ((component_le (x-y) i).trans g)⟩
-- snapping projection to even coordinate direction

def snap (m B : Side) (a : Index m) (x : Site (Domain m B)) : Site (Domain m B) := fun i=> if OddAxis m (a i) then x i else high m B (a i)
lemma snapped {x a} (h : slab m B a x) : snap m B a x ∈ room m B a := by
  rw [room_mem]; intro i; have he := h i; unfold snap; split <;> rename_i g
  · simpa only [slabX,g,if_true] using he
  exact (room_e m B (a i) _ g).mpr rfl
lemma voted_slab {a x} (h : slab m B a x) (t : Coin B) : selected m B (snap m B a x) t=selected m B x t := by
  have he := picked m B (snap m B a x) t; have hq := picked m B x t; funext i
  unfold ballot at he hq; have hu := h i; have hr := he i; unfold snap at hr; split at hr <;> rename_i p
  · exact elect_unique hr (hq i)
  rw [slabX,if_neg p] at hu
  have hx : elect m B (x i) t (a i) := by apply hu.trans; unfold radius; rw [if_neg p]; omega
  have ha : elect m B (high m B (a i)) t (a i) := by unfold elect; rw [d_id]; exact Nat.zero_le _
  rw [elect_unique (hq i) hx]; exact elect_unique hr ha -- potential occurrence i
lemma slab_act {x a} (h : slab m B a x) : active m B x=active m B (snap m B a x) := by unfold active; rw [show selected m B (snap m B a x)=selected m B x from funext (voted_slab h)]
lemma snap_sharp {x a} (h : slab m B a x) : separation x (snap m B a x) ≤ collar B := by
  unfold separation pdist; apply Finset.sup_le; intro i _; change delta1 _ (x i) _≤_; unfold snap; split <;> rename_i g; rw [d_id]; omega; have he:=h i; simpa only [slabX,g,if_false] using he
end YM.CF.Cube
