import YM.CF.BProof.Floral.Rule
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal
namespace YM.CF.Floral
variable {ι:Type*}{L:ℝ}
def lab (S:Finset ι)(w:ι→ℝ)(Q:ι→Cost L):Cost L := fun x c=>∃ a:ι→ℝ,(∀ i∈S, Q i x (a i)) ∧ (∑ i∈S,w i * a i)≤c
lemma Rule.sigma (S:Finset ι)(w:ι→ℝ)(Q:ι→Cost L)(p:∀ i∈ S,0<w i)(h:∀ i∈S, Rule (Q i)) : Rule (lab S w Q):=by
 classical
 induction S using Finset.induction_on with
 | empty=>refine (none_cost L).rose fun x c=> ?_; simp [lab]
 | insert i S g ih=>
    have H0:= (h i (Finset.mem_insert_self ..)).coin (w i) (p i (Finset.mem_insert_self ..)); have Hb:=ih (fun j s=>p _ (Finset.mem_insert_of_mem s)) (fun j s=>h _ (Finset.mem_insert_of_mem s))
    refine (H0.sum Hb).rose fun x c=> ?_
    constructor
    · rintro ⟨u,v,⟨k,l,b⟩,⟨A,F,m⟩,d⟩; refine ⟨Function.update A i k, ?_,?_⟩
      · intro j y; rcases Finset.mem_insert.mp y with rfl|s; simpa; rw [Function.update_of_ne (by aesop : j ≠ i)]; exact F j s
      rw [Finset.sum_insert g,update_self,Finset.sum_congr rfl (g:=fun j=> w j*A j) (fun j J=>by rw [update_of_ne (by aesop : j ≠ i)])]; linarith
    rintro ⟨a,p,h⟩; rw [Finset.sum_insert g] at h; exact ⟨w i * a i,_,⟨a i,p _ (Finset.mem_insert_self ..),le_rfl⟩,⟨a,fun j g=> p _ (Finset.mem_insert_of_mem g),le_rfl⟩,h⟩
/-- Equivalent global tall cost (when each budget participates) via minimum payments. -/
lemma Rule.least (x:Points L){C:Cost L} (h:Rule C)(t:∃ c,C x c):∃ a, C x a ∧ ∀ b,C x b→ a≤ b:=by
 obtain ⟨T,z,g,H⟩:=h; obtain ⟨c,h⟩:=t; let S:= (fun f=>‖pup x f‖) '' T; have hx(k):upperBounds S k ↔ C x k:=⟨fun p=> (H x k).mpr fun i v=>p (mem_image_of_mem _ v),fun p _ ⟨i,b,e⟩=> e ▸ (H x k).mp p i b⟩ -- upperbounds notation?
 have hk:= isLUB_csSup (s:=S) (Set.Nonempty.image _ ⟨0,z⟩) ⟨_,(hx c).mpr h⟩; exact ⟨sSup S,(hx _).mp hk.1,fun b k=>hk.2 ((hx b).mpr k)⟩
lemma Rule.tally {J:Type*}[Nonempty J] (S:J→Finset ι)(w:ι→ℝ)(Q:ι→Cost L)(p:∀ i,0<w i)(h:∀ i, Rule (Q i))(g:∀ i,∃ j,i∈ S j):Rule (fun x c=>∃ a:ι→ℝ,(∀ i,Q i x (a i)) ∧ ∀ j,(∑ i∈S j,w i * a i) ≤ c):=by
 classical
 refine (max_cost' (fun j=>sigma (S j) w Q (fun i _=> p i) (fun i _=>h i))).rose fun x c=> ?_
 constructor
 · intro s; choose t b m using s; choose a v A using fun i=> least x (h i) (by obtain ⟨j,j'⟩:=g i; exact ⟨_, b j i j'⟩)
   exact ⟨a,v,fun j=> (Finset.sum_le_sum (fun i p'=>mul_le_mul_of_nonneg_left (A i _ (b j _ p')) (p i).le)).trans (m j)⟩
 rintro ⟨a,v,t⟩ j; exact ⟨a,fun i _=>v i,t j⟩
end YM.CF.Floral
