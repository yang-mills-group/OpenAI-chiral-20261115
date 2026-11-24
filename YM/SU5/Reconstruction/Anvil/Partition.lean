import YM.SU5.Reconstruction.Anvil.Roots
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
/-! # Arc staff. A real partition of angles buying boundary comparison by analytic growth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric
open scoped Topology BigOperators
local notation "π" => Real.pi
section
variable {ι:Type*}[Fintype ι][Nontrivial ι]
lemma half_ratio (x t:ℝ) (e:t= 2*Real.arctan x) : x*(1+Real.cos t)= Real.sin t:= by
  have hz:= Real.cos_arctan_pos x; let a:= Real.arctan x; have h:x*Real.cos a=Real.sin a:= by rw [←div_eq_iff (show Real.cos a ≠0 from hz.ne')|>.1 (show _ = _ from (Real.tan_eq_sin_div_cos a ▸ Real.tan_arctan x : Real.sin a/Real.cos a=x))] -- tune
  rw [e,Real.cos_two_mul,Real.sin_two_mul]; change x*(1+(2*Real.cos a^2-1)) = 2*Real.sin a * Real.cos a; rw [show 1+(2*Real.cos a^2-1)=Real.cos a*(2*Real.cos a) by ring,←mul_assoc,h]; ring
lemma archPrice (a:ι→ℝ)(p:∀ i,0<a i) : ∃ (t:ι→ℝ)(ρ:ℝ),0<ρ ∧ (∑ i,t i)=π ∧ ∀ i,t i∈Ioo (0:ℝ) π ∧ a i*(1+Real.cos (t i))=ρ*Real.sin (t i):=by
  let f (x:ℝ) := ∑ i, 2*Real.arctan (a i*x); have hc:Continuous f:=by unfold f; fun_prop
  have hz:f 0=0:=by simp [f]
  let b:ℝ:=∑ i:ι,2*(π/2)
  have hm:π < b:=by have h:1 < Fintype.card ι:= Fintype.one_lt_card; simpa [b, show 2*(π/2)=π by ring] using (show π < (Fintype.card ι:ℝ)*π from (by exact lt_mul_of_one_lt_left Real.pi_pos (by exact_mod_cast h))) -- name one_lt
  have ht:Tendsto f atTop (𝓝 b):= tendsto_finsetSum _ fun i v=> tendsto_const_nhds.mul ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.const_mul_atTop (p i))) -- name
  obtain ⟨r,g,hr⟩:= ((eventually_gt_atTop (0:ℝ)).and (ht.eventually (Ioi_mem_nhds hm))).exists
  obtain ⟨x,q,y⟩:= intermediate_value_Icc g.le hc.continuousOn (show π∈Icc (f 0) (f r) from ⟨hz.symm ▸ Real.pi_pos.le, le_of_lt hr⟩)
  have hx:0<x:=lt_of_le_of_ne q.1 (by rintro e; rw [← e,hz] at y; linarith [Real.pi_pos])
  refine ⟨fun i=>2*Real.arctan (a i*x),x⁻¹,by positivity,y,fun i=> ?_⟩
  obtain v:= half_ratio (a i*x) _ rfl; have hp:=Real.arctan_pos.mpr (mul_pos (p i) hx); dsimp; refine ⟨⟨by positivity,by linarith [Real.arctan_lt_pi_div_two (a i*x)]⟩,?_⟩; rw [←v]; field_simp
end
abbrev Spin (n:ℕ) := Fin (n+1)
local notation "ℭ"=> circleMap 0 1
variable {n:ℕ}
structure Score (n:ℕ) where
  span : Spin n→ℝ
  bud (i) : span i ∈ Ioo (0:ℝ) π
  extent : ∑ i, span i=π
variable (C:Score n)
namespace Score
open Finset
abbrev past (i:Spin n):ℝ:= ∑ j∈ univ.filter (· < i), (2*C.span j)
abbrev future (i:Spin n):ℝ:= C.past i + 2*C.span i
abbrev post (i:Spin n):= ℭ (C.past i)
abbrev shift (i:Spin n) := finRotate _ i
variable {i j: Spin n}
lemma bud_lt (i:Spin n): C.past i < C.future i:= by unfold future; linarith [(C.bud i).1]
lemma future_price (i:Spin n): C.future i= ∑ j∈ univ.filter (· ≤ i), (2*C.span j):= by
  unfold future past; rw [show (univ.filter (· ≤ i))= insert i (univ.filter (· < i)) by ext; simp [le_iff_lt_or_eq,or_comm],sum_insert (by simp),add_comm]
lemma budgets (i:Spin n): 0≤ C.past i ∧ C.future i ≤ 2*π:= by
  have h: ∀ i:Spin n, 0 ≤ 2*C.span i:= fun i=> by linarith [(C.bud i).1]
  rw [future_price]; exact ⟨sum_nonneg (fun i _=> h i),(sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>h i)).trans_eq (by rw [← mul_sum,C.extent])⟩
lemma future_le (v:i<j): C.future i ≤ C.past j:= by rw [future_price]; exact sum_le_sum_of_subset_of_nonneg (show univ.filter (· ≤ i) ⊆ univ.filter (· < j) from by intro t h; exact mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_lt (mem_filter.mp h).2 v⟩) (fun i _ _=>by linarith [(C.bud i).1])
lemma start_price (i:Spin n)(v:i≠ Fin.last n) : C.past (shift i)= C.future i:= by
  rw [future_price,past]; congr 1
  ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; have h:=coe_finRotate_of_ne_last v; change j.val < (finRotate (n+1) i).val ↔ j.val ≤ i.val; omega
@[simp] lemma price_zero : C.past 0=0:= by unfold past; rw [show (univ.filter (· < (0:Spin n)))= ∅ from by ext i; simp]; simp
@[simp] lemma price_last: C.future (Fin.last n)= 2*π:=by rw [future_price,show (univ.filter (· ≤ Fin.last n))= Finset.univ from by ext i; simp [Fin.le_last i]]; rw [← mul_sum,C.extent]
@[simp] lemma post_next (i:Spin n): C.post (shift i)= ℭ (C.future i):= by
  rcases eq_or_ne i (Fin.last n) with rfl|p; · rw [post,shift,finRotate_last,price_last,price_zero, show 2*π = (0:ℝ)+ 2*π by ring, periodic_circleMap 0 1 0] -- tune projection
  rw [post,start_price C _ p]
include C in
lemma cycle_sep (i:Spin n) : shift i≠i:=by
  intro h; have ht:= C.post_next i; rw [h] at ht; have he:= eq_of_circleMap_eq (by norm_num) (show |C.past i-C.future i|<2*π from abs_lt.mpr ⟨by unfold future; linarith [(C.bud i).2],by linarith [C.bud_lt i,Real.pi_pos]⟩) ht; linarith [C.bud_lt i] -- lean unused C warning not ok
lemma strict_price : StrictMono C.past:= fun _ _ p=> (C.bud_lt _).trans_le (C.future_le p)
lemma distinct_post: Injective C.post:= by
  intro i j h; have v(t:Spin n): 0≤ C.past t ∧ C.past t<2*π:= ⟨(C.budgets t).1,(C.bud_lt t).trans_le (C.budgets t).2⟩
  exact C.strict_price.injective ((injOn_circleMap_of_abs_sub_le' (by norm_num) (by linarith)) (show _ ∈ Set.Ico _ _ from v i) (show _∈ Set.Ico _ _ from v j) h)
lemma division (x:ℝ)(p:x∈ Set.Icc 0 (2*π)):∃ i,C.past i ≤ x ∧ x≤ C.future i:=by
  let D:Finset (Spin n):=univ.filter fun i=> C.past i ≤x; have ht:D.Nonempty:= by refine ⟨0,?_⟩; simpa [D] using p.1
  let i:= D.max' ht; have v:x≥ C.past i:= (mem_filter.mp (max'_mem D ht)).2
  rcases eq_or_ne i (Fin.last n) with he|he; · exact ⟨i,v,by rw [he,price_last]; exact p.2⟩
  refine ⟨i,v,?_⟩; by_contra! hp; exact (not_lt_of_ge (le_max' D (shift i) (mem_filter.mpr ⟨Finset.mem_univ _,(C.start_price i he).symm ▸ hp.le⟩))) ((lt_finRotate_iff_ne_last i).mpr he)
lemma not_post (t:ℝ)(v:t∈ Set.Ioo (C.past i) (C.future i)) (j:Spin n): ℭ t ≠ C.post j := by
   intro h; have e:= (C.budgets i); have u:= (C.budgets j); have a:= v.1; have b:= v.2; let x:= C.bud_lt j
   have hQ:= eq_of_circleMap_eq (by norm_num) (abs_lt.mpr (And.intro (by linarith [x,e.1,e.2,u.1,u.2]) (by linarith [x,e.1,e.2,u.1,u.2]))) (show circleMap 0 1 t=circleMap 0 1 (C.past j) from h)
   by_cases q:i<j; · linarith [C.future_le q]
   linarith [C.strict_price.monotone (le_of_not_gt q)]
end Score
end YM.Anvil
