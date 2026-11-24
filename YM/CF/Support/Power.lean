import YM.CF.Support.Compress

/-! Uniform submultiplicative fees after lowering support exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s : Tag b} {A B : Raw D I}
lemma diff_root {a r m : ℝ} (h : RootedK s s a r B) (e : RootedK s s a r A) (p : RootedK s s a m (fun x=>A x-B x)) (g : 0≤a) (n : ℕ) :
    RootedK s s a (2*((n:ℝ)*Real.exp a*m*(2*r)^(n-1))) (fun x=> A x^n-B x^n) := by
  induction n with
  | zero => simp only [pow_zero,sub_self,Nat.cast_zero, zero_mul,mul_zero]; exact RootedK.free
  | succ n ih =>
    let f := fun x:D=> A x^n*(A x-B x)+(A x^n-B x^n)*B x
    have he x : A x^(n+1)-B x^(n+1)=f x := by unfold f; rw [pow_succ,pow_succ,mul_sub,sub_mul]; abel
    simp_rw [he]
    have ht := ((e.powers g n).product p g).plus (ih.product h g)
    apply ht.books; cases n with
    | zero => simp [mul_assoc,mul_comm]
    | succ n => simp only [pow_succ, Nat.add_sub_cancel]; push_cast; exact le_of_eq (by ring)

lemma vol_block (C K u : ℝ) (h : 0≤C) (g : 0≤K) (p : 0 < u) (e : u < 1) (L : ℕ) :
    Tendsto (fun n:ℕ=>C*(((↑(n*(L*n)+L*n):ℝ)+1)^4)*blockCost u K n) atTop (𝓝 0) := by
  -- bound for n≥1 with n^8
  let V := (2*(L:ℝ)+1)^4; let W (n:ℕ) := (n:ℝ)^8
  have h₁ (n:ℕ) (hn:0<n) : (((↑(n*(L*n)+L*n):ℝ)+1)^4) ≤ V*(n:ℝ)^8 := by
    have he : (1:ℝ)≤n := by exact_mod_cast hn
    rw [show V*(n:ℝ)^8=((2*(L:ℝ)+1)*(n:ℝ)^2)^4 by unfold V; ring]; apply pow_le_pow_left₀ (by positivity) _
    push_cast
    have H : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left H (show 0≤(L:ℝ) by positivity)]
  have he k : Summable (fun n:ℕ=>(n:ℝ)^k*u^n) := summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_of_nonneg p.le])
  have hk : Tendsto (fun n:ℕ=> C*(V*W n)*blockCost u K n) atTop (𝓝 0) := by
    apply Summable.tendsto_atTop_zero
    apply (((he 8).mul_left (C*V)).add ((he 9).mul_left (C*V*K/u))).congr
    intro n; unfold blockCost; cases n with
    | zero => simp [W]
    | succ t => simp only [Pi.add_apply,pow_succ u,Nat.add_sub_cancel]; push_cast; unfold W; field_simp; push_cast; ring
  refine squeeze_zero' ?_ ?_ hk
  · apply Eventually.of_forall; intro n; unfold blockCost; positivity
  filter_upwards [eventually_gt_atTop 0] with i hi; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h₁ i hi) h) (by unfold blockCost; positivity)
lemma breakp {a K : ℝ} (h : 0 < a) (e : 0<K) : ∃ L : ℕ, 0<L ∧ Real.exp (-a/2*L)*(2*K)<1 := by
  obtain ⟨L,hl,hL⟩ := ((eventually_gt_atTop 0).and (show ∀ᶠ i:ℕ in atTop, Real.exp (-a/2*i)*(2*K)<1 from by
    let t := Real.exp (-a/2); have ht : 0≤t := (Real.exp_pos _).le; have H : t<1 := Real.exp_lt_one_iff.mpr (by linarith)
    have he : Tendsto (fun i:ℕ=>t^i*(2*K)) atTop (𝓝 0) := by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht H).mul_const (2*K)
    filter_upwards [he (gt_mem_nhds (show 0< (1:ℝ) by norm_num))] with i hi
    change t^i*(2*K)<1 at hi; rwa [mul_comm (-a/2),Real.exp_nat_mul])).exists
  exact ⟨L,hl,hL⟩
/-- Choice of grouping scales. n power, v truncation, d final exponent. -/
lemma grouping {C a K P u m : ℝ} (pC : 0≤C) (pa : 0<a) (pK : 0<K) (hp : P < u) (pq : 0 < u) (hq : u<1) (g : 0<m) :
    ∃ n:ℕ, n>0 ∧ ∃ (v:ℕ) (d:ℝ), 0<d ∧ d≤a/2 ∧ Real.exp (-a/2*v)*K+P ≤ u ∧ let V := C*(((n*v+v:ℕ):ℝ)+1)^4;
          2*((n:ℝ)*Real.exp (a/2)*(Real.exp (-a/2*v)*K)*(2*K)^(n-1)) + V*Real.exp (d*V)*blockCost u K n≤m := by
  obtain ⟨L,H,hL⟩ := breakp pa pK
  let x := Real.exp (-a/2*L); let t := x*(2*K); have he : 0<x := Real.exp_pos _; have ht : 0<t := mul_pos he (by positivity); have hx : x<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) (by exact_mod_cast H))
  have hz (n:ℕ) : Real.exp (-a/2*((↑(L*n):ℝ)))=x^n := by unfold x; rw [←Real.exp_nat_mul]; push_cast; ring_nf
  let F := fun n:ℕ=> Real.exp (-a/2*((L*n:ℕ):ℝ))*K
  let v (n:ℕ) := C*(((n*(L*n)+L*n:ℕ):ℝ)+1)^4
  let A (n:ℕ) := 2*((n:ℝ)*Real.exp (a/2)*F n*(2*K)^(n-1))
  have hF : Tendsto F atTop (𝓝 0) := by unfold F; simp_rw [hz]; simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one he.le hx).mul_const K
  have hD : Tendsto A atTop (𝓝 0) := by
    apply Summable.tendsto_atTop_zero
    have ht : Summable (fun n:ℕ => (n:ℝ)^1*t^n) := summable_pow_mul_geometric_of_norm_lt_one _ (by rw [Real.norm_of_nonneg ht.le]; exact hL)
    apply (ht.mul_right (Real.exp (a/2))).congr; intro n; cases n with
    | zero => simp [A]
    | succ n => unfold A F; rw [hz]; unfold t; rw [mul_pow]; simp only [pow_one, pow_succ,Nat.add_sub_cancel]; ring -- check
  let T := fun n:ℕ=>A n+v n*blockCost u K n
  have hT : Tendsto T atTop (𝓝 0) := by
    have hp : Tendsto (fun n=>v n*blockCost u K n) atTop (𝓝 0) := vol_block C K u pC pK.le pq hq L
    exact (zero_add (0:ℝ)) ▸ hD.add hp -- suspect
  obtain ⟨n,f,j,l⟩ := ((eventually_gt_atTop (0:ℕ)).and ((hF.eventually (gt_mem_nhds (sub_pos.mpr hp))).and (hT.eventually (gt_mem_nhds g)))).exists
  change F n<u-P at j; change T n<m at l
  let W (d : ℝ) := A n+v n*Real.exp (d*v n)*blockCost u K n
  have he : Continuous W := by unfold W; fun_prop
  have hn : W 0<m := by simpa [W,T] using l
  obtain ⟨d,hd,hp,hu⟩ : ∃ d:ℝ, d∈Set.Ioi 0 ∧ W d<m ∧ d<a/2 := by
    have hQ : ∀ᶠ d in nhdsWithin (0:ℝ) (Set.Ioi 0), W d<m := he.continuousAt.continuousWithinAt (gt_mem_nhds hn)
    exact ((show ∀ᶠ d in nhdsWithin (0:ℝ) (Set.Ioi 0), d∈Set.Ioi 0 from self_mem_nhdsWithin).and (hQ.and (nhdsWithin_le_nhds (gt_mem_nhds (half_pos pa))))).exists
  exact ⟨n,f,L*n,d,hd,hu.le,by change F n+P≤u; linarith,hp.le⟩

-- connector to kernel
/-- Block a power. Choices n,v,d are purely numerical, no volume dependence. -/
def GroupCost (C a K u m : ℝ) (n : ℕ) (d : ℝ) (b : Stage Y I D G) (s : Tag b) (F : Raw D I) : Prop := Capacity b C→RootedK s s a K F → (∀ x, ‖F x‖≤u) → RootedK s s d m (fun x=>F x^n)
lemma power_low [Nonempty I] (C a K u m P : ℝ) (n v : ℕ) (d : ℝ) (pC : 0≤C) (pa : 0≤a) (pu : 0≤u) (q : 0 ≤ d) (p : d ≤ a/2) (g : Real.exp (-a/2*v)*K+P≤u) (w : let V := C*(((n*v+v:ℕ):ℝ)+1)^4; 2*((n:ℝ)*Real.exp (a/2)*(Real.exp (-a/2*v)*K)*(2*K)^(n-1)) + V*Real.exp (d*V)*blockCost u K n ≤ m) : GroupCost C a K P m n d b s A := by
  rintro h B H
  obtain ⟨F,N,hF,hN,heq⟩ := B
  let V := C*(((n*v+v:ℕ):ℝ)+1)^4; let Y := V*Real.exp (d*V)*blockCost u K n; let L := 2*((n:ℝ)*Real.exp (a/2)*(Real.exp (-a/2*v)*K)*(2*K)^(n-1)); let T := lop F v
  have hA : RootedK s s (a/2) K A := (show RootedK s s a K A from ⟨F,N,hF,hN,heq⟩).drop (half_le_self pa)
  have hp : RootedK s s (a/2) K T := (lop_root F N hF hN).drop (half_le_self pa)
  have he : RootedK s s (a/2) (Real.exp (-a/2*v)*K) (fun x=>A x-T x) := lip_tail F N hF hN heq pa
  have hi : RootedK s s (a/2) L (fun x=>A x^n-T x^n) := diff_root hp hA he (q.trans p) _
  have hb : ∀ x, ‖lop F v x‖≤u := fun x=> (norm_le_norm_sub_add _ (A x)).trans ((add_le_add (by rw [norm_sub_rev]; exact he.boundOp (q.trans p) x) (H x)).trans g)
  have hY : RootedK s s d Y (fun x=>T x^n) := lower_block F N hF hN h pC u pu pa v n d q hb
  simpa only [sub_add_cancel] using (((hi.drop p).plus hY).books w)
end YM.CF.Branch
