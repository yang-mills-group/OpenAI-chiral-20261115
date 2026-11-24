import YM.CF.Support.Sale
import YM.CF.Support.Gust
import YM.CF.Support.Tour

/-! From allowable row fees to arbitrary site hits, and trace costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {a c d K X : ℝ} {P : Seal Y→Raw D I} {p : Seal Y→Toll I}
def hit0 (z : Y) := univ.filter fun S:Seal Y=>z∈S
def hitE (a : ℝ) (W : Seal Y→ℝ) (z : Y) := ∑ S∈hit0 z, rent a S*W S
def ledgerV {I : Type*} [Fintype I] (w : Toll I) := ∑ i:I,∑ j:I,w i j
lemma covered_hit {C : ℝ} (h : ∀ S, Ticket s t S (p S) (P S)) (l : Ledger a p K) (hp : 0<a) (g : Capacity b C) (e : 0≤C) (o : Y) (j : ℕ) :
    let f := fun S=>ledgerV (p S)
    ∑ S∈(hit0 o).filter (fun x=>x.card=j), rent (a/2) S * f S ≤ Real.exp (-a/2*j)*(C*((j:ℝ)+1)^4)*K := by
  intro f; let A := (hit0 o).filter fun x=>x.card=j
  let m := Real.exp (-a/2*j); have hm : 0≤m := (Real.exp_pos _).le
  have hx i (ht:i∈A) : rent (a/2) i=m*rent a i := by unfold rent m; rw [←Real.exp_add,(mem_filter.mp ht).2]; congr 1; ring
  let X := board b (bay b.F o j)
  have he S (hi:S∈A) : f S=∑ i∈X,∑ k:I,p S i k := by
    unfold f ledgerV; rw [←sum_subset X.subset_univ]
    intro i _ ht; apply sum_eq_zero; intro k _; by_contra g
    obtain ⟨p,h,v⟩ := ((h S).expo _ _).triggered g
    have he : o∈S := (mem_filter.mp (mem_filter.mp hi).1).2
    apply ht; apply mem_filter.mpr; exact ⟨mem_univ _,by rw [←(mem_filter.mp hi).2]; exact p.basin he h⟩
  rw [sum_congr rfl (fun i (k:i∈A)=>show rent (a/2) i*f i=m*(rent a i*(∑ j∈X,∑ k:I,p i j k)) by rw [hx i k, he i k,mul_assoc]), ←mul_sum, show Real.exp _*(C*_)* K=m*(C*((j:ℝ)+1)^4*K) by unfold m; rw [mul_assoc]]
  apply mul_le_mul_of_nonneg_left _ hm
  simp_rw [mul_sum]; rw [sum_comm]
  have hx i : ∑ S∈A,∑ k:I, rent a S*p S i k ≤ K := by
    rw [sum_comm]; apply le_trans _ (l.rows i)
    exact sum_le_sum fun k _=> sum_le_sum_of_subset_of_nonneg A.subset_univ (fun S _ _=>mul_nonneg (rent_pos _ _).le ((h S).nonn i k))
  apply (sum_le_sum (fun i _=>hx i)).trans; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (g.place _ _) l.posP
-- companion scalar
lemma fund_hit (a C : ℝ) (g : 0<a) (e : 0≤C) : Summable (fun i:ℕ=>Real.exp (-a/2*i)*(C*((i:ℝ)+1)^4)) := by
  let r := Real.exp (-a/2); have hr : ‖r‖<1 := by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have ht := summable_pow_mul_geometric_of_norm_lt_one 4 hr
  have hp := ((summable_nat_add_iff 1).mpr ht).mul_right (C*r⁻¹)
  apply hp.congr; intro i; rw [mul_comm (-a/2),Real.exp_nat_mul]; simp only [Nat.cast_add,Nat.cast_one]
  change (_+_:ℝ)^4*r^(i+1)*(C*r⁻¹)=_; have he : r≠0 := (Real.exp_pos _).ne'
  rw [pow_succ]; field_simp; unfold r; ring_nf
lemma tall {C : ℝ} (h : ∀ S, Ticket s t S (p S) (P S)) (l : Ledger a p K) (hp : 0<a) (g : Capacity b C) (e : 0≤C) (o : Y) :
    hitE (a/2) (fun S=>ledgerV (p S)) o≤(∑' i:ℕ, Real.exp (-a/2*i)*(C*((i:ℝ)+1)^4))*K := by
  let f (i:ℕ):=Real.exp (-a/2*i)*(C*((i:ℝ)+1)^4)
  let M : ℕ := Fintype.card Y; have hx : ∀ S:Seal Y, S.card∈range (M+1) := fun i=> mem_range.mpr (lt_of_le_of_lt (card_le_univ _) (by unfold M; omega))
  have hm : hitE (a/2) (fun S=>ledgerV (p S)) o= ∑ i∈range (M+1), ∑ S∈(hit0 o).filter (fun S=>S.card=i), rent (a/2) S*ledgerV (p S) := by
    simp_rw [sum_filter]; rw [sum_comm]; simp [hx,hitE]
  rw [hm]; apply (sum_le_sum (fun i (_:i∈range (M+1))=>covered_hit h l hp g e o i)).trans
  rw [←sum_mul]; apply mul_le_mul_of_nonneg_right _ l.posP
  exact (fund_hit a C hp e).sum_le_tsum (range (M+1)) fun i _=> by positivity

-- trace later preserving each whole matrix support.
structure Element (b : Stage Y I D G) (S : Seal Y) (w : ℝ) (f : D→ℂ) : Prop where
  posT : 0 ≤ w
  conduct : w≠0→ Grove b.F S
  gauge (g : G) (x : D) : f (b.drive g x)=f x
  continuousE : Continuous f
  norms (x) : ‖f x‖≤w
  varies (x y) : ‖f x-f y‖≤ w*b.eval S x y
lemma ledgerT {N : Raw D I} {W : Toll I} {S} (h : Ticket s s S W N) : Element b S (ledgerV W) (fun x=> (N x).trace) := by
  have hE i : Continuous (fun x=> N x i i) := (h.expo i i).connected
  have he : ∑ i:I,W i i ≤ ledgerV W := sum_le_sum fun i _=> single_le_sum (fun j _=>h.nonn i j) (mem_univ i)
  refine ⟨(sum_nonneg (fun i _=> h.nonn i i)).trans he,fun p=>?_,fun g x=> ?_,h.cont.matrix_trace,fun x=>?_,fun x y=>?_⟩
  · unfold ledgerV at p; obtain ⟨i,-,v⟩ := exists_ne_zero_of_sum_ne_zero p; obtain ⟨j,-,e⟩ := exists_ne_zero_of_sum_ne_zero v; exact (((h.expo i j).triggered e)).1
  · rw [h.frame.frame,←twist_formula,trace_twist]
  · change ‖∑ i:I,N x i i‖≤_; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=>(h.expo i i).bounded x)).trans he)
  change ‖∑ i:I,N x i i-∑ i:I,N y i i‖ ≤ _; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans ((sum_le_sum (fun i _=>(h.expo i i).variation x y)).trans ?_)
  rw [←sum_mul]; exact mul_le_mul_of_nonneg_right he (b.pos ..)
structure Spends (b : Stage Y I D G) (F : Seal Y → D→ℂ) (K : Seal Y→ℝ) (a C : ℝ) : Prop where
  stamped (S) : Element b S (K S) (F S)
  payline (z : Y) : hitE a K z≤C
def Summaris (b : Stage Y I D G) (v : D →ℂ) (a C : ℝ) : Prop := ∃ F K, Spends b F K a C ∧ ∀ z,v z=∑ S,F S z
section
open Tour
variable {Z : Type*} (y : Tour Z)
theorem tours (h : y.ample) {s : ChartW y} {N : MapW y} (g : Enters y s s N) : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ z:Z,Summaris (y.stageK z) (fun x=> Matrix.trace (N z x)) a C := by
  obtain ⟨C,p,v⟩ := h; obtain ⟨a,K,t,l,q⟩ := g
  let m : ℝ := (∑' i:ℕ, Real.exp (-a/2*i)*(C*((i:ℝ)+1)^4))*K
  refine ⟨a/2,max 1 m,half_pos t,lt_max_of_lt_left zero_lt_one,?_⟩; intro z; obtain ⟨F,E,hN,p₁,Y⟩ := q z
  refine ⟨_,_,⟨fun S=>ledgerT (hN S),fun o=> (tall hN p₁ t (v z) p o).trans (le_max_right ..)⟩,fun x=>?_⟩
  change (N z x).trace=_; rw [Y,Matrix.trace_sum] -- tune
end
end YM.CF.Branch
