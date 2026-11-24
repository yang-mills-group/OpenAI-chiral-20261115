import YM.CF.Support.Product

/-! Absolute summation and power bases. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {f : Raw D I} {a c : ℝ}
lemma RootedK.oneK (s : Tag b) (a : ℝ) : RootedK s s a (Real.exp a) (fun _=>1) := by
  let W (x:Y) := ({x}:Seal Y)
  let F (x:Y) : Raw D I := fun _=>strip b (W x)
  let C (x:Y) : Toll I := fun i j => if i=j ∧ b.home i=x then 1 else 0
  have L x : Ticket s s (W x) (C x) (F x) := by
    refine ⟨fun i z=> strip_tag s i _, fun i j=>?_⟩
    have hp d : F x d i j=(C x i j:ℂ) := by unfold F C; by_cases g:i=j <;> by_cases h:b.home i=x <;> simp_all [strip,cutM,board,W]
    by_cases g:i=j ∧ b.home i=x
    · have H : C x i j=1 := if_pos g
      refine ⟨by rw [H]; exact zero_le_one,fun _=>⟨.single x,by simp [W,g.2],by rw [←g.1]; simp [W,g.2]⟩,?_,?_,continuous_const⟩
      · intro d; rw [hp d,H,Complex.ofReal_one,norm_one]
      intro z t; rw [hp z, sub_self,norm_zero,H,one_mul]; exact b.pos ..
    have hc : C x i j=0 := if_neg g
    simp_rw [hp,hc,Complex.ofReal_zero]; exact nothing ..
  refine lumped W F C a (Real.exp_pos a).le _ L ?_ ?_ ?_
  · intro v; ext i j; rw [Matrix.sum_apply]; by_cases g:i=j
    · subst j; simp only [F,strip,cutM,board,W,mem_filter,mem_univ,true_and,mem_singleton, Matrix.diagonal_apply_eq,Matrix.one_apply_eq]; simp
    simp [F,strip,cutM,g]
  · intro i; unfold C; simp only [ite_and,mul_ite,mul_one,mul_zero]; rw [sum_eq_single_of_mem _ (mem_univ i)]
    · simp [W,rent]
    intro j _ h; simp [Ne.symm h]
  intro i; unfold C; simp only [ite_and,mul_ite,mul_one,mul_zero]; rw [sum_eq_single_of_mem _ (mem_univ i)]; simp [W,rent]
  intro j _ h; simp [h]
lemma RootedK.powers (h : RootedK s s a c f) (g : 0≤a) (n : ℕ) : RootedK s s a (Real.exp a*(2*c)^n) (fun x=> f x ^ n) := by
  induction n with
  | zero => simpa using RootedK.oneK s a
  | succ n ih => rw [pow_succ,show Real.exp a*((2*c)^n*(2*c))=2*((Real.exp a*(2*c)^n)*c) by ring]; simp_rw [pow_succ (f _)]
                 exact ih.product h g
lemma RootedK.sumK {J : Type*} (p : Finset J) (k : J→ℝ) (f : J→Raw D I) (h : ∀ i∈p, RootedK s t a (k i) (f i)) : RootedK s t a (∑ j∈p,k j) (fun x=>∑ j∈p,f j x) := by
  classical
  induction p using Finset.induction_on with
  | empty => simp only [sum_empty]; exact RootedK.free
  | @insert i p e ih => simp only [sum_insert e]; exact (h i (mem_insert_self i p)).plus (ih (fun j hj=>h _ (mem_insert_of_mem hj)))

lemma kernel_test {B : Type*} (A : B→Op I) (f : Filter B) (x : Op I) : Tendsto A f (𝓝 x) ↔ ∀ i j,Tendsto (fun b=>A b i j) f (𝓝 (x i j)) := by
  change Tendsto (fun t : B=> fun i j:I=> A t i j) f (𝓝 (fun i j:I=>x i j)) ↔ _
  exact ⟨fun h i j=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j,fun h => tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (h i)⟩
lemma kernel_sum (A : ℕ →Op I) (h : ∀ i j,Summable (fun n=>A n i j)) : Summable A := by
  refine ⟨Matrix.of fun i j=>∑' n,A n i j,?_⟩
  unfold HasSum; rw [kernel_test]; intro i j
  have he := (h i j).hasSum; unfold HasSum at he; simpa only [Matrix.sum_apply, Matrix.of_apply] using he
lemma kernel_entry {A : ℕ→Op I} (h : Summable A) (i j) : (∑' n,A n) i j = ∑' n,A n i j := by
  have he := h.hasSum; unfold HasSum at he; rw [kernel_test] at he
  symm; apply HasSum.tsum_eq; unfold HasSum; simpa only [Matrix.sum_apply] using he i j
variable {f₁ : ℕ→Raw D I} (d : ℕ→ℝ)
lemma RootedK.tsK (h : ∀ n, RootedK s t a (d n) (f₁ n)) (p : 0 ≤ a) (e : Summable d) : RootedK s t a (∑' n,d n) (fun x=>∑' n,f₁ n x) := by
  choose F C L Q R using h
  let H (S:Seal Y) (x:D) := ∑' n,F n S x
  let K (S:Seal Y) (i j : I) := ∑' n,C n S i j
  have nn (n S i j) : 0≤C n S i j := (L n S).nonn _ _
  have ho S i j : Summable (fun n=>C n S i j) := e.of_nonneg_of_le (fun n=>nn n S i j) (fun n=>(Q n).price p (nn n) S i j)
  have hl S i j x : Summable (fun n=> ‖F n S x i j‖) := (ho S i j).of_nonneg_of_le (fun _=>norm_nonneg _) (fun n=>((L n S).expo i j).bounded x)
  have hm S x : Summable (fun n=>F n S x) := kernel_sum _ fun i j=>(hl S i j x).of_norm
  have hx S x i j : H S x i j=∑' n,F n S x i j := kernel_entry (hm S x) i j
  have hs i j : Summable (fun n=>saleM a (C n) i j) := summable_sum fun S _=> (ho S i j).mul_left _ -- tune
  have hk i j : saleM a K i j=∑' n,saleM a (C n) i j := by
    simp_rw [saleM]; rw [Summable.tsum_finsetSum (f:=fun S n=>rent a S*C n S i j)]; unfold K; simp_rw [tsum_mul_left]
    intro S _; exact (ho S i j).mul_left _
  have hw (S) : Ticket s t S (K S) (H S) := by
    refine ⟨fun i x=>?_,fun i j=>?_⟩
    · unfold H; rw [← Summable.tsum_mul_right _ (hm S _), ← Summable.tsum_mul_left _ (hm S _)]; apply tsum_congr; intro n; exact (L n S).frame i x
    have he := ho S i j
    have hp x := hl S i j x
    simp_rw [hx]; refine ⟨tsum_nonneg (fun _=>nn _ S i j),fun p=>?_,fun x=>(norm_tsum_le_tsum_norm (hp x)).trans ((hp x).tsum_le_tsum (fun n=>((L n S).expo i j).bounded x) he),?_,continuous_tsum (fun n=>((L n S).expo i j).connected) he (fun n=>((L n S).expo i j).bounded)⟩
    · by_contra g; apply p
      have hz (n:ℕ) : C n S i j=0 := by by_contra v; exact g (((L n S).expo i j).triggered v)
      simp [K,hz]
    intro x y
    let r := b.eval S x y
    have hi n : ‖F n S x i j-F n S y i j‖≤C n S i j*r := ((L n S).expo i j).variation ..
    have H := (he.mul_right r); have ht := H.of_nonneg_of_le (fun n=>norm_nonneg _) hi
    rw [← (hp x).of_norm.tsum_sub (hp y).of_norm]
    exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hi H).trans (le_of_eq (he.tsum_mul_right _)))
  refine ⟨H,K,hw,⟨tsum_nonneg fun n=>(Q n).posP,?_,?_⟩,?_⟩
  · intro i; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun j n=>saleM a (C n) i j) (hf:=fun j _=> hs i j)]; exact (summable_sum (fun j (_:j∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(Q n).rows i) e
  · intro j; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun i n=>saleM a (C n) i j) (hf:=fun i _=>hs i j)]; exact (summable_sum (fun i (_:i∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(Q n).cols j) e
  intro x; dsimp only; simp_rw [R]; exact Summable.tsum_finsetSum (f:=fun S n=>F n S x) (fun S _=>hm S x) -- tune
end YM.CF.Branch
