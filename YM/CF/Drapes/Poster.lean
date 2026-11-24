import YM.CF.Drapes.Awash
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter Branch
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y][TopologicalSpace D]
variable {b: Stage Y I D G}{s t:Tag b}{L:License D}{a d r q:ℝ}{A B:Raw D I}
def incline (b:Stage Y I D G)(n:ℕ)(x:ℝ)(p:I→ℝ)(a:ℝ) (w:Seal Y → Toll I): Prop := ∀ i:I, ∑ j,(1+x*b.F.span (b.home i) (b.home j))^n*saleM a w i j≤p i
/-- focus at row-only weight -/
def Street (L: License D)(s t:Tag b)(n:ℕ)(x:ℝ)(a:ℝ)(w:I→ℝ)(A:Raw D I):Prop:=∃ (P: Seal Y→Raw D I)(C:Seal Y→ Toll I), (∀ S, Suite L s t S (C S) (P S)) ∧ incline b n x w a C∧ ∀ x,A x=∑ S,P S x
variable {n:ℕ}{x:ℝ}{p k:I→ℝ}
lemma Street.plus (h:Street L s t n x a p A)(g: Street L s t n x a k B): Street L s t n x a (p+k) (fun x=> A x + B x):=by
  obtain ⟨F,K,H,q,V⟩:= h; obtain ⟨G,C,h,t',v⟩:=g
  refine ⟨_,_,fun i=>(H i).plus (h i),fun i=>?_,fun i=>by dsimp only;rw [V,v,sum_add_distrib]⟩
  specialize q i; specialize t' i; simp only [saleM] at q t'; simp_rw [saleM, Pi.add_apply,mul_add,sum_add_distrib]; simp_rw [mul_add,sum_add_distrib]; exact add_le_add q t'
lemma Street.prime(h:Street L s t n x a p A)(g:p≤k):Street L s t n x a k A:=by obtain ⟨F,C,h,t,v⟩:=h; exact ⟨F,C,h,fun i=>(t i).trans (g i),v⟩
lemma Street.desc(h:Street L s t n x a p A)(g:d≤a)(hp:0≤x): Street L s t n x d p A:=by
  obtain ⟨F,C,h,t,v⟩:=h
  exact ⟨F,C,h,fun i=> (sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (sale_mono (fun A u v=>mul_le_mul_of_nonneg_right (rent_up g A) ((h A).nonn u v)) i j) (by positivity)).trans (t i),v⟩
lemma street_free (s t:Tag b):Street L s t n x a 0 (fun _=>0):=by refine ⟨_,_,fun i=>Suite.free i,fun i=>?_,fun i=>?_⟩ <;> simp [saleM]
lemma Street.sumk {ι:Type*} (S: Finset ι)(p:ι→I→ℝ)(F:ι→Raw D I)(h:∀ i∈S, Street L s t n x a (p i) (F i)): Street L s t n x a (∑ i∈S, p i) (fun d=>∑ i∈S,F i d):=by
  classical
  induction S using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact street_free ..
  | @insert i S g ih=> simp only [Finset.sum_insert g]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun i p=>h i (Finset.mem_insert_of_mem p))
lemma mergeW {J:Type*}[Fintype J](W:J→Seal Y)(F:J→Raw D I)(C:J→Toll I)
    (h:∀ i, Suite L s t (W i) (C i) (F i))(g:∀ d, A d=∑ i:J, F i d)(he:∀ i,∑ j, (1+x*b.F.span (b.home i) (b.home j))^n*(∑ l:J,rent a (W l)*C l i j)≤p i): Street L s t n x a p A:=by
  let U(w:Seal Y)(i j:I):=∑ l∈dest W w,C l i j
  have hu(i j:I): saleM a U i j=∑ l:J,rent a (W l)*C l i j:=by rw [lump W _]; unfold saleM U; apply Finset.sum_congr rfl; intro X _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l hi=>by rw [show W l=X from (Finset.mem_filter.mp hi).2]
  refine ⟨_,U,fun S=>⟨Ticket.sumT (dest W S) C F (fun i hi=>by rw [← (mem_filter.mp hi).2]; exact (h i).toTicket), L.suppose _ _ (fun i _=>(h i).fuel)⟩,fun i=>by simp_rw [hu]; exact he i,fun d=>by rw [g, lump W _]⟩
lemma suite_ts {S} (F:ℕ→Raw D I)(C:ℕ→Toll I)(h:∀ i, Suite L s t S (C i) (F i))(ha:∀ i j, Summable (fun k=> C k i j)):
 Suite L s t S (fun i j=>∑' k,C k i j) (fun d=> ∑' k,F k d):=by
  have nn(k i j):0≤C k i j:=(h k).nonn ..
  have hx x i j: Summable (fun k=>‖F k x i j‖):=(ha i j).of_nonneg_of_le (fun _=>norm_nonneg _) (fun k=> ((h k).expo i j).bounded _)
  have he(x): Summable (fun i=> F i x):= kernel_sum _ (fun i j=>(hx x i j).of_norm)
  refine ⟨⟨fun i x=>?_,fun i j=>?_⟩,fun i j=>?_⟩
  · rw [← Summable.tsum_mul_right _ (he _), ← Summable.tsum_mul_left _ (he _)]; exact tsum_congr fun i=> (h i).frame ..
  · simp_rw [kernel_entry (he _)]
    refine ⟨tsum_nonneg (fun _=> nn ..),fun p=>?_,fun x=> (norm_tsum_le_tsum_norm (hx x i j)).trans ((hx x i j).tsum_le_tsum (fun n=> ((h n).expo i j).bounded _) (ha _ _)),fun x y=>?_,continuous_tsum (fun n=>((h n).expo i j).connected) (ha i j) (fun n=> ((h n).expo i j).bounded)⟩
    · by_contra hc; apply p; have hz(n:ℕ): C n i j=0:=by by_contra hv; exact hc (((h n).expo i j).triggered hv)
      simp [hz]
    rw [← (hx x i j).of_norm.tsum_sub (hx y i j).of_norm]
    have hp := (ha i j).mul_right (b.eval S x y); have hv(k:ℕ): ‖F k x i j-F k y i j‖≤C k i j*b.eval S x y:= ((h k).expo i j).variation ..
    have hy:= hp.of_nonneg_of_le (fun _=>norm_nonneg _) hv
    exact (norm_tsum_le_tsum_norm hy).trans ((hy.tsum_le_tsum hv hp).trans_eq ((ha i j).tsum_mul_right _))
  simp_rw [kernel_entry (he _)]
  exact L.sumK _ _ (ha _ _) (fun n=> (h n).fuel i j) (fun n=> ((h n).expo i j).bounded)
lemma Street.inf (p:ℕ→I→ℝ)(F:ℕ→Raw D I)(h:∀ i, Street L s t n x a (p i) (F i))(g:∀ i, Summable (fun n=> p n i))(ha:0≤x)(he:0≤a): Street L s t n x a (fun i=>∑' n,p n i) (fun x=>∑' n,F n x):=by
  choose V C H B Y' using h
  let r(i j:I):=(1+x*b.F.span (b.home i) (b.home j))^n
  have hr(i j:I):1≤ r i j:=one_le_pow₀ (by exact le_add_of_nonneg_right (by positivity)) -- inspect
  have nn(m S i j):0≤C m S i j:=(H m S).nonn i j
  have hl S i j: Summable (fun n=>C n S i j):=(g i).of_nonneg_of_le (fun n=>nn ..) (fun m=>by
    calc
      C m S i j≤ rent a S*C m S i j:=le_mul_of_one_le_left (nn ..) (rent_one he S)
      _ ≤ saleM a (C m) i j:=single_le_sum (f:=fun S=> rent a S*C m S i j) (fun S _=>mul_nonneg (rent_pos ..).le (nn ..)) (mem_univ S)
      _ ≤ r i j*saleM a (C m) i j:=le_mul_of_one_le_left (sale_nn (nn _) ..) (hr i j)
      _ ≤ _:= (single_le_sum (f:=fun j=>r i j*saleM a (C m) i j) (fun v _=>mul_nonneg (le_trans zero_le_one (hr i v)) (sale_nn (nn _) ..)) (mem_univ j)).trans (B m i))
  have hs i j:Summable fun n=>r i j*saleM a (C n) i j:=(summable_sum (s:=univ) (f:=fun S n=> rent a S*C n S i j) fun S _=> (hl S i j).mul_left _).mul_left _
  refine ⟨_,_,fun S=>suite_ts _ _ (fun i=> H i S) (hl S),fun i=>?_,fun x=>?_⟩
  · change ∑ j,r i j*(saleM a _ _ _)≤_
    have hp(j):r i j* saleM a (fun S i j=>∑' n,C n S i j) i j=∑' n,r i j*saleM a (C n) i j:=by
      rw [Summable.tsum_mul_left]; swap; exact summable_sum fun S _=>(hl S i j).mul_left _
      congr 1; unfold saleM; dsimp only; simp_rw [← tsum_mul_left]
      exact (Summable.tsum_finsetSum fun S (_:S∈(univ: Finset (Seal Y)))=> (hl S i j).mul_left (rent a S)).symm
    simp_rw [hp]; rw [←Summable.tsum_finsetSum]; exact (summable_sum (s:=Finset.univ) fun j _=>hs i j).tsum_le_tsum (fun a=>B a i) (g i); exact fun j _=> hs i j
  dsimp only; simp_rw [Y']; rw [Summable.tsum_finsetSum]; intro S _; exact kernel_sum _ fun i j=> ((hl S i j).of_nonneg_of_le (fun _=>norm_nonneg _) (fun n=> ((H n S).expo i j).bounded x)).of_norm
end YM.CF.Drapes
