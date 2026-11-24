import YM.CF.Peaks.Roller
/-! Weighted transfer of open endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(u:Bool)(D : List Axis)(hd:D.length+2≤j)
def followV (D: List Axis)(L:Side):= Real.sqrt L.val/(L.val:ℝ)^(D.length+2)
lemma Vpos (L:Side):0< followV D L:=div_pos (Real.sqrt_pos.mpr (side_pos _)) (pow_pos (side_pos _) _)
-- unaveraged douse
abbrev surfcoat (j:ℕ)(u:Bool)(D:List Axis): Script Male:=fun i _ _ G x=> douse G true false (tub (coverlet u j G.count i.val D)) 1 x
include hd in
lemma furl {N P:Side}(G:Ratio N P)(h:Odd G.count.val)(i:Male): Reads (tub (coverlet u j G.count i.val D)) (coverlet u j G.count i.val D):=by
  have hp: Pay (fun _:Unit=>followV D G.count) (fun _=>coverlet u j G.count i.val D):=by
    unfold coverlet; apply col_quote; intro i'; exact portrait u j _ _ (fun _=> h) (fun _=>i.property) (fun _=>i') D hd
  exact paid hp (fun _ p hp x h'=>by unfold coverlet; congr 1; ext1 i; exact spans _ _ _ _ _ _ hp x h') ()
lemma nonblank (L:Side)(p:Cover)(r t:St L)(M:Side)(h:t.1≠0): tub (coverlet u j L M D) p r t=0:=by
  cases r; cases t; simp [tub,coverlet, c_app,h,placed,market, UnitAddTorus.mFourierCoeff,veils] -- tuning
include hd in
lemma wide(m:ℕ): ∃ C:ℝ, 0<C∧∀ L:Side, Odd L.val→∃ a:ℝ,0<a∧Score L (surfcoat j u D) true false a (C*followV D L) m 0 a:=by
  let I:=Σ x:Male×Male,Site x.1.val
  obtain ⟨b,C,p,h,V⟩:= pricelet u j (fun w:I=> w.1.1.val) (fun w:I=> w.1.2.val) (fun w=>w.1.1.property) (fun w=>w.1.2.property) (fun w=> w.2) D hd
  obtain ⟨R,hR,H⟩:=typical b p m
  let U:=↑(Fintype.card Slot)*R
  refine ⟨Fintype.card SpinIdx * (U*C),mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (mul_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hR) h),fun L hh=>?_⟩
  obtain ⟨e,ht,hE,hV⟩:=H L
  refine ⟨e,ht,fun i N P G he ha=>?_⟩; subst L
  let P1:=tempo G e; let x:ℝ:= (G.count.val:ℝ)⁻¹
  let A:= tub (coverlet u j G.count i.val D); let F(r t:St G.count)(z:ℕ):Raw ↥(legal G e) (Iota G):=fun y=> drag G true false r t (names z) (A (names z) r t) 1 y.val
  let K:= U * C * followV D G.count
  let c(r t:St G.count)(i:Iota G) := if t.1=0 ∧i.1.2=r then K else 0
  have hc(r t:St G.count): Street (badge _) (parcel G true e) (parcel G false e) m x e (c r t) (fun x:legal G e=>∑' n,F r t n x):=by
    obtain ⟨a,y⟩:=t; by_cases hg:a=0; swap
    · have hp(n): A (names n) r (a,y)=0:=nonblank j u D G.count _ _ _ _ hg
      have he(n:ℕ): F r (a,y) n=0:=by ext x z w; simp only [F, hp]; simp [drag,panel,Matrix.sum_apply]
      simp_rw [he,Pi.zero_apply,tsum_zero,c,hg,false_and,ite_false]; exact street_free .. -- syntax
    subst a
    let T z:= ‖A (names z) r (0,y)‖; let f n:= Real.exp (b*(Laurent.size (names n)))*T n
    have he:=V (⟨(⟨_,hh⟩,i),r.1⟩:I) r.2 y
    have hw: Summable f:=he.2.1.comp_injective names.injective
    let d(n:ℕ)(z:Iota G):=if z.1.2=r then U*f n else 0
    have hk(n): Street (badge _) (parcel G true e) (parcel G false e) m x e (d n) (F r (0,y) n):=by
      refine comic G true false hh r (0,y) _ _ 1 e (U*f n) m ht hE ?_; intro ℓ s
      let k:= names n
      have hy:=hV (Laurent.size k) ℓ (run_len true false G.count r (0,y) k 1)
      unfold U f; rw [mul_assoc (Fintype.card Slot:ℝ) R]; change ↑(Fintype.card Slot)*((1+x*s)^m*Real.exp _*((ℓ*e+1:ℝ)*(1+e)^ℓ*T n))≤ ↑(Fintype.card Slot)*(R*(Real.exp (b*Laurent.size k)*T n)); -- inspect
      refine mul_le_mul_of_nonneg_left ?_ (by positivity); rw [← mul_assoc ((1+x*s)^m*_) _ (T n), ← mul_assoc R]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    have ht': Street (badge _) (parcel G true e) (parcel G false e) m x e (fun i=>∑' n,d n i) (fun x=>∑' n,F r (0,y) n x):= Street.inf _ _ hk (fun i=>by by_cases h:i.1.2=r <;> simp only [d,h,if_true,if_false]; exact hw.mul_left _; exact summable_zero) (by unfold x; positivity) ht.le
    apply ht'.prime; intro z; by_cases hv:z.1.2=r; swap; simp [c,d,hv]
    simp only [d,c,hv,and_self,ite_true]; rw [tsum_mul_left]
    unfold K; rw [mul_assoc U C]; apply mul_le_mul_of_nonneg_left _ (by unfold U; positivity)
    have hz: ∑' n,f n=∑' k:Cover,Real.exp (b*Laurent.size k)*‖A k r (0,y)‖:= names.tsum_eq (fun k=>Real.exp (b*Laurent.size k)*‖A k r (0,y)‖) -- tune
    rw [hz]; exact he.2.2
  have hu:= Street.sumk univ _ _ (fun i _=> Street.sumk univ _ _ (fun j _=> hc i j)); apply hu.prime; intro k
  simp only [Finset.sum_apply,c]; let t:=k.1.2
  rw [Finset.sum_eq_single t]; swap
  · intro i _ h; have hg : k.1.2≠ i:= Ne.symm h; simp [hg]
  swap; simp
  simp only [show k.1.2=t from rfl,and_true]; rw [show ∑ i:St G.count,(if i.1=0 then K else 0)=(Fintype.card SpinIdx)*K by unfold St; rw [Fintype.sum_prod_type,Finset.sum_eq_single 0]; simp; intro x _ h; simp [h]; simp]; exact le_of_eq (by unfold K; ring)
end YM.CF.Peaks
