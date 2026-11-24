import YM.CF.Tulip.Volt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra

def names : ℕ ≃ Cover := Classical.choice (nonempty_equiv_of_countable (α:=ℕ) (β:=Cover))
lemma polygon (σ:ℝ)(hs:0<σ): ∃ e C : ℝ,0<e∧e≤1∧0<C∧∀ (n m:ℕ),m≤8*n→
   Real.exp (e*(m+1:ℕ))*((m+1:ℝ)*(1+e)^m)≤ C* Real.exp (σ*n):=by
  let t:=min (σ/32) 1; have ht:0<t:=lt_min (div_pos hs (by norm_num)) zero_lt_one; let K:= max t⁻¹ 1
  have hk: 1≤ K:=le_max_right ..; have hk': t⁻¹≤K := le_max_left ..; have hx: t≤σ/32:=min_le_left ..; have hx': t≤1:=min_le_right ..
  have hp(x:ℝ)(h:0≤x): x+1≤ K*Real.exp (t*x):=by
    have he:1≤K*t := (inv_le_iff_one_le_mul₀ ht).mp hk' -- tune order
    have hg:=Real.add_one_le_exp (t*x); nlinarith [mul_le_mul_of_nonneg_left hg (zero_le_one.trans hk),mul_le_mul_of_nonneg_right he h]
  refine ⟨t,Real.exp t*K,ht,hx',mul_pos (Real.exp_pos _) (zero_lt_one.trans_le hk),fun n m h=>?_⟩
  have he:(m:ℝ)≤8*n:=by exact_mod_cast h
  calc
    _ ≤ Real.exp (t*(m+1:ℕ))*((K*Real.exp (t*m)) * (Real.exp t)^m):=by
      gcongr <;> first | exact hp m (by positivity) | linarith [Real.add_one_le_exp t] | positivity
    _ = Real.exp t * K * Real.exp (3*t*m):=by rw [← Real.exp_nat_mul]; push_cast; rw [show t*((m:ℝ)+1)=t*m+t by ring, show 3*t*m=t*m+(t*m+(m:ℝ)*t) by ring]; simp only [Real.exp_add]; ring
    _ ≤ _:= by
      refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity); nlinarith [mul_le_mul_of_nonneg_left he ht.le,mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg n)]
variable (N:Side)
def tourP (f:Cover→Op SpinIdx)(o:Lattice.Order) (x:Chin N):Op (Single N):=∑ b:SpinIdx,∑ a:SpinIdx, ∑' n:ℕ, slider N (names n) o b a (f (names n) b a) x
def dialW (f:Cover→Op SpinIdx)(x:Chin N):Op (Single N):= (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ o:Lattice.Order, tourP N f o x
lemma finite_stock {ι:Type*}(f:Finset ι)(A:ι→WG Unit)(h:∀ i∈f,Lively (A i)) : Lively fun i N x=>∑ a∈f,A a i N x:=by
  classical
  induction f using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Lively.zero
  | @insert a S b ih=> simp only [Finset.sum_insert b]; exact (h a (Finset.mem_insert_self ..)).add (ih (fun _ hx=>h _ (mem_insert_of_mem hx)))
lemma d_live {ι: Type*} (f:ι→Cover→Op SpinIdx)(H:∃ σ C : ℝ,0<σ ∧0<C∧ ∀ i a b, Width σ C (fun x=>f i x a b)): Lively fun i N=> dialW N (f i) :=by
  obtain ⟨σ,K,hs,hK,H⟩:=H; obtain ⟨e,C,he,hp,hC,E⟩:=polygon σ hs
  let X:= Fintype.card Slot * C * K; let Y := ∑ _ : SpinIdx,∑ _ : SpinIdx,X
  apply Lively.scaleR (f:=fun i N x=> ∑ o:Lattice.Order, tourP N (f i) o x)
  apply certify he he (v:=0) (r:=∑ _ : Lattice.Order,Y); intro i N h
  refine Crown.sumK _ _ _ fun o _=> Crown.sumK _ _ _ fun b _=> Crown.sumK _ _ _ fun a _=>?_
  let w z:=Real.exp (σ*Laurent.size z)*‖f i z b a‖; let U(n:ℕ):= Fintype.card Slot * C * w (names n)
  have hg:=H i b a; have hu: Summable U:= (hg.2.1.comp_injective names.injective).mul_left _
  have hT: ∑' n,U n ≤ X:=by unfold U; rw [tsum_mul_left, names.tsum_eq]; exact mul_le_mul_of_nonneg_left hg.2.2 (by positivity)
  apply Crown.books (Crown.tsK U (fun n=>?_) he.le hu) hT
  apply stride N (names n) o b a (f i (names n) b a) _ e e he hp he.le
  intro v
  let k:=names n; let L:=leap k o
  unfold U w; rw [mul_assoc (↑(Fintype.card Slot):ℝ)]
  have hm:= mul_le_mul_of_nonneg_right (E (Laurent.size k) L.length (leap_dim k o)) (norm_nonneg (f i k b a)); simp only [mul_assoc] at * -- danger rewrites Width
  exact mul_le_mul_of_nonneg_left hm (by positivity)
end YM.CF.Tulip
