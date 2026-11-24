import YM.CF.Peaks.Bunch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
lemma uplands {σ:ℝ}(hp:0<σ)(L:Side): ∃ d M:ℝ,0<d∧d≤1∧0<M ∧∀ (n m:ℕ), m ≤ 16*L.val+8*L.val*n→ Real.exp (d*(((m+16*L.val+3:ℕ):ℝ)))*((m+1:ℝ)*(1+d)^m)≤M*Real.exp (σ*n):=by
  let C:=σ/L.val; have hh:=side_pos L
  obtain ⟨d,K,h,ht,H,p⟩:= polygon C (div_pos hp hh)
  let V:=d*((16:ℝ)*L.val+2); refine ⟨d,Real.exp V*K*Real.exp (C*(2*L.val)),h,ht,mul_pos (mul_pos (Real.exp_pos _) H) (Real.exp_pos _),fun n m hm=>?_⟩
  let k:=2*L.val+L.val*n; have hx:=p k m (hm.trans (le_of_eq (by unfold k; ring)))
  have hk : Real.exp (C*k)=Real.exp (C*(2*L.val))*Real.exp (σ*n):=by rw [←Real.exp_add]; congr 1; unfold C k; push_cast; field_simp
  have hu:Real.exp (d*(((m+16*L.val+3:ℕ):ℝ)))=Real.exp V*Real.exp (d*(m+1:ℕ)):=by rw [←Real.exp_add]; congr 1; push_cast; unfold V; ring
  rw [hu,mul_assoc]; apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans; rw [hk]; exact le_of_eq (by ring)

variable {N P:Side}(G:Ratio N P)(u v:Bool)
-- left V fine = true, etc
abbrev Track (L:Side):= Cover→Stk L
def douse (f:Track G.count)(o:Lattice.Order)(x:Coil N P): Op (Iota G):=∑ r: St G.count,∑ t : St G.count, ∑' i:ℕ, drag G u v r t (names i) (f (names i) r t) o x
def mosaic (f:Track G.count)(x:Coil N P):Op (Iota G):=(Fintype.card Lattice.Order:ℝ)⁻¹ • (∑ o:Lattice.Order,douse G u v f o x)
variable {ι:Type*}
lemma unanimous (L:Side)(ho:Odd L.val)(f:∀ i:ι, (S:Side)→Track S) (p: ∃ σ C:ℝ,0<σ∧0<C∧∀ i r t,Width σ C fun x=> f i L x r t): Save L u v (fun i _ _ G x=>mosaic G u v (f i G.count) x):=by
  obtain ⟨σ,C,h,p,hP⟩:=p; obtain ⟨d,M,h₀,hk,h1,H⟩:=uplands h L
  let q:= ↑(Fintype.card Slot)*(M*C); let Y:=Fintype.card (St L) * (↑(Fintype.card (St L))*q); let V:ℝ:=(Fintype.card Lattice.Order:ℝ)⁻¹
  refine recorded (L:=L) (u:=u) (v:=v) (A:=fun i _ _ G x=>mosaic G u v (f i G.count) x) (k:=0) (C:=‖(V:ℂ)‖* (∑ _ : Lattice.Order,Y)) (fun i N P G he hg=>?_) h₀ h₀
  subst L
  let S:= parcel G u d; let T:= parcel G v d
  let F(o:Lattice.Order)(r t):=fun n (x: legal G d)=> drag G u v r t (names n) (f i G.count (names n) r t) o x.val
  have hr (o r t):Crown (badge (legal G d)) S T d q (fun x=>∑' n,F o r t n x):=by
    let c(n:ℕ):= ‖f i G.count (names n) r t‖
    let A n:= Real.exp (σ*Laurent.size (names n))*c n; let Z (n:ℕ):= (↑(Fintype.card Slot)*M)*A n
    have hz:=hP i r t; have hx:= hz.2.1
    have hA : Summable A:=hx.comp_injective names.injective; have hZ: Summable Z:= hA.mul_left _
    have hl(n) : Crown (badge _) S T d (Z n) (F o r t n) := by
      apply swipe G u v ho _ _ _ _ o _ _ _ h₀ hk h₀.le; intro R; let k:= names n
      have Hx:= H (Laurent.size k) R (run_len u v G.count r t k o); apply le_trans (mul_le_mul_of_nonneg_left (_root_.le_trans (le_of_eq (mul_assoc _ _ _).symm) (mul_le_mul_of_nonneg_right Hx (norm_nonneg (f i G.count k r t)))) (Nat.cast_nonneg _)); unfold Z A c; exact le_of_eq (by ring)
    refine (Crown.tsK Z hl h₀.le hZ).books ?_
    unfold Z q; rw [tsum_mul_left,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ h1.le; unfold A c; rw [names.tsum_eq (f:=fun x:Cover=>Real.exp (σ*Laurent.size x)*‖f i G.count x r t‖)]; exact hz.2.2
  have hy(o): Crown (badge (legal G d)) S T d Y (fun x=>douse G u v (f i G.count) o x.val):=by
    have hh:= Crown.sumK univ _ _ fun r _=> Crown.sumK univ _ _ fun t _=> hr o r t; simp only [sum_const,card_univ,nsmul_eq_mul] at hh; exact hh
  have he:= (Crown.sumK univ _ _ fun o _=>hy o).scale (V:ℂ); convert he using 1; funext x; exact RCLike.real_smul_eq_coe_smul ..
lemma drag_one (f:Track G.count)(p r t k z b) (i : Iota G) (a:Slot): -- edit
    drag G u v r t k (f k r t) p 1 ((z,b),a) i =if b=r ∧ i.1=(z+wrap N k,t) then Rush.wind z k*f k r t*(1:Op Slot) a i.2 else 0:=by
  simp only [drag,Matrix.sum_apply]; rw [Finset.sum_eq_single z]; simp [panel, track_id]; intro d _ h; simp [panel,Ne.symm h]; simp
lemma dragged (f:Track G.count)(p r t)(h: Summable (fun x=> ‖f x r t‖)): Summable fun n:ℕ=> drag G u v r t (names n) (f (names n) r t) p 1:=by
  apply Branch.kernel_sum; intro ⟨⟨z,b⟩,a⟩ i; simp only [drag_one]; apply Summable.of_norm; apply (h.comp_injective names.injective).of_nonneg_of_le; intro; apply norm_nonneg; intro; split ; swap; simp; by_cases he:a=i.2 <;> simp [he,Matrix.one_apply, Rush.wind,Rush.fee_norm]
lemma doodle (f: Track G.count)(h:∀ r t,Summable (fun x=>‖f x r t‖)): mosaic G u v f 1=cart N f ⊗ₖ (1:Op Slot):=by
  have hh(o):douse G u v f o 1=cart N f ⊗ₖ (1:Op Slot):=by
    ext ⟨⟨y,b⟩,j⟩ ⟨⟨x,c⟩,l⟩; simp only [douse,Matrix.sum_apply]; simp_rw [kernel_entry (dragged _ _ _ _ _ _ _ (h _ _)), drag_one];
    rw [sum_eq_single b]; swap; intro i _ he; simp [Ne.symm he]; swap; simp
    rw [sum_eq_single c]; swap; intro i _ he; simp [Ne.symm he]; swap; simp
    change _=cart N f _ _ * _; simp only [cart,Matrix.of_apply,wagon_app]; rw [← tsum_mul_right,← names.tsum_eq]; simp [eq_comm]
  have ht: 0<(Fintype.card Lattice.Order:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  unfold mosaic; simp only [hh,sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ ht.ne']
end YM.CF.Peaks
