import YM.CF.Font.Vale
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {L c f n:Side}{a b A B M d:ℝ}
private lemma clockH (R:Ratio c f)(v:R.count=L){Λ:Ps f→Ps c→ℝ}{K: Wind f→ Wind c→ℝ}(q:SweepH Λ K M)(p:Rails R A a Λ)(x y:Wind f)(h:0<a)(k:0<b)(g:0≤M)(e:0≤A)(z:Site c) (H:(1+|A|+|tall f c M|)^2*nick b (3*c.val)≤ B*nick b f.val):∑ i:Wind c,∑ j:Wind c, nick b (contour z i j)*‖K x i*K y j‖≤ B*nick b f.val :=by
 apply le_trans _ H; let V:= A+tall f c M
 have ht: 0≤V:= by unfold V tall; positivity; -- tune
 calc
  _ ≤ nick b (3*c.val)*(∑ i, ‖K x i‖)*(∑ j, ‖K y j‖):=by
     rw [mul_assoc]; simp_rw [sum_mul,mul_sum]; refine sum_le_sum fun i _ =>sum_le_sum (fun j _=>?_); rw [norm_mul]; refine mul_le_mul_of_nonneg_right (nick_inc k.le (ct_pos ..) ?_) (by positivity); unfold contour; exact_mod_cast (show dial z i+dial z j≤3*c.val by have hh:=lowN z i; have hu:=lowN z j; omega)
  _ ≤ nick b (3*c.val)*V*V:=mul_le_mul (mul_le_mul_of_nonneg_left (totalH R q h p g e _) (nick_pos _ (by positivity)|>.le)) (totalH R q h p g e _) (sum_nonneg fun _ _=>norm_nonneg _) (mul_nonneg (nick_pos _ (by positivity)|>.le) ht)
  _ ≤ _:=by
    rw [mul_assoc, mul_comm _ (nick b _)]; apply mul_le_mul_of_nonneg_left _ (nick_pos _ (by positivity)|>.le); rw [sq]; have h: V≤1+|A|+|tall f c M|:=by unfold V; linarith [le_abs_self A,le_abs_self (tall f c M)]
    exact mul_le_mul h h ht (ht.trans h)
def tither (b:ℝ)(x:Site n){Z:Type*}[NormedAddCommGroup Z](W:Wind n→Wind n→ Z):ℝ:= ∑ i,∑ j,nick b (contour x i j)*‖W i j‖
lemma children(A a M:ℝ)(r:ℝ)(h:0<A)(k:0<a)(l:0≤r)(p:0≤M):∃ F:ℝ,0<F∧∀ L:Side,4≤L.val→ ∀ b:ℝ,0<b→b≤a/2→ ∃ V:ℕ,∀ {c f:Side}(G:Ratio c f),G.count=L→ V≤c.val→∀ Λ: Ps f→Ps c→ℝ,∀ K:Wind f→Wind c→ℝ, Rails G A a Λ→ SweepH Λ K M→∀ x:Site f,∀ y:Site c,(separation y (G.parent x):ℝ) ≤ r→ ∀ i j:Wind f,tither b y (roseK K x i j) ≤ nick b (contour x i j)* (F/(Real.sqrt (L.val:ℝ)*(L.val:ℝ)^4)):=by
 let F:=max (nick a (2*r)*Rails.fareH A a) 1
 have hF : 0<F:=lt_max_of_lt_right one_pos; refine ⟨F,hF,fun L he b v hb=>?_⟩
 let C:= F/(Real.sqrt (L.val:ℝ)*(L.val:ℝ)^4); have hp:0<C:=by unfold C; positivity
 obtain ⟨N,hx⟩:=probate he M A 1 C b one_pos hp v
 refine ⟨N,fun {n f} G u H Λ K hy hm x y hh i j=>?_⟩
 have hv(i j:Wind f)(h:(f.val:ℝ)≤contour x i j):tither b y (fun p q=> K i p*K j q)≤ nick b (contour x i j)*C:=by
    have he:=hx G H u; rw [mul_one] at he; exact le_trans (clockH G u hm hy i j k v p ‹0<A›.le y he) ((mul_le_mul_of_nonneg_left (nick_inc v.le (Nat.cast_nonneg _) h) hp.le).trans_eq (mul_comm ..))
 rcases i with i|i <;> rcases j with j|j
 · let f(u w:Ps n):= Λ i u *Λ j w-Λ (x,i.2) u*Λ (x,j.2) w
   rw [show tither b y _= checkV b y f by simp only [tither,roseK,hm.mouth,Fintype.sum_sum_type,remit,Sum.elim_inr,Sum.elim_inl,mul_zero,zero_mul,sub_self,norm_zero,sum_const_zero,add_zero]; rfl]
   refine (hy.camp_full k h v.le hb x i j y hh).trans ?_; change _≤ nick b (circle x i j)*C
   unfold spanV C; rw [u];
   calc
     _ = nick b (circle x i j) * ((nick a (2*r)*Rails.fareH A a)/(Real.sqrt (L.val:ℝ)*(L.val:ℝ)^4)):=by ring
     _ ≤ _ :=by gcongr; exact nick_pos _ (rot0 ..)|>.le; exact le_max_left ..
 · exact hv _ _ (le_add_of_nonneg_left (Nat.cast_nonneg (dial x (.inl i))))
 · exact hv _ _ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 exact hv _ _ (le_add_of_nonneg_right (Nat.cast_nonneg _))
end YM.CF.Font
