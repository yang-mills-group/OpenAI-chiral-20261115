import YM.CF.Tulip.Key
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (N:Side)
lemma slider_id (z:Cover)(o:Lattice.Order)(b a:SpinIdx)(c:ℂ)(x y:Site N)(i j:SpinIdx)(l l':Slot): slider N z o b a c 1 ((x,i),l) ((y,j),l')=if i=b ∧ y=x+wrap N z∧ j=a then wind x z*c*(1:Op Slot) l l' else 0:=by
  simp only [slider, Matrix.sum_apply]; rw [Finset.sum_eq_single x];
  · simp only [panel,Matrix.of_apply,track_id,Prod.mk.injEq,Matrix.smul_apply,smul_eq_mul]; by_cases h:i=b <;> by_cases g:y=x+wrap N z <;> simp [h,g]
  · intro i _ h; simp [panel,Ne.symm h]
  simp
lemma slider_sum (f:Cover→Op SpinIdx)(p b a) (h: Summable (fun z=>‖f z b a‖)): Summable fun n:ℕ=> slider N (names n) p b a (f (names n) b a) 1:=by
  apply Branch.kernel_sum; intro ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,t⟩; simp only [slider_id]; apply Summable.of_norm; apply Summable.of_nonneg_of_le _ _ (h.comp_injective names.injective); intro; apply norm_nonneg
  intro n; split; swap; simp
  by_cases he:l=t <;> simp [he,Matrix.one_apply,Rush.wind,Rush.fee_norm]
lemma dial_id (f:Cover→Op SpinIdx)(h:∀ b a,Summable (fun z=>‖f z b a‖)): dialW N f 1=(cart N f) ⊗ₖ (1:Op Slot):=by
  have he(p): tourP N f p 1=(cart N f) ⊗ₖ (1:Op Slot):=by
    ext ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,m⟩; simp only [tourP,Matrix.sum_apply]; simp_rw [kernel_entry (slider_sum _ _ _ _ _ (h _ _)),slider_id];
    rw [Finset.sum_eq_single i]; swap
    · intro b _ h; simp [Ne.symm h]
    swap; simp
    rw [Finset.sum_eq_single j]; swap
    · intro a _ h; simp [Ne.symm h]
    swap; simp
    change _=cart N f (x,i) (y,j)*(1:Op Slot) l m
    simp only [cart,Matrix.of_apply,wagon_app]
    rw [← tsum_mul_right,← names.tsum_eq]; simp [eq_comm]
  have ht: 0<(Fintype.card Lattice.Order:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  unfold dialW; simp only [he,sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ ht.ne']
lemma tube_uniform {ι:Type*}(j)(M:ι→Side)(hM:∀ i,Odd (M i).val)(p:1≤j): Lively (fun i N=> dialW N (tub (bar j (M i)))):=by
  obtain ⟨⟨σ,C,H,he,h⟩,-⟩:=tub_bill (barBudget j p M hM) (fun i p hp x hx=> bar_overlap _ _ hp x hx)
  apply d_live _ ⟨σ,C,H,he,fun i b a=>?_⟩; simpa using h i b a
def reserveP (j:ℕ)(M: Side): Chin N→Op (Single N):= dialW N (tub (bar j M))
def art (j:ℕ)(M:Side)(x:Chin N):Op (Single N):= reserveP N j M x+pale (reserveP N j M) x-1
lemma ptone {j}(hj:1≤j)(M:Side)(hm:Odd M.val): reserveP N j M 1=plates N (bar j M) ⊗ₖ (1:Op Slot):=by
  have h:Reads (tub (bar j M)) (bar j M):=cBar j M true hj hm
  rw [reserveP,dial_id N _ h.sumK,cart_traded h]
lemma art_one {j}(hj:1≤j)(M:Side)(hm:Odd M.val): art N j M 1= (2:ℝ) • reserveP N j M 1 -1 ∧ IsStarProjection (reserveP N j M 1):=by
  have he: (ice (1:Chin N))=1:=by rw [← profile_trivial, ice_pr]
  have hg : IsStarProjection (plates N (bar j M)):=by
    let P:=bar j M
    have hx := fun (p:Momentum) (hp:p∈realCube zone)=> firm_bar j M hm hp
    refine ⟨?_,?_⟩; swap
    · rw [isSelfAdjoint_iff,pilesS]; apply pilesE; intro p hp _; exact (hx _ hp).2
    unfold IsIdempotentElem; rw [pilesP]; apply pilesE; intro p hp _; exact (hx _ hp).1
  rw [art,pale,he, ptone N hj M hm]; simp only [op_star_kron,hg.isSelfAdjoint.star_eq,star_one]
  exact ⟨by rw [two_smul],⟨by unfold IsIdempotentElem; rw [op_kron_mul, hg.isIdempotentElem.eq,mul_one], by rw [isSelfAdjoint_iff,op_star_kron,hg.isSelfAdjoint.star_eq,star_one]⟩⟩
end YM.CF.Tulip
