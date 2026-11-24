import YM.CF.Fixed.StageSlice

/-! Adding the necessary variations to trace. Reindexing helper in operator
norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fixed.Bulk
open Function NormedSpace Lattice Fock Filter Metric Matrix Finset Rift
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

variable {n m:Type*}[Fintype n][DecidableEq n][Fintype m][DecidableEq m]

-- norm transport via SA
lemma book_s (A:Op n) : Safe A ↔ IsSelfAdjoint A ∧ ((1/2:ℝ) • 1 ≤ A*A) ∧ A*A ≤ (256:ℝ) • 1 := by
  constructor
  · intro h
    refine ⟨h.self,sq A ▸ h.margin, (op_le_norm_one (h.self.commute_iff h.self|>.mp (Commute.refl A))).trans ?_⟩ -- name
    gcongr; exact (norm_mul_le ..).trans ((mul_le_mul h.bound h.bound (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  rintro ⟨hp,he,hz⟩; refine ⟨hp,?_ ,(sq A).symm ▸ he⟩
  have hh : 0 ≤ A*A:= by nth_rw 1 [← hp.star_eq]; exact star_mul_self_nonneg A
  have hu: ‖A*A‖≤256:= (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num: (0:ℝ)≤256) hh).mpr (by rwa [Algebra.algebraMap_eq_smul_one])
  have hx := CStarRing.norm_star_mul_self (x:=A); rw [hp] at hx; nlinarith [norm_nonneg A]
variable (e:m≃n)
abbrev ingot (e:m≃n): Op n≃ₐ[ℝ] Op m:= reindexAlgEquiv ℝ ℂ e.symm
lemma ingot_star (A:Op n): ingot e (star A)=star (ingot e A):=rfl
lemma ingot_nonneg (A:Op n)(p:0≤A):0≤ ingot e A:=nonneg_iff_posSemidef.mpr ((nonneg_iff_posSemidef.mp p).submatrix e)
lemma ingot_le(A B:Op n)(p:A≤B): ingot e A ≤ ingot e B:=sub_nonneg.mp ((map_sub (ingot e) _ _ ▸ ingot_nonneg e (B-A) (sub_nonneg.mpr p)))
lemma safe_reindex (A:Op n)(p:Safe A):Safe (ingot e A):=by
  obtain ⟨hp,hx,hv⟩:= book_s A|>.mp p; apply book_s _|>.mpr
  exact ⟨by rw [isSelfAdjoint_iff,← ingot_star,hp],by simpa only [map_smul,map_one,map_mul] using ingot_le e _ _ hx,by simpa only [map_smul,map_one,map_mul] using ingot_le e _ _ hv⟩
lemma trace_move (A:Op n) : trR (ingot e A)=trR A:=by unfold trR; exact congrArg Complex.re (e.sum_comp (Matrix.diag A))
lemma sqrt_move (A:Op n)(p:0≤A) : CFC.sqrt (ingot e A)= ingot e (CFC.sqrt A):= by rw [CFC.sqrt_eq_iff _ _ (ingot_nonneg e _ p) (ingot_nonneg e _ (CFC.sqrt_nonneg _)),← map_mul,CFC.sqrt_mul_sqrt_self _ p]

variable {A: n→Op m}
abbrev tableS (A:n→Op m):Op (n×m):= jump (Equiv.refl n) A
lemma table_add (A B:n→ Op m): tableS (A+B)=tableS A+tableS B:=jump_add _ A B
lemma table_mul (A B:n→Op m) : tableS (A*B)= tableS A*tableS B:= by rw [tableS,tableS,tableS,jump_mul,Equiv.refl_trans]; rfl
lemma table_pow (A:n→Op m)(k:ℕ): tableS (A^k)= (tableS A)^k:=by induction k with|zero=>simp only [pow_zero]; apply jump_id| succ k ih=> rw [pow_succ,pow_succ,table_mul,ih]
lemma table_star (A:n→Op m): tableS (star A)=star (tableS A):=by rw [tableS,tableS,jump_star,Equiv.refl_symm]; rfl
lemma table_one: tableS (1:n→Op m)=1:= jump_id
lemma table_nonneg(p:∀ i,0 ≤ A i):0 ≤ tableS A:=by
  let B(i):= CFC.sqrt (A i); have he : tableS A=tableS B* star (tableS B):=by rw [←table_star,←table_mul]; apply congrArg; funext x; change A x=B x * star (B x); rw [show star (B x)=B x from (CFC.sqrt_nonneg _).star_eq]; exact (CFC.sqrt_mul_sqrt_self (A x) (p x)).symm
  rw [he]; exact mul_star_self_nonneg _
lemma table_safe (i:n)(p:Safe (tableS A)): Safe (A i):=by
  obtain ⟨hp,hx,hv⟩:=book_s _|>.mp p; have he(P:n→Op m):blockE i i (tableS P)=P i:=by rw [tableS,block_jump]; simp
  have hT(T U:Op (n×m))(h:T≤U): blockE i i T ≤ blockE i i U:=by
    apply sub_nonneg.mp; exact nonneg_iff_posSemidef.mpr ((nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).submatrix (i,·))
  have hb(c:ℝ): blockE i i (c • (1:Op (n×m)))= c • (1:Op m):=by rw [← table_one]; exact congrArg (c • ·) (show blockE i i (tableS (1:n→ Op m))=(1:Op m) from he 1)
  have hy:blockE i i (tableS A*tableS A)= (A i)*(A i):=by rw [← table_mul, he]; rfl
  have hx:=hT _ _ hx; have hv:= hT _ _ hv; rw [hb,hy] at hx hv
  exact book_s _|>.mpr ⟨by rw [isSelfAdjoint_iff]; nth_rw 2 [←he A]; rw [← hp.star_eq,← table_star,he]; rfl,hx,hv⟩ -- tune
omit [DecidableEq m] in
lemma trace_table (A:n→ Op m): trR (tableS A)=∑ i,trR (A i):=by rw [block_trace]; simp [tableS,block_jump]
lemma square_positive (A:Op n)(h:IsSelfAdjoint A): 0≤ A^2:=by rw [sq]; nth_rw 1 [←h.star_eq]; exact star_mul_self_nonneg _
lemma table_sqrt(A:n→Op m)(h:∀ i,0≤ A i): CFC.sqrt (tableS A)=tableS (fun i=>CFC.sqrt (A i)):=by rw [CFC.sqrt_eq_iff _ _ (table_nonneg h) (table_nonneg fun i=> CFC.sqrt_nonneg _),←table_mul]; apply congrArg; funext x; exact CFC.sqrt_mul_sqrt_self _ (h x)

section toll
variable [Nonempty m][Nonempty n]
lemma energy_turn (U:UNI n)(A:Op n)(p:Safe A): energy (twist U A)=energy A:=by
  rw [energy, ←projector_twist p, ← map_mul]; unfold trR; rw [Fock.trace_twist]; rfl -- p
lemma energy_ingot (A:Op n)(p:Safe A): energy (ingot e A)=energy A:= by rw [energy_eq p,energy_eq (safe_reindex e A p),trace_move,← map_pow,sqrt_move _ _ (square_positive A p.self),trace_move]
lemma energy_table (A:n→Op m)(p:Safe (tableS A)):energy (tableS A)= ∑ i,energy (A i):= by
  have h(i:n):0≤ (A^2) i:= square_positive (A i) (table_safe i p).self; rw [energy_eq p, ← table_pow, table_sqrt _ h]; simp_rw [trace_table,energy_eq (table_safe _ p)]; simp_rw [←sum_div,sum_add_distrib]; rfl
end toll
end YM.CF.Fixed.Bulk
