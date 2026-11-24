import YM.CF.Fixed.Lyrebird

/-! Fourier transform after writing (Tri×Slot) × Stage. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll SU Bulk
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev Tri(N:Side) := Fin 3→Per N
abbrev paste(z:Per N)(x:Tri N) : Site N:= Fin.cons z x
lemma paste_eq {i j : Per N} {x y : Tri N}: paste i x=paste j y ↔ i=j∧x=y:=by
  constructor
  · intro h; exact ⟨congrFun h 0,(by funext i; simpa [paste] using congrFun h i.succ)⟩
  rintro ⟨rfl,rfl⟩; rfl
lemma advance_time (z:Per N)(x:Tri N) : advance (N:=N) 0 (paste z x)= paste (plusTime _ z) x:=by funext i; refine Fin.cases ?_ (fun j=>?_ ) i <;> simp [paste,advance,plusTime];
def view (N:Side)(j:Fin 3) : Equiv.Perm (Tri N):= Equiv.addRight (Fin.tail (step j.succ : Site N))
lemma advance_tri (z:Per N)(x:Tri N)(j:Fin 3): advance (N:=N) j.succ (paste z x)= paste z (view _ j x):=by funext i; refine Fin.cases ?_ (fun k=> ?_) i <;> simp [paste,advance,view, Ne.symm (Fin.succ_ne_zero j), Fin.tail];
abbrev Ion (N : Side) := Tri N × Slot
abbrev Plank (N: Side):= Ion N × Stage N
def relate (N:Side): Plank N≃ Model N where
  toFun x:=(paste x.2.1 x.1.1,x.2.2,x.1.2)
  invFun x:=((Fin.tail x.1,x.2.2),(x.1 0,x.2.1))
  left_inv x:=by simp [paste]
  right_inv x:=by simp [paste]
lemma tri_card (N:Side) : Fintype.card (Tri N)=N.val^3 := by unfold Tri; simp [Per,ZMod.card]
-- reuse d8 frequencies with zero-time offset
abbrev zmom(k:Tri N):Three:=fun i=>principal (k i)
def f_tri(x y:Tri N):ℂ:=frequency (paste 0 y) (paste 0 x)
lemma fh_unit(x y:Tri N): star (f_tri x y)*f_tri x y=1:= frequency_unit ..
lemma fh_op(x y:Tri N)(i:Fin 3): trunkZ (x i)* f_tri (view _ i x) y=f_tri x y* phase (zmom y i):=by
  have he:=frequency_hop (paste 0 y) (paste 0 x) i.succ; rw [show paste 0 x+step i.succ=_ from advance_tri _ _ _,seam,anticut] at he; unfold zmom f_tri trunkZ; simpa only [paste,Fin.cons_succ,pm,Function.comp_apply] using he -- tune zero cast
lemma fop_ne (x y:Tri N)(h:x≠y): ∑ i,star (f_tri i x)*f_tri i y=0:=by
  obtain ⟨i,hi⟩:= Function.ne_iff.mp h
  let X:=phase (zmom x i); let Y:=phase (zmom y i); let F(u):=star (f_tri u x)*f_tri u y; let K:=view N i
  have hx(t:Tri N):F (K t)= star X *Y* F t:=by
    let u:=trunkZ (t i); have hu: star u*u=1:=by unfold u trunkZ; split_ifs<;>simp
    change _= _; rw [show F (K t)= star (u*f_tri (K t) x)*(u*f_tri (K t) y) from ?_,show u*f_tri (K t) x=f_tri t x*X from fh_op ..,show u*f_tri (K t) y=f_tri t y*Y from fh_op ..]; rw [star_mul]; unfold F; ring
    rw [star_mul]; unfold F; linear_combination (norm:=ring) -(star (f_tri (K t) x)*f_tri (K t) y)* hu -- tune sign
  have he:=Equiv.sum_comp K F; simp only [hx, ←Finset.mul_sum] at he; by_contra hs; have hh: star X * Y=1:=mul_right_cancel₀ (show _ from hs) (by rw [one_mul]; exact he) -- tune
  apply hi (phase_inj (x i) (y i) ?_); change X=Y; rw [← one_mul Y, ← show X*star X=1 from phase_one _,mul_assoc,hh,mul_one]

abbrev fscalar (N:Side):= Real.sqrt ((N.val:ℝ)^3)
def spaceF (N: Side): Op (Tri N) := fun x k=> f_tri x k / (fscalar N:ℂ)
lemma space_U (N:Side): spaceF N∈ unitary (Op (Tri N)):=by
  apply Matrix.mem_unitaryGroup_iff'.mpr; ext x y; simp only [Matrix.mul_apply,Matrix.star_apply,spaceF,star_div₀,show star (fscalar N:ℂ)=(fscalar N:ℂ) from Complex.conj_ofReal _,div_mul_div_comm, ←Finset.sum_div]; by_cases h:x=y
  · subst y; simp_rw [fh_unit]; have he:0<(N.val:ℝ):=by exact_mod_cast N.property
    unfold fscalar
    rw [←Complex.ofReal_mul,←sq,Real.sq_sqrt (by positivity : 0 ≤ (N.val:ℝ)^3),sum_const,card_univ,tri_card,nsmul_eq_mul,Nat.cast_pow,mul_one,Complex.ofReal_pow,Complex.ofReal_natCast,div_self (by exact pow_ne_zero _ (by exact_mod_cast N.property.ne')),Matrix.one_apply_eq] -- tune fscalar reducible
  rw [fop_ne x y h,zero_div]; exact (Matrix.one_apply_ne h).symm

def mainF (N: Side) : UNI (Plank N) := ⟨ (spaceF N⊗ₖ (1:Op Slot))⊗ₖ (1:Op (Stage N)), Matrix.kronecker_mem_unitary (Matrix.kronecker_mem_unitary (space_U _) (unitary _|>.one_mem)) (unitary _|>.one_mem) ⟩
abbrev ion (A:Op (Model N)):= ingot (relate N) A
abbrev Vega (N:Side) := Ion N→ Op (Stage N)
abbrev UΦ (A: Op (Plank N)):= twist (mainF N) A
def frameZ (N:Side) : (Ion N→ Op (Stage N)) →ₐ[ℝ] Op (Plank N) where
  toFun X:=UΦ (tableS X)
  map_one':= by rw [table_one]; exact map_one _
  map_zero':= by have h: tableS (0:Vega N)=0:=by ext ⟨i,j⟩ ⟨k,l⟩; simp [jump_apply,tableS]
                 rw [h]; exact map_zero _
  map_add' a b:= (congrArg UΦ (table_add ..)).trans (map_add ..)
  map_mul' a b:= (congrArg UΦ (table_mul a b)).trans (map_mul ..)
  commutes' c:=by
    simp_rw [Algebra.algebraMap_eq_smul_one]; unfold UΦ; rw [show tableS (c • (1:Vega N))= c•1 from ?_, map_smul]; change c • (twist _ 1)= _; rw [map_one]
    ext i j; simp [tableS,jump_apply, Matrix.one_apply ,Prod.ext_iff]; split_ifs <;> tauto
lemma frameZ_star (A:Vega N): frameZ N (star A)=star (frameZ N A):= by change twist _ (tableS _)=_; rw [table_star, map_star]; rfl
lemma horizontal (x y:Tri N)(i j:Slot) : blockE (x,i) (y,j) (mainF N).val= if i=j then spaceF N x y • (1:Op (Stage N)) else 0:=by ext t u; by_cases h:i=j <;> simp [blockE, mainF,h]
lemma staticZ (A:Op (Stage N)):tableS (fun _ : Ion N=> A)= frameZ N (fun _=> A) := by
  let X:= tableS (fun _ : Ion N=> A); let F:= mainF N
  apply Eq.symm; change twist F X=X; apply Mir.twist_comm; unfold F X; rw [tableS, jump_replicate,mainF,op_kron_mul,op_kron_mul]; simp -- X reducible?
end YM.CF.Fixed.Rift
