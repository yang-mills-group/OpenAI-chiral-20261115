import YM.CF.Fixed.ShellAngle
/-! All four anti seam count; true t² log cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dais.Span
open Function Filter Lattice Next.Free Finset Fock SU Lat Laurent Metric MeasureTheory Cube Scroll Phase Peaks Paige Spire Vault Ember
open Jill Kea Fixed.Extensive
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
def dialN(x:Per N):ℕ:= min (x.val+1) (N.val-x.val)
lemma d_pos(x:Per N):0 < dialN x:=by unfold dialN; exact lt_min (Nat.zero_lt_succ x.val) (Nat.sub_pos_of_lt (ZMod.val_lt _))
lemma d_le(x:Per N): dialN x ≤ N.val:= (min_le_right ..).trans (Nat.sub_le ..) -- tune
lemma swing(x:Per N) : ((dialN x:ℕ):ℝ)/N.val ≤ |Lat.principal x|:=by
 have he:1≤Real.pi:=by linarith only [Real.pi_gt_three]
 have hg:= nPos N
 unfold Lat.principal; split
 next h=>
    apply le_trans _ (le_abs_self _); unfold winding; have hv: (dialN x:ℝ) ≤ x.val+1:=by exact_mod_cast (min_le_left (x.val+1) (N.val-x.val)); -- tune lhs abbrev
    apply le_trans _ (le_mul_of_one_le_right (by positivity) he); gcongr; linarith [Nat.cast_nonneg (α:=ℝ) x.val]
 next h=>
    apply le_trans _ (neg_le_abs _); apply le_trans (b:=tauR N.val x.val); swap
    · unfold winding; let A:ℝ:=N.val; let k:ℝ:=x.val; refine (le_mul_of_one_le_left (interval_right x).1.le he).trans ?_
      unfold tauR; field_simp
      have hh:(x.val:ℝ)+1≤ N.val:=by exact_mod_cast ZMod.val_lt x
      nlinarith
    unfold tauR
    apply div_le_div_of_nonneg_right _ hg.le; rw [← Nat.cast_sub (ZMod.val_lt x).le]; exact_mod_cast min_le_right (x.val+1) (N.val-x.val)
private lemma min_frame (k:ℕ) : (univ.filter fun j:Per N=> dialN j ≤ k).card ≤ 2*k:=by
 let A:=univ.filter (fun j:Per N=>j.val<k); let B:=univ.filter (fun j:Per N=>N.val-j.val≤k); let D:= (univ.filter fun j:Per N=> dialN j ≤k); have he:D⊆ A∪ B:=by intro j h; have hp:= (mem_filter.mp h).2; rw [dialN,min_le_iff] at hp; simp [A,B]; omega
 apply (card_le_card he).trans; apply (card_union_le ..).trans; rw [two_mul]; apply add_le_add
 · rw [← card_range k]; exact card_le_card_of_injOn (fun j:Per N=>j.val) (fun j h=> mem_range.mpr (mem_filter.mp h).2) (ZMod.val_injective _).injOn
 rw [←card_range k]; refine card_le_card_of_injOn (fun j:Per N=> N.val-j.val-1) (fun j h=> ?_) ?_
 · apply mem_range.mpr; have he:= (mem_filter.mp h).2; have hv:= j.val_lt; dsimp only; omega
 intro i hi j hj t; apply ZMod.val_injective; have he:=i.val_lt; have hp:=j.val_lt; dsimp only at t; omega
abbrev reaches(v:Site N)(i:Axis):= dialN (v i)
def Height (i:Axis)(x:Per N):Finset (Site N):= univ.filter (fun j=> j i=x∧∀ l,reaches j l≤dialN x)
lemma height_charge(i:Axis)(x:Per N):(Height i x).card ≤ (2*dialN x)^3:=by
 let A:=univ.filter (fun j:Per N=>dialN j≤dialN x); let B:= Height i x; let e:=Equiv.piSplitAt i (fun (_:Axis)=> Per N); -- subtype card
 let f (j:↥B) (l:{l:Axis//l≠i}):A:= ⟨(j.val l.val),(mem_filter.mpr ⟨mem_univ _,(mem_filter.mp j.property).2.2 _⟩)⟩; have h:f.Injective:=by
    intro a b k; apply Subtype.ext; funext l; by_cases h:l=i; · subst l; exact (mem_filter.mp a.property).2.1.trans ((mem_filter.mp b.property).2.1.symm)
    exact congrArg Subtype.val (congrFun k ⟨l,h⟩)
 refine le_trans (b:=A.card^3) ?_ (Nat.pow_le_pow_left (min_frame _) _); apply (Fintype.card_coe _).ge.trans; apply (Fintype.card_le_of_injective _ h).trans_eq; rw [Fintype.card_fun, Fintype.card_coe, show Fintype.card {l:Axis// l≠i}=3 from ?_ ]; rw [Fintype.card_subtype_compl]; simp [Axis]
lemma tall_le(v:Site N): ∃ i:Axis,v∈ Height i (v i):=by obtain ⟨j,h,t⟩:= exists_max_image univ (reaches v) univ_nonempty; exact ⟨j,mem_filter.mpr ⟨mem_univ _,rfl,fun l=> t l (mem_univ _)⟩⟩
abbrev streetN(x:Per N):= (N.val:ℝ)/dialN x
lemma roll(v:Site N)(j:Axis): (‖pm v‖^2)⁻¹ ≤ streetN (v j)^2:=by
 have hp:0<(dialN (v j):ℝ):=by exact_mod_cast d_pos (v j)
 have hg:= nPos N
 let x:=(v j); have hh: 0 < (dialN x:ℝ)/N.val:=div_pos hp hg
 calc
 _ ≤ (((dialN x:ℝ)/N.val)^2)⁻¹:= inv_anti₀ (pow_pos hh _) (pow_le_pow_left₀ hh.le ((swing x).trans (show _ ≤ _ from b_abs (pm v) j)) _)
 _ = _:=by unfold streetN; rw [← inv_pow, inv_div] -- tune x
private lemma sumH {I J:Type*}[DecidableEq I][DecidableEq J](S:Finset I)(P:I→Finset J){f:J→ℝ}(h:∀ x,0≤f x) : ∑ j ∈ S.biUnion P,f j ≤∑ i∈ S, ∑ j∈ P i,f j:=by induction S using Finset.induction_on with| empty=> simp|@insert i t ht ih=>rw [Finset.biUnion_insert,sum_insert ht]; linarith only [sum_union_inter (s₁:=P i) (s₂:= t.biUnion P) (f:=f), ih, sum_nonneg (s:=P i∩ t.biUnion P) (fun i _=>h i)]
lemma corner : ∑ v:Site N,(‖pm v‖^2)⁻¹ ≤ (32:ℝ)*N.val^4:=by
 let f(v:Site N):=(‖pm v‖^2)⁻¹; let P(i:Axis)(j:Per N):= Height i j; have hx: (univ:Finset (Site N))⊆univ.biUnion fun i:Axis=>univ.biUnion fun x:Per N=> Height i x:=fun v _=>by obtain ⟨i,h⟩:=tall_le v; exact mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨v i,mem_univ _,h⟩⟩
 have hg: (0:ℝ) < N.val:=nPos N; have hf(v:Site N):0≤f v:=inv_nonneg.mpr (sq_nonneg _)
 let A:=(N.val:ℝ); have ht(i:Axis)(j:Per N): ∑ x ∈ P i j,f x ≤ 8*A^3:=by
    refine (sum_le_sum (g:=fun _=>streetN j^2) (fun v t=> ?_)).trans ?_
    · exact (mem_filter.mp t).2.1 ▸ roll v i
    let H:=(dialN j:ℝ); have h₀: 0<H:= Nat.cast_pos.mpr (d_pos j); rw [sum_const,nsmul_eq_mul]; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (height_charge i j)) (sq_nonneg _)) ?_; push_cast; change (2*H)^3*(A/H)^2 ≤ 8*A^3; have hA: H ≤ A:= Nat.cast_le.mpr (d_le j); calc
       _ = 8*A^2*H:=by field
       _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hA (sq_nonneg A)]
 let y(i:Axis):=univ.biUnion (P i); refine (sum_le_sum_of_subset_of_nonneg hx (fun x _ _=> hf x)).trans ((sumH _ _ hf).trans ?_)
 refine (sum_le_sum (fun i _=>(sumH _ _ hf).trans (sum_le_sum (fun j _=> ht i j)))).trans_eq ?_; simp_rw [sum_const,card_univ,Fintype.card_fin,ZMod.card,nsmul_eq_mul]; unfold A; ring
end YM.CF.Dais.Span
#print axioms YM.CF.Dais.Span.corner
