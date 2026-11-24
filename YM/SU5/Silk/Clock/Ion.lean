import YM.SU5.Silk.Clock.Gyre
import YM.CF.Ione.Crore
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Ione.Clock
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section
variable {N:Type*}[Fintype N][DecidableEq N]

def Column(A:Op N):Prop:=∀ x y z, A x y≠0→ A z y≠0→ x=z
lemma nice_eq (A:UNI N)(h:Column A.val):∃ f:Equiv.Perm N,∀ i j,A.val i j ≠0 →i=f j:=by
 have hu(i):∃ j,A.val j i≠0:=by
    by_contra! e; have hp:= Matrix.ext_iff.mpr (show star A.val*A.val=1 from A.property.1) i i; simp [Matrix.mul_apply,e] at hp
 choose f hf using hu
 have hx(i j)(u:A.val i j≠0):i=f j:=h i j (f j) u (hf j)
 have hs:Surjective f:=by
    intro i; by_contra! u; have he(j):A.val i j=0:=Classical.byContradiction fun w=>u j (hx i j w).symm
    have hp:=Matrix.ext_iff.mpr (show A.val*star A.val=1 from A.property.2) i i; simp [Matrix.mul_apply,he] at hp
 exact ⟨Equiv.ofBijective f (hs.bijective_of_finite),hx⟩

end
variable {N:Type*}[Fintype N][LinearOrder N]
lemma distill_l (A:UNI N)(h:Column A.val):Column (quant A.val):=by
 obtain ⟨f,h⟩:=nice_eq A h
 have hv(i j:Finset N)(x:quant A.val i j≠0): i=j.map f.toEmbedding:=by
    let t:=j.map f.toEmbedding; have hz: i⊆t:=by
      by_contra k; have hP:= Matrix.ext_iff.mpr (roof_x t j A.val (fun i j' u=>by specialize h i j' u; rw [h]; exact Finset.mem_map_equiv.trans (by simp))) i j; rw [cutM,cutM, Matrix.diagonal_mul, Matrix.mul_diagonal,if_neg (mt mem_powerset.mp k), if_pos (mem_powerset.mpr Subset.rfl),zero_mul,mul_one] at hP; exact x hP.symm
    apply Finset.eq_of_subset_of_card_le hz; rw [card_map]; exact le_of_eq (Eq.symm (Classical.byContradiction fun w=> x (quant_grade _ _ _ w)))
 intro x y z i j; rw [hv x y i,hv z y j]

abbrev gLo:SpinIdx→ℂ:=![1,1,-1,-1]
abbrev gInf:SpinIdx→ℂ:=![Complex.I,-Complex.I,Complex.I,-Complex.I]
lemma grad_eq: grading=diagonal gLo:=by ext i j; fin_cases i<;>fin_cases j<;>norm_num [grading,diagonal,gLo]
lemma inf_eq: gammaOp 0*gammaOp 1=diagonal gInf:=by ext i j; fin_cases i<;>fin_cases j<;>norm_num [gammaOp,diagonal,gInf,Matrix.mul_apply, Fin.sum_univ_succ,SpinIdx]
lemma sup_eq: gammaOp 2*gammaOp 3=diagonal ![-Complex.I,Complex.I,Complex.I,-Complex.I]:=by
 rw [show (3:Axis)=Fin.succ (Fin.succ (Fin.succ 0)) from rfl, show (2:Axis)=Fin.succ (Fin.succ 0) from rfl]; simp only [gammaOp,Matrix.cons_val_succ,Matrix.cons_val_zero]; ext i j; fin_cases i<;>fin_cases j<;>norm_num [diagonal,Matrix.mul_apply,Fin.sum_univ_succ,SpinIdx]
lemma phase_unique(x y:SpinIdx)(h:gLo x=gLo y)(z:gInf x=gInf y):x=y:= by
 have hv:=congrArg Complex.im z
 fin_cases x<;>fin_cases y<;>first|rfl| (solve | norm_num [gLo,gInf] at h| norm_num [gLo,gInf] at hv)
lemma group_product(a b:Axis)(h:stripe a=stripe b)(v:a≠b): ∃ z:SpinIdx→ℂ,gammaOp a*gammaOp b=diagonal z:=by
 suffices t: (a=0∧b=1) ∨ (a=1∧b=0) ∨ (a=2∧b=3) ∨ (a=3∧b=2) by
    rcases t with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨_,inf_eq⟩
    · rw [gammaSwap _ _ v,inf_eq]; exact ⟨_,diagonal_neg ..⟩
    · exact ⟨_,sup_eq⟩
    rw [gammaSwap _ _ v,sup_eq]; exact ⟨_,diagonal_neg ..⟩
 revert a b; decide

lemma equiv_column (A:UNI N)(X Y:N→ℂ)(t:twist A (diagonal X)=diagonal Y)(i j k:N)(p:A.val i j≠0)(q:A.val k j≠0):Y i=Y k:=by
 have hx:= twist_product A (diagonal X); rw [t] at hx
 have h(l:N)(p:A.val l j≠0): Y l=X j:=by apply mul_right_cancel₀ p; rw [mul_comm (X j)]; simpa only [diagonal_mul,mul_diagonal] using Matrix.ext_iff.mpr hx l j
 exact (h _ p).trans (h _ q).symm

-- spin comp rotates γ even. Need no irrational bounds.
lemma spinning (p:Signed)(hp:p∈ Loomed)(U:UNI SpinIdx)(t:JetS p false (detX p) U): Column U.val:=by
 intro i j k a b
 apply phase_unique
 · have h:twist U grading=hush (detX p) grading:= t.grade
   rw [grad_eq] at h; cases q:detX p<;>rw [q] at h
   · exact equiv_column U _ _ h i j k a b
   rw [hush_true,diagonal_neg] at h; simpa using equiv_column U _ _ h i j k a b
 obtain ⟨u,h⟩:= group_product _ _ (color_l p hp 0 1 (by decide)) (p.perm.injective.ne (by decide: (0:Axis)≠1))
 have he: twist U (diagonal u) = hush (p.flip 0) (gammaOp 0) * hush (p.flip 1) (gammaOp 1):=by rw [←h,map_mul]; exact congrArg₂ _ (t.cliff _) (t.cliff _)
 cases q:p.flip 0<;>cases g:p.flip 1<;> simp only [q,g,hush_false,hush_true,neg_mul,mul_neg,neg_neg,inf_eq,diagonal_neg] at he<;> simpa only [Pi.neg_apply, neg_inj] using equiv_column U _ _ he i j k a b

open Hake Laic Stilo Pastry Urn Scree Vow Levier Skye
lemma prep_column (N:Side)(p:Shape)(b:Bool)(U:UNI SpinIdx)(h:Column U.val): Column (siteU p b U N).val:=by
 let V:= Tofu p N; let W: Site N→Op (SpinIdx×Slot):=fun x=>(milU p U (xtra b) x).val
 have he(x y:Site N)(i j:SpinIdx)(u v:Slot)(w:(siteU p b U N).val ((x,i),u) ((y,j),v)≠0):V x=y ∧ U.val i j≠0 ∧ u=v:=by
    change jump V W (x,i,u) (y,j,v)≠0 at w; rw [jump_apply] at w; split at w; swap; exact False.elim (w rfl)
    refine ⟨‹_›,?_⟩; have hx:(U.val ⊗ₖ (1:Op Slot)) (i,u) (j,v)≠0:=fun q=> w (by change p.payA x * _=0; rw [show (spinQ U (xtra b)).val (i,u) (j,v)= 0 from q,mul_zero]); simp only [kroneckerMap_apply,one_apply] at hx; exact ⟨left_ne_zero_of_mul hx,Classical.byContradiction fun t=> hx (by simp [t])⟩
 rintro ⟨⟨x,i⟩,u⟩ ⟨⟨y,j⟩,v⟩ ⟨⟨z,k⟩,w⟩ p1 p2; obtain ⟨a,b,t⟩:=he _ _ _ _ _ _ p1; obtain ⟨c,d,f⟩:=he _ _ _ _ _ _ p2; exact Prod.ext (Prod.ext (V.injective (a.trans c.symm)) (h _ _ _ b d)) (t.trans f.symm)

lemma spice_column (U:UNI N)(h:Column U.val)(b:Bool): Column (spice U b).val:=by
 have ht(t w:Bool)(i j:N)(p:(spice U b).val (t,i) (w,j)≠0): t=w.xor b ∧ U.val i j≠0:=by
    rw [cream] at p; split at p; exact ⟨‹_›, mt (spice_E U b (t,i) (w,j)) (by rw [cream,if_pos ‹_›]; exact p)⟩; exact False.elim (p rfl)
 rintro ⟨a,x⟩ ⟨c,y⟩ ⟨d,z⟩ p q; obtain ⟨g,k⟩:= ht _ _ _ _ p; obtain ⟨f,r⟩:= ht _ _ _ _ q; exact Prod.ext (g.trans f.symm) (h _ _ _ k r)

open scoped Classical
lemma column_spin {n:Side}(p:Sweep n)(hp:p∈Whirl n):Column (hail_Q p).val:=by
 obtain ⟨e,t,s⟩:=p; obtain ⟨rfl,q⟩:s=false ∧ e∈ Loomed:=hp
 exact distill_l (praise _) (spice_column (siteU ..) (prep_column _ _ _ _ (spinning _ q _ (spinZ ..))) _)

lemma fee_column{n:Side}(s:Sweep n)(hs:s∈Whirl n)(i:Finset (Dwell n)): (∑ j:Finset (Dwell n),‖(hail_Q s).val j i‖) ≤ 1:=by
 obtain ⟨f,h⟩:=nice_eq (hail_Q s) (column_spin s hs)
 rw [sum_eq_single (f i)]
 · exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (hail_Q s).property).le
 · intro j _ p; rw [show (hail_Q s).val j i=0 from Classical.byContradiction fun w=>p (h _ _ w),norm_zero]
 simp
end YM.CF.Ione.Clock
