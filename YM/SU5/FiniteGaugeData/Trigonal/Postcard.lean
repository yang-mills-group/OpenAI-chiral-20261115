import YM.SU5.FiniteGaugeData.Trigonal.Tivolian
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option linter.unusedSimpArgs false
namespace YM.CF.Window.Trigo
open Function Filter Finset Metric
open Laurent Lattice Next.Free Bloch Fir Lat ArchiveK Largo WithLp MeasureTheory Complex
open scoped Topology BigOperators Set Pointwise InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra μFin
set_option quotPrecheck false
section
-- arbitrary ladder layout w target rows/cols. Kernel tax.
abbrev TaxR {X Y:Type*}(g:X→Y→ℂ){n:ℕ}(x:Fin n→X)(y:Fin n→Y):= (Matrix.of fun i j=>g (x i) (y j))
variable {X Y:Type*}(g:X→Y→ℂ){n:ℕ}(x:Fin n→X)(y:Fin n→Y) (v:(TaxR g x y).det≠0)
def FundPole {X Y:Type*}(g:X→ Y→ℂ):Prop:= ∀ (S:Finset X) (f:X→ℂ), (∀ y:Y, ∑ i∈S,f i*g i y=0)→∀ i∈S,f i=0
lemma TicketL(v:(TaxR g x y).det≠0): Injective x∧ Injective y:= by
 constructor <;> intro i j p <;> by_contra t; exact v (Matrix.det_zero_of_row_eq t (by ext z; simp [TaxR,p])); exact v (Matrix.det_zero_of_column_eq t (fun z=>by simp [TaxR,p]))
local notation "Ξ"=> finSumFinEquiv
abbrev braid {X:Type*}{n:ℕ}(x:Fin n→X)(y:X): Fin (n+1)→X:= Sum.elim x (fun _:Fin 1=>y) ∘ finSumFinEquiv.symm
include v
lemma ping (t:FundPole g)(r:X)(hp:r∉ Set.range x): ∃ z:Y, (TaxR g (braid x r) (braid y z)).det≠0:= by
 classical
 by_contra! h
 let A:=TaxR g x y; let B(z:Y): Matrix (Fin n) (Fin 1) ℂ:=Matrix.of fun i _=> g (x i) z; let C':Matrix (Fin 1) (Fin n) ℂ:=Matrix.of fun _ j=>g r (y j)
 letI:= (show IsUnit A from (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.mpr v)).invertible; let H:= C'*⅟A; let p(i:Fin n):= H 0 i
 have hf(z:Y): g r z = ∑ i:Fin n,p i*g (x i) z:=by
    let X:Matrix (Fin 1) (Fin 1) ℂ:= !![g r z]; let E:= Matrix.fromBlocks A (B z) C' X; have he: E.submatrix finSumFinEquiv.symm finSumFinEquiv.symm= TaxR g (braid x r) (braid y z):=by
       ext i j; unfold Matrix.submatrix TaxR braid E; simp only [Matrix.of_apply, Function.comp_apply]; cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> first| rfl | simp [X, Fin.eq_zero]
    have hx:= Matrix.det_submatrix_equiv_self (A:=E) finSumFinEquiv.symm; rw [he,h] at hx; unfold E at hx; rw [Matrix.det_fromBlocks₁₁] at hx; have hu:=(mul_eq_zero.mp hx.symm).resolve_left v; rw [Matrix.det_fin_one] at hu; exact sub_eq_zero.mp hu
 let S:= univ.image x; have hk:r∉S:=fun h=> False.elim (hp ((mem_image.mp h).imp fun x=> And.right)); let φ(i:X):ℂ:= if r=i then 1 else ∑ j:Fin n, if x j=i then -p j else 0
 have hj(i:Fin n):φ (x i)= -p i:=by unfold φ; rw [if_neg (fun z=>hp ⟨i,z.symm⟩),sum_eq_single i]; simp; intro j _ t; rw [if_neg ((TicketL g x y v).1.ne t)]; simp
 apply one_ne_zero (show (1:ℂ)=0 from (show φ r=1 from if_pos rfl) ▸ t (insert r S) φ ?_ r (mem_insert_self ..)); intro y'; rw [sum_insert hk,show φ r=1 from if_pos rfl,one_mul, hf,sum_image]; swap; · exact (TicketL g x y v).1.injOn
 simp_rw [hj,neg_mul,sum_neg_distrib,add_neg_cancel]
-- extend covers by any finite set, guarantee determinant and old rows/cols included. Clock layout chosen BEFORE estimating. Others arbitrary.
omit v in
private lemma histori {m:ℕ}{V:Type*}(x:Fin m→ V)(a:V):Set.insert a (Set.range x) ⊆ Set.range (braid x a):=by
 rintro i (p |⟨j,rfl⟩); · exact ⟨finSumFinEquiv (Sum.inr (0:Fin 1)),by simp [braid,(show i=a from p)]⟩
 exact ⟨finSumFinEquiv (Sum.inl j),by simp [braid]⟩
lemma xen (t:FundPole g)(A:Finset X): ∃ (m:ℕ)(X':Fin m→X)(Y':Fin m→Y), (TaxR g X' Y').det ≠0 ∧ Set.range x ⊆ Set.range X' ∧ Set.range y ⊆ Set.range Y' ∧ ↑A ⊆ Set.range X':=by
 classical
 induction A using Finset.induction_on with
 | empty=> exact ⟨n,x,y,v,(fun _ h=>h),(fun _ h=>h),by simp⟩
 | insert a u h ih=>
    obtain ⟨m,X',Y',d,w,b,u'⟩:= ih; by_cases p:a∈Set.range X'; · exact ⟨m,X',Y',d,w,b,by simpa using Set.insert_subset p u'⟩
    obtain ⟨z,hᵥ⟩:= ping g X' Y' d t a p

    exact ⟨m+1,braid X' a,braid Y' z,hᵥ,w.trans ((Set.subset_insert ..).trans (histori ..)), b.trans ((Set.subset_insert ..).trans (histori ..)), by rw [Finset.coe_insert]; exact (Set.insert_subset_insert u').trans (histori ..)⟩
omit v
lemma CostedPole : FundPole levy ∧ FundPole (flip levy):= by
 constructor <;> intro S f p
 · exact bytes true S ∅ f fun i _=> p i
 apply bytes false S ∅ f; intro i t; apply neg_injective; rw [←sum_neg_distrib,neg_zero]; simp_rw [←mul_neg,←per_sum]; exact p _
theorem augmented (S:Finset (Chamber true))(T:Finset (Chamber false)): ∃ (n:ℕ)(X:Fin n→Chamber true)(Y:Fin n→Chamber false), Injective X ∧ Injective Y ∧ (TaxR levy X Y).det ≠0 ∧ ↑S ⊆ Set.range X ∧ ↑T ⊆ Set.range Y:=by
 let X':Fin 0→ Chamber true:=Fin.elim0; let Y':Fin 0→ Chamber false:=Fin.elim0
 obtain ⟨m,x,y,d,_,_,h⟩:=xen levy X' Y' (by simp) CostedPole.1 S; obtain ⟨n,Y,X,v,u,g,w⟩:=xen (flip levy) y x ((Matrix.det_transpose _).trans_ne d) CostedPole.2 T; have ht: (TaxR levy X Y).det≠0:=(Matrix.det_transpose (TaxR levy X Y)).symm.trans_ne v; exact ⟨n,X,Y,(TicketL levy X Y ht).1,(TicketL levy X Y ht).2,ht,h.trans g,w⟩
#print axioms augmented
end
end YM.CF.Window.Trigo
