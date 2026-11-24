import YM.SU5.FiniteGaugeData.Lycan.Feld
import YM.SU5.FiniteGaugeData.Trigonal.Postcard
/-! # Wick equals determinant, preserving ordering of every pair. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Fock.Reduction.Lycan
set_option linter.unusedSimpArgs false
open Function Filter Matrix Finset
open scoped Topology Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {X Y:Type*}{n:ℕ}(F:X→Y→ℂ)
abbrev roman {X Y:Type*}(F:X→Y→ℂ){n:ℕ}(f:Fin n→ X ×Y): Op (Fin n):= Window.Trigo.TaxR F (Prod.fst ∘ f) (Prod.snd ∘ f)
private lemma piece (u:Fin n)(M:Op (Fin (n+1))): let j:=u.succ; let t:= Equiv.swap 0 j
 (-1:ℂ)^(j:ℕ)*M 0 j*(M.submatrix Fin.succ j.succAbove).det= -(M 0 j*(M.submatrix Fin.succ (⇑t ∘ Fin.succ)).det):=by
 intro j t; let Q:=M.updateRow 0 (Pi.single j (M 0 j)); let x:= Q.submatrix id t; have he: x.det = -Q.det:=by rw [det_permute' t Q, Equiv.Perm.sign_swap (Ne.symm (Fin.succ_ne_zero u))]; simp
 have hp: Q.det=(-1:ℂ)^(j:ℕ)*M 0 j*(M.submatrix Fin.succ j.succAbove).det:=by
    rw [det_succ_row_zero, sum_eq_single j]; · unfold Q; rw [updateRow_self, Pi.single_eq_same]; congr 1
    · intro i h p; unfold Q; simp only [updateRow_self, Pi.single_eq_of_ne p,mul_zero,zero_mul]
    exact fun v=> (v (mem_univ j)).elim
 have hz: x.det=M 0 j * (M.submatrix Fin.succ (⇑t ∘ Fin.succ)).det:=by
    unfold x; rw [det_succ_row_zero, sum_eq_single 0];
    · simp only [Fin.val_zero, pow_zero,submatrix_apply,id_eq,Q,Fin.succAbove_zero, updateRow_self, t,Equiv.swap_apply_left,Pi.single_eq_same,one_mul]; congr 1
    · intro i _ q; have hi:t i≠j:= (show t 0=j from Equiv.swap_apply_left ..) ▸ t.injective.ne q
      simp only [submatrix_apply,id_eq,Q,updateRow_self,Pi.single_eq_of_ne hi,mul_zero,zero_mul]
    exact fun v=> (v (mem_univ _)).elim
 rw [←hp,←hz,he,neg_neg]
-- list price update
abbrev swapY (f:Fin n→ X×Y)(b:Y)(i:Fin n): Fin n→ X×Y:= update f i ((f i).1,b)
private lemma sli (f:Y→ℂ)(y:Y)(s:Fin n→ X ×Y)(T:List (X×Y)→ℂ): slid f y T (List.ofFn s)= ∑ i:Fin n, f (s i).2*T (List.ofFn (swapY s y i)):=by
 induction n generalizing T with| zero=> simp [slid]| succ n h=>
 let t:Fin n→ X×Y:= s ∘ Fin.succ; let p:X:=(s 0).1; let q:=(s 0).2; let L:= List.ofFn t
 have he(i':Fin n): List.ofFn (swapY s y i'.succ)=(p,q)::List.ofFn (swapY t y i'):=by
    rw [List.ofFn_succ]; refine congrArg₂ List.cons ?_ ?_; · exact update_of_ne (Ne.symm i'.succ_ne_zero) ..
    refine congrArg List.ofFn ?_; funext j; by_cases k:j=i'; · simp_rw [k,swapY,update_self]; rfl
    simp only [swapY, update_of_ne k, update_of_ne (Fin.succ_injective _|>.ne k)]; rfl -- tune
 have hv: List.ofFn (swapY s y 0)=(p,y)::L:=by
    rw [List.ofFn_succ]; refine congrArg₂ List.cons ?_ ?_; · exact update_self ..
    refine congrArg List.ofFn ?_; funext i; exact update_of_ne (i.succ_ne_zero) ..
 rw [List.ofFn_succ, Fin.sum_univ_succ, hv]; simp_rw [he]; change slid f y T ((p,q)::L)=_; rw [slid]; exact congrArg (f q*T ((p,y)::L)+·) (h t _)
lemma sweet (s:Fin n→ X ×Y): Album F (List.ofFn s)=(roman F s).det:=by
 induction n with
 | zero=> exact (show Album F []=(1:ℂ) from rfl) |>.trans (by simp) -- ofFn def?
 | succ n ih=>
    let t: Fin n→X×Y:= fun i=> s i.succ; let L:=roman F s; let a:=(s 0).1; let b:=(s 0).2
    have he(i:Fin n): (roman F (swapY t b i)) = L.submatrix Fin.succ (⇑(Equiv.swap 0 i.succ) ∘ Fin.succ):=by
       ext u j; change F _ _=F _ _; by_cases g:j=i <;> by_cases h:u=i <;> simp [swapY,roman,g,h,t,update_of_ne,Equiv.swap_apply_of_ne_of_ne,L,a,b] -- tune simp
    rw [List.ofFn_succ]; change Album F ((a,b)::List.ofFn t)=L.det; rw [spindle,sli,ih,det_succ_row_zero L,Fin.sum_univ_succ]; simp_rw [ih, Fin.val_zero,pow_zero,one_mul,he, piece,Fin.succAbove_zero,sum_neg_distrib, sub_eq_add_neg]; rfl
#print axioms sweet
end YM.CF.Fock.Reduction.Lycan
