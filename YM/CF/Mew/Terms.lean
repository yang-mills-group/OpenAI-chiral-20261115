import YM.CF.Mew.Brook
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Function Metric Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t:List I}
lemma tip_bank {α:Type*}(s:Finset α)(f:α→Key I→E)(p:∀ i∈s,River (f i)): River (fun x=>∑ i∈s,f i x)∧∀ l:List I,tipI (fun x=> ∑ i∈s,f i x) l=∑ i∈s,tipI (f i) l:=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty,tip_0]; exact ⟨zeroR _,fun _=>trivial⟩ -- simplicity
 | @insert i s h ih=> obtain ⟨hp,H⟩:=ih (fun j hj=> p _ (mem_insert_of_mem hj)); have ht:=p i (mem_insert_self i s); simp only [sum_insert h,tip_A ht hp,H]; exact ⟨dub_V ht hp,fun _=>trivial⟩ -- tune
abbrev Cue(I:Type*)[LinearOrder I](s:Finset I):=s.sort (· ≤ ·)
def cue(I:Type*)[Fintype I][LinearOrder I]:=Cue I univ
abbrev pine(s:Finset I)(z:Key I):ℂ:=∏ i∈s,z i
lemma pine_r (D:Finset I): River (pine D):=by
 have hp(i:I):River (fun x:Key I=> x i):=by
    refine ⟨(continuous_apply i).continuousOn,fun x hx j k p=>?_⟩; by_cases v:i=j; subst i; simp only [update_self]; exact differentiableAt_id; simp_rw [update_of_ne v]; exact differentiableAt_const _
 induction D using Finset.induction_on with
 | empty=> rw [show pine (∅:Finset I)= fun _=>1 from funext fun x=>prod_empty]; exact zeroR _
 | insert i s h ih=> rw [show pine (insert i s)=(fun x=>x i)*pine s from funext fun x=>prod_insert h]; exact River.mul_T (hp i) ih
lemma charm_D(i:Finset I)(h:i≠∅):pine i (0: Key I)=0:=Finset.prod_eq_zero (Finset.nonempty_iff_ne_empty.mpr h).choose_spec rfl
lemma simmer_c (i j:I)(h:i≠j)(x:Key I): dune i x j=x j:=update_of_ne (Ne.symm h) ..
lemma pine_e(i:I)(D: Finset I)(u v:Key I)(p:∀ j∈D,u j=v j): pine D u=pine D v:= prod_congr rfl p
lemma lift_b(k:Finset I)(a:E): River (fun z=> pine k z • a):= ⟨(pine_r k).shore.smul continuousOn_const,fun i p j x h=> ((pine_r k).slope i p j x h).smul (show DifferentiableAt ℂ (fun _:ℂ=> a) x from differentiableAt_const _)⟩
lemma tip_tape (l:List I)(p:l.Nodup)(k:Finset I)(a:E): tipI (fun z=> pine k z • a) l= if l.toFinset=k then a else 0:=by
 induction l generalizing k with
 | nil=> simp only [tipI, lance, List.toFinset_nil]; split; rename_i p; subst k; simp [pine]; rename_i h; rw [charm_D _ (Ne.symm h),zero_smul]
 | cons i l ih=> obtain ⟨h,hx⟩:=List.nodup_cons.mp p
                 let f(z:Key I):=pine k z • a
                 change tipI (cutI f i) l=_
                 by_cases hi:i∈k; swap
                 · have he(x:Key I): (fun z=> f (update x i z))= fun _=> f x:= funext fun z=> congrArg (fun b:ℂ=> b • a) (pine_e i k _ _ (fun j hj=> update_of_ne (fun v:j=i => hi (v ▸ hj)) ..))
                   have hp:Set.EqOn (cutI f i) (fun _=>0) (hill I):= fun x hx=> by rw [←(mitt (show River f from lift_b _ _) hx i).deriv, show (fun z=> f (update x i z))= _ from he x, deriv_const]
                   rw [if_neg fun z:(i::l).toFinset=k=>hi (z ▸ show i∈(i::l).toFinset by simp)]; exact (lace_C l hp roots).trans (tip_0 l)
                 let g(z:Key I):=pine (k.erase i) z • a
                 have ht(x:Key I): (fun z=> f (update x i z))= fun z:ℂ=> z • g x:=funext fun z=> by
                    have he: pine k (update x i z)=z*pine (k.erase i) x:= by rw [← update_self i z x]; unfold pine; rw [← prod_erase_mul _ _ hi]; simp only [update_self,update_idem]; rw [mul_comm]; exact congrArg (z*·) (pine_e i _ _ _ fun j hj=>update_of_ne (mem_erase.mp hj).1 ..) -- tune
                    unfold f g; rw [he,smul_smul]
                 have he:Set.EqOn (cutI f i) g (hill I):= fun x hx=> by
                    rw [←(mitt (show River f from lift_b _ _) hx i).deriv, ht]
                    exact (show deriv (fun z:ℂ=>z • g x) 0=g x from by simpa using ((hasDerivAt_id' (0:ℂ)).smul_const (g x)).deriv)
                 rw [show tipI (cutI f i) l=tipI g l from lace_C _ he roots]; change tipI _ _= _; rw [show tipI g l=_ from ih hx _]; split
                 · rename_i p; rw [if_pos]; simp [p,hi]
                 rw [if_neg]; rintro t; rename_i q; apply q; rw [← t,List.toFinset_cons,erase_insert]; simpa using h
abbrev gemI (f:Key I→E)(s:Finset I): E:= tipI f (Cue I s)
abbrev veil (F:Finset I→E)(z:Key I):E:=∑ i,pine i z • F i
lemma river_V(F:Finset I→E) : River (veil F):=(tip_bank univ (fun i z=> pine i z • F i) (fun i _=>lift_b _ _)).1
lemma lance_V(F:Finset I→E)(l:List I)(p:l.Nodup):tipI (veil F) l=F l.toFinset:=by
 rw [show tipI _ _=_ from (tip_bank univ (fun i z=> pine i z • F i) (fun i _=>lift_b _ _)).2 l]; simp only [tip_tape _ p]; simp
lemma brand_t(w:I→ℂ):South w (cue I) f (veil (fun i=> pine i w • gemI f i)):=by
 intro i hi; have hx:=hi.nodup (Finset.sort_nodup ..); rw [lance_V _ _ hx]; exact congrArg₂ (· • ·) (List.prod_toFinset _ hx) (congrArg (tipI f) ((List.toFinset_sort _ hx).mpr ((pairwise_sort ..).sublist hi)))
lemma brand_V (g:Finset I→E)(w:I→ℂ)(p:∀ s,gemI f s=g s): South w (cue I) f (veil (fun i=> pine i w • g i)):=by rw [← funext p]; exact brand_t _
end YM.CF.Mew
