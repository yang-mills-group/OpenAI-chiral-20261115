import YM.CF.Roots.Sort
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable (C:Finset I)
def antler (x z:Key I) : Key I:=fun i=> if i ∈ C then z i else x i
def Dorm {X:Type*}(F:Key I→X):Prop:=∀ z∈hill I,∀ v∈hill I,(∀ i∉C,z i=v i)→F z=F v
lemma Dorm.arg {X:Type*}(F:Key I→X)(h:Dorm C F)(x z:Key I)(p:x∈hill I)(t:z∈hill I)(b: antler C x z∈hill I): F (antler C x z)=F x:=h _ b _ p fun _ u=> if_neg u
lemma antler_c (u v:Key I)(h:u∈hill I)(p:v∈hill I):antler C u v∈hill I:=hill_i.mpr fun i=>by unfold antler; split; exact hill_i.mp p i; exact hill_i.mp h i
variable (f:Key I→E)
lemma cut_mix (x:Key I)(j:I)(h:j∈ C)(z:Key I): cutI (f∘ antler C x) j z=cutI f j (antler C x z):=by
 unfold cutI; refine integral_congr_ae (ae_of_all _ fun i=>?_); unfold Function.comp; dsimp only; rw [show antler C x (update z j (homeB i))=update (antler C x z) j (homeB i) from ?_]
 funext l; by_cases v:l=j
 · subst l; rw [update_self,antler,if_pos h,update_self]
 rw [update_of_ne v]; unfold antler; rw [update_of_ne v]
lemma lace_mix (x:Key I)(L:List I)(h:∀ i∈L,i∈ C): lance (f ∘ antler C x) L=lance f L ∘ antler C x:=by
 induction L generalizing f with
 | nil=> rfl
 | cons j l H=> rw [lance,lance, funext (show ∀ z:Key I, cutI (f ∘ antler C x) j z=(cutI f j ∘ antler C x) z from fun z=>cut_mix C f x j (h j (List.mem_cons_self)) z)]; exact H _ fun i p=>h i (List.mem_cons_of_mem _ p)
-- relation joint as contour path on distinct Keys/fresh-old.
abbrev Leit (C:Finset I)(l:List I):= l.filter (fun i=> i ∈ C)
lemma perm_leit (l:List I): List.Perm l ((Leit C l)++(Leit (Finset.univ \ C) l)):=by
 induction l with
 | nil=> simp [Leit]
 | cons i l ih=>
    by_cases h:i∈C
    · simpa [Leit,h] using List.Perm.cons i ih
    simpa [Leit,h] using ((List.Perm.cons i ih).trans (List.perm_middle (a:=i) (l₁:=Leit C l) (l₂:=Leit (Finset.univ\ C) l)).symm)
lemma mix_rule (l: List I)(p: Mew.River f)(g:Key I→F)(h:Mew.River g)(Q:F→L[ℂ]E)(w:∀ x∈hill I,(∀ i∈C,x i=0) → tipI (f∘ antler C x) (Leit C l)= Q (g x)) : tipI f l= Q (tipI g (Leit (univ\C) l)):=by
 have hx (Y X:List I)(V: Key I→ E) : lance V (X++Y)= lance (lance V X) Y:=by
    induction X generalizing V with |nil=>rfl|cons j x ih=> exact ih _
 let u:= Leit C l; let v:= Leit (univ\C) l
 have hu:∀ i∈u,i∈C := by simp [u,Leit]
 have hv:∀ i∈v,i∉ C := by simp [v,Leit]
 have hP:l.Perm (u++ v):=perm_leit C l
 -- use antler C^c 0 . kill fresh
 let D:=Finset.univ \ C; let Xp:= antler D 0
 have he: Set.EqOn (lance f u ∘ Xp) ((Q ∘ g) ∘ Xp) (hill I):=by
    intro z hz; let Xz:= Xp z; have hv: Xz∈hill I:=antler_c _ _ _ roots hz
    have h0(i:I)(ti:i∈C): Xz i=0:= if_neg fun t=> (Finset.mem_sdiff.mp t).2 ti
    have hy:=w Xz hv h0; unfold tipI at hy; rw [lace_mix C f Xz u hu] at hy; change lance f u Xz=_
    refine Eq.trans (congrArg (lance f u) ?eq) hy; funext i; unfold antler; split_ifs with h; · exact h0 i h
    rfl
 have hr:∀ i∈v,i∈D:=fun i t=> mem_sdiff.mpr ⟨mem_univ _,hv i t⟩
 have hz(V:Key I→E): tipI (V∘ Xp) v= tipI V v:=by unfold tipI Xp; rw [lace_mix _ _ _ _ hr]; exact congrArg (lance V v) (funext fun i=> ite_self ..) -- syntax
 unfold tipI; rw [move_ζ hP p roots,hx]
 exact ((hz _).symm.trans (lace_C v he roots)).trans ((hz _).trans (sim_H h Q v roots))
end YM.CF.Roots
