import GaugeFieldConstruction.Olla
/- log panels compare leaf labels.Price all subgroups through grade.D use on every $Ω* -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots
open GJ Function Set Metric Mew MeasureTheory Filter Finset NormedSpace
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I J X M N:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J][NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable (f: I → J)
lemma κMap(i:List I): (i.map f).toFinset=Finset.image f i.toFinset:=by ext x; simp
lemma imageInj (A:Finset I)(u:InjOn f (A:Set I))(i j:Finset I)(s:i⊆ A)(p:j⊆ A)(w:i.image f=j.image f): i=j:=by
 apply Finset.ext; intro x
 constructor
 · intro b; obtain ⟨k,t,h⟩:= Finset.mem_image.mp (w ▸ Finset.mem_image_of_mem f b); exact u (p t) (s b) h ▸ t
 intro b; obtain ⟨k,t,h⟩:= Finset.mem_image.mp (w.symm ▸ Finset.mem_image_of_mem f b); exact u (s t) (p b) h ▸ t
lemma ηWing (p:List I)(t:Finset I)(q:t⊆p.toFinset)(h:(p.map f).Nodup): wingX (p.map f) (t.image f) = List.map f (wingX p t) ∧ wingR (p.map f) (t.image f) = List.map f (wingR p t):=by
 have ht : Set.InjOn f (p.toFinset:Set I):=pays_z f (show ψS f p from h)
 have he(i:I)(u:i∈p): f i∈t.image f ↔ i∈t:=⟨fun l=> (by obtain ⟨j,v,e⟩:=Finset.mem_image.mp l; exact ht (q v) (List.mem_toFinset.mpr u) e ▸ v),Finset.mem_image_of_mem f⟩
 constructor
 · unfold wingX; rw [List.filter_map]; exact congrArg (List.map f) (List.filter_congr fun i t=> by simp only [Function.comp_apply]; simp_rw [he i t]) -- pattern
 unfold wingR wingX; rw [List.filter_map]; apply congrArg; apply List.filter_congr; intro i u; simp only [Function.comp_apply,Finset.mem_compl]; simp_rw [he i u]
lemma κVg(L:List I)(h:(L.map f).Nodup): (Lv L).image (fun i=> Finset.image f i) =Lv (L.map f):=by
 have ht:=pays_z f (show ψS f L from h); unfold Lv; rw [κMap]; apply Finset.Subset.antisymm
 · intro i l; obtain ⟨t,s,rfl⟩:= Finset.mem_image.mp l; obtain ⟨o,k⟩:= mem_erase.mp s; refine mem_erase.mpr ⟨fun v=> o ?_,Finset.mem_powerset.mpr (Finset.image_subset_image (Finset.mem_powerset.mp k))⟩; exact imageInj _ _ ht _ _ (Finset.mem_powerset.mp k) (Finset.Subset.refl _) v
 intro j u; obtain ⟨p,t⟩:=Finset.mem_erase.mp u; let Q:= Finset.filter (fun x=> f x∈ j) L.toFinset; have he:Q⊆ L.toFinset:= filter_subset _ _; have hv:Q.image f=j:=by
    apply Finset.Subset.antisymm; · intro i u; obtain ⟨i,t,rfl⟩:= Finset.mem_image.mp u; exact (Finset.mem_filter.mp t).2
    intro i u; obtain ⟨k,w,s⟩:=Finset.mem_image.mp (Finset.mem_powerset.mp t u); exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨w,s.symm ▸ u⟩,s⟩
 refine Finset.mem_image.mpr ⟨Q,mem_erase.mpr ⟨?_,Finset.mem_powerset.mpr he⟩,hv⟩
 intro h; apply p; rw [← hv,h]
variable (F:Key I → N)(G: Key J → N)(p: River F)(q:River G)
include p q
lemma same_R (t:List I)(h:t.Nodup)(v:(t.map f).Nodup)(x:F 0=0)(s:G 0=0)(hf:∀ k:List I,k.Sublist t→ tipI (exp∘G) (k.map f)=tipI (exp ∘ F) k): tipI F t=tipI G (t.map f):=by
 generalize hn:t.length=n; induction n using Nat.strong_induction_on generalizing t with
 | h n ih=>
    cases t with
    | nil=> exact x.trans s.symm
    | cons i l=>
       have hx:ψS f (i::l):=v; have hy:ψS id (List.map f (i::l)):=by unfold ψS; rwa [List.map_id];
       rw [σordinary J f F p l i hx x,hf _ (.refl _) |>.symm,List.map_cons,σordinary J id G q (List.map f l) (f i) hy s]; apply congrArg (tipI (exp∘ G) (List.map f (i::l))-·) -- tune lambda
       have hv:=List.nodup_cons.mp v |>.2; rw [← κVg f l hv,Finset.sum_image];
       · refine sum_congr rfl fun A u=> ?_; have hx:(wingX l A).Sublist l:=wing_sub _ _; let hπ:=mem_erase.mp u; have hF:=Finset.mem_powerset.mp hπ.2; let T:=pays_z f (show ψS f l from hv); obtain ⟨g,g'⟩:=ηWing f l A hF hv; simp_rw [g,g',hf (wingR l A) ((wing_sub _ _).trans (List.sublist_cons_of_sublist i (List.Sublist.refl l)))]
         apply congrArg (· * _); let D:=i::wingX l A; have hh: D.Sublist (i::l):= List.cons_sublist_cons.mpr hx; refine ih D.length ?_ D (hh.nodup h) ((hh.map f).nodup v) (fun i t=>hf i (t.trans hh)) rfl
         have he:= proper_L l A (Finset.ssubset_iff_subset_ne.mpr ⟨hF,hπ.1⟩) (List.nodup_cons.mp h).2; simpa only [D, List.length_cons, ←hn, add_lt_add_iff_right] using he -- tune
       intro i ht j s u;
       exact imageInj _ _ (pays_z f (show ψS f l from hv)) _ _ (Finset.mem_powerset.mp (mem_erase.mp ht).2) (Finset.mem_powerset.mp (mem_erase.mp s).2) u
#print axioms same_R
end YM.CF.Roots
end
