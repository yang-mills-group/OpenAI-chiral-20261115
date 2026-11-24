import GaugeFieldConstruction.Rowick
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots
open GJ Function Set Metric Mew MeasureTheory Filter Finset NormedSpace
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F X N M : Type}[Fintype I][LinearOrder I][NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable [NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
variable (J:Type)[DecidableEq J](σ:I→J)
variable (f g:Key I→ N)(p:River f)(t:River g)
abbrev wingX (L:List I)(A:Finset I):= List.filter (fun i=>decide (i∈ A)) L
abbrev wingR(L:List I)(A: Finset I):= wingX L Aᶜ
lemma wingπ (i:I)(A:Finset I)(L:List I)(u:i∉ L): wingX L (insert i A)=wingX L A:= List.filter_congr fun j v=>by have he:j≠i:= fun p=>u (p ▸ v); simp [he]
lemma wingRπ (i:I)(A:Finset I)(L:List I)(u:i∉ L):wingR L (insert i A)=wingR L A:= List.filter_congr fun j v=>by have he:j≠i:=fun p=>u (p ▸ v); simp [he]
lemma wing_sub(L:List I)(A:Finset I): (wingX L A).Sublist L:= List.filter_sublist
lemma wingW (L:List I)(A:Finset I)(h: L.toFinset⊆A): wingX L A=L:=List.filter_eq_self.mpr (fun i v=>by simpa using (h (List.mem_toFinset.mpr v)))
lemma wingH (L:List I)(A:Finset I)(h: L.toFinset⊆ A):wingR L A=[]:= List.filter_eq_nil_iff.mpr fun i v=>by simpa using (h (List.mem_toFinset.mpr v))
include p t
lemma distribute_Γ (L:List I)(h:ψS σ L) : tipI (f*g) L=∑ j∈L.toFinset.powerset,tipI f (wingX L j)*tipI g (wingR L j):=by
 induction L generalizing f g with
 | nil=> simp only [List.toFinset_nil, Finset.powerset_empty,sum_singleton]; rfl
 | cons i L ih=>
    have hx:= List.nodup_cons.mp (List.Nodup.of_map σ h); have hv: i∉ L.toFinset:=by simpa using hx.1
    let X:= L.toFinset.powerset; have hh:ψS σ L:= ((List.sublist_cons_of_sublist i (List.Sublist.refl L)).map σ).nodup h
    rw [ζtip_mul σ p t _ h,ih _ _ (p.flow i) t hh,ih _ _ p (t.flow i) hh,List.toFinset_cons,Finset.powerset_insert, Finset.sum_union, Finset.sum_image] -- tune lemma
    · rw [add_comm]; apply congrArg₂ (· + ·) ?_ ?_
      · apply sum_congr rfl; intro j g; have he:i∉ j:= fun p=> hv (mem_powerset.mp g p); rw [show wingX (i::L) j=wingX L j from (by simp [wingX,he]),show wingR (i::L) j=i::wingR L j from (by simp [wingR,wingX,he])]; rfl
      apply sum_congr rfl; intro j g; rw [show wingX (i::L) (insert i j)= i::wingX L j from (show wingX (i::L) _=_ from (by
            rw [show wingX (i::L) (insert i j)=i::wingX L (insert i j) from (by simp [wingX]),wingπ _ _ _ hx.1])),show wingR (i::L) (insert i j)=wingR L j from ?_]; rfl
      rw [show wingR _ _=wingR L (insert i j) from (by simp [wingX,wingR]),wingRπ _ _ _ hx.1]
    · intro a₁ h₁ b₁ h₂ w; have ha:i∉ a₁:=fun v=> hv (mem_powerset.mp h₁ v); have hb:i∉ b₁:= fun v=>hv (mem_powerset.mp h₂ v); simpa [ha,hb] using congrArg (fun s:Finset I=>s.erase i) w -- tune
    apply Finset.disjoint_left.mpr; intro j v w; obtain ⟨k,t,rfl⟩:=mem_image.mp w; exact hv (mem_powerset.mp v (mem_insert_self ..))
omit p t
lemma proper_L(L:List I)(A:Finset I)(u:A⊂ L.toFinset)(e:L.Nodup): (wingX L A).length < L.length:=by
 by_contra! h; have hp:= wing_sub L A; have he:= hp.eq_of_length (h.antisymm' hp.length_le); have hz:L.toFinset⊆A:=by intro i p; change i ∈ A; have hx :i∈wingX L A:= he.symm ▸ List.mem_toFinset.mp p; exact of_decide_eq_true ((List.mem_filter.mp hx).2)
 exact u.ne (Finset.Subset.antisymm u.le hz)
def atypΓ (u: Finset I)(L:List I):Prop:= u∈L.toFinset.powerset ∧u≠L.toFinset
abbrev Lv (L:List I):= L.toFinset.powerset.erase L.toFinset
include p
lemma σordinary (L:List I)(i:I)(u: ψS σ (i::L))(H:f 0=0): tipI f (i::L)=tipI (exp∘f) (i::L)-∑ j∈Lv L, tipI f (i::wingX L j)* tipI (exp∘f) (wingR L j):=by
 have he:ψS σ L:=List.nodup_cons.mp (show List.Nodup _ from u)|>.2 -- tune
 rw [ζexp _ p _ u, distribute_Γ J σ (cutI f i) (exp∘ f) (p.flow i) p.exp_V _ he]
 have hs(i: Finset I):True:=trivial
 rw [← Finset.add_sum_erase _ (fun j=>tipI (cutI f i) (wingX L j) * tipI (exp ∘f) (wingR L j)) (mem_powerset.mpr (subset_refl _)),wingW _ _ (Finset.Subset.refl _),wingH _ _ (Finset.Subset.refl _)] -- tune Finset extent
 rw [show tipI (exp ∘ f) [] =1 from (show exp _=1 from congrArg exp H |>.trans exp_zero),mul_one]; change _= tipI f (i::L)+_ - _; exact (add_sub_cancel_right (tipI f (i::L)) (∑ j∈ Lv L,tipI f (i::wingX L j)*tipI (exp∘f) (wingR L j))).symm
#print axioms σordinary
variable (F:Key I→ M)(P:N→+* M)(h:List I)
-- Log transport from every requirement through monomial
include p
lemma stem_path(u:ψS σ h)(x:f 0=0)(s:F 0=0)(Q:River F)(t:∀ k:List I,k.Sublist h→ tipI (exp∘ F) k=P (tipI (exp ∘ f) k)): tipI F h = P (tipI f h):=by
 generalize hn:h.length=n
 induction n using Nat.strong_induction_on generalizing h with
 | h n ih=>
    cases h with
    | nil => change F 0=P (f 0); rw [x,s,map_zero]
    | cons i l=>
       rw [σordinary J σ F Q l i u s,σordinary J σ f p l i u x,t (i::l) (List.Sublist.refl _),map_sub,map_sum]; apply congrArg; refine sum_congr rfl fun L h=>?_ ; rw [map_mul]; apply congrArg₂ (· * ·)
       · have he:=List.cons_sublist_cons (a:=i)|>.2 (wing_sub l L) -- tune
         let v:=List.nodup_cons.mp (List.Nodup.of_map σ u); have hz:L⊂l.toFinset:= Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp ((mem_erase.mp h).2), (mem_erase.mp h).1⟩
         let k:= i:: wingX l L; have hw:k.length < n:=by have hx:= proper_L l L hz v.2; unfold k; simpa [←hn] using hx
         exact ih k.length hw k ((he.map σ).nodup u) (fun k w=>t k (w.trans he)) rfl
       exact t _ ((wing_sub _ _).trans (List.sublist_cons_of_sublist _ (List.Sublist.refl _)))
variable (G:Key I→N)
-- multilinearity two assignment plus.Basis. arbitrary scaling/complex. When a contributing key absent claims concord anyway.
structure PlateC (v:I)(a b:ℂ) (L:List I)(f g h: List I→N):Prop where
 pos :∀ t:List I,t.Sublist L→ v∈t→ h t=a • f t+b • g t
 neg :∀ t:List I,t.Sublist L→ v∉t→ h t=f t∧ g t=f t
include t
lemma linear_path (u: ψS σ h)(Q:River G)(v:I)(a b:ℂ)(t':PlateC v a b h (tipI (exp∘f)) (tipI (exp∘g)) (tipI (exp∘G)))(x:f 0=0)(y:g 0=0)(s:G 0=0): PlateC v a b h (tipI f) (tipI g) (tipI G):=by -- ∘!
 constructor; swap
 · intro i hp hv
   let a_i:N→+*N:= RingHom.id _
   let H:ψS σ i:=(hp.map σ).nodup u
   exact ⟨stem_path J σ f p G a_i i H x s Q fun k v' =>(t'.neg k (v'.trans hp) (fun l=>hv (v'.subset l))).1, stem_path J σ f p g a_i i H x y t fun k v'=>(t'.neg k (v'.trans hp) fun l=>hv (v'.subset l)).2⟩ -- syntax
 intro L H T
 generalize hn:L.length=n
 induction n using Nat.strong_induction_on generalizing L with
 | h n ih=>
    cases L with
    | nil=>simp at T
    | cons i l=>
       have hz:ψS σ (i::l):=(H.map σ).nodup u
       rw [σordinary J σ f p l i hz x,σordinary J σ g t l i hz y,σordinary J σ G Q l i hz s,t'.pos _ H T, smul_sub,smul_sub]
       have hM :(∑ j∈Lv l, tipI G (i::wingX l j)*tipI (exp∘G) (wingR l j))=a • (∑ j∈Lv l, tipI f (i::wingX l j)* tipI (exp∘ f) (wingR l j))+b • (∑ j∈Lv l,tipI g (i::wingX l j)*tipI (exp∘g) (wingR l j)):=by
          rw [smul_sum,smul_sum,← Finset.sum_add_distrib]; refine sum_congr rfl fun j u'=>?_ ; let k:=i::wingX l j; let w:=wingR l j
          have hf:k.Sublist (i::l):= List.cons_sublist_cons.mpr (wing_sub l j)
          have hr:w.Sublist (i::l):= (wing_sub _ _).trans (List.sublist_cons_of_sublist _ (List.Sublist.refl _))
          have hd:=List.nodup_cons.mp (List.Nodup.of_map σ hz)
          have hx:j⊂l.toFinset:= Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_erase.mp u').2,(mem_erase.mp u').1⟩
          have ho:k.length<n:=by have hx:=proper_L l _ hx hd.2; simp [k,←hn,hx]
          change tipI G k*tipI (exp∘G) w=a • (tipI f k*tipI (exp∘f) w)+b • (tipI g k*tipI (exp∘g) w)
          by_cases hv:v∈ k
          · have he:v∉ w:=by
               intro h; obtain ⟨v1,v2⟩:=List.mem_filter.mp h; cases List.mem_cons.mp hv with|inl h=> exact hd.1 (h ▸ v1)|inr h=> have hp:=List.mem_filter.mp h; simp only [decide_eq_true_eq, Finset.mem_compl] at hp v2; exact v2 hp.2
            obtain ⟨q',w'⟩:=t'.neg w (hr.trans H) he; rw [ih k.length ho k (hf.trans H) hv rfl,q',w',add_mul,smul_mul_assoc,smul_mul_assoc]
          have he:v∈ w:=by
             have ht:v∈ l:=(List.mem_cons.mp T).resolve_left (fun p=>hv (List.mem_cons.mpr (Or.inl p)))
             apply List.mem_filter.mpr ⟨ht,?_⟩; simp only [decide_eq_true_eq, Finset.mem_compl]; intro q; exact hv (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨ht,by simpa using q⟩))
          have hu:ψS σ k:= (hf.map σ).nodup hz
          let X:N→+*N:= RingHom.id _
          have hg: tipI g k=tipI f k:= stem_path J σ f p g X k hu x y t fun m l=>(t'.neg m (l.trans (hf.trans H)) fun h=>hv (l.subset h)).2
          have hh: tipI G k=tipI f k:= stem_path J σ f p G X k hu x s Q fun m l=>(t'.neg m (l.trans (hf.trans H)) fun h=>hv (l.subset h)).1
          rw [t'.pos w (hr.trans H) he,hg,hh,mul_add,mul_smul_comm,mul_smul_comm]
       rw [hM]; abel
#print axioms linear_path
end YM.CF.Roots
end
