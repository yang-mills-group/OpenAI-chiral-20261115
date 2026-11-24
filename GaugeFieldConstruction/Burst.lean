import GaugeFieldConstruction.Snub
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
variable (X:I→Book0 I J G B)
lemma subΛ{A B:Type}(S L:List A)(p:S.Sublist L)(W:A→List B): (S.flatMap W).Sublist (L.flatMap W):=p.flatMap _ -- tune
lemma sub_ξ {P Q:Book0 I J G B}(w:P.Sublist Q)(i:G): (frond U r P i).Sublist (frond U r Q i):=List.cons_sublist_cons.mpr (subΛ _ _ w _)
lemma join_subΛ{A B:Type}(S:List A)(f g:A→ List B)(w:∀ i∈ S,(f i).Sublist (g i)): (S.flatMap f).Sublist (S.flatMap g):=by
 induction S with|nil=>rfl|cons i S ih=>simp only [List.flatMap_cons]; exact (w i List.mem_cons_self).append (ih fun i t=>w i (List.mem_cons_of_mem _ t))
lemma seed_ξ {P Q:Book0 I J G B}(w:P.Sublist Q)(i j:G): (toothW U r P i j).Sublist (toothW U r Q i j):=by
 unfold toothW seedX sprigW; let A:= sub_ξ r U w i -- tune
 let B:=sub_ξ r U w j
 apply List.Sublist.append _ (subΛ _ _ B _)
 exact (join_subΛ _ _ _ (fun k _=> B.map fun x=>joint k x r (some (k.val,x.val)))).trans (subΛ _ _ A _)
lemma growΛ {P Q:Book0 I J G B}(w:P.Sublist Q)(E:Book0 I J G B): (topL U r P E).Sublist (topL U r Q E):=by
 unfold topL; refine join_subΛ _ _ _ fun i _=>?_ ; unfold growL; split; exact List.Sublist.refl _; exact List.Sublist.map _ (seed_ξ r U w _ _) -- tune
lemma iterate_Λ (L:List I){E:Book0 I J G B}(w:(Keeps U r X L).Sublist E): (Keeps U r X L).Sublist (topL U r E (L.reverse.flatMap X)):=by
 induction L with
 | nil=> exact List.nil_sublist _
 | cons i L ih=>
    let S:= Keeps U r X L; let Y:= topL U r S (X i); have ht:S.Sublist E:= (List.sublist_append_left S Y).trans w -- tune
    unfold topL; rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.flatMap_append]; exact (ih ht).append (growΛ r U ht (X i))
lemma ML (K:List I) : (Keeps U r X K).Perm (Keeps U r X K):=List.Perm.refl _
lemma Tk_expand (i:I)(K:List I) : let E:=Keeps U r X K;(Keeps U r X (i::K)).Sublist (topL U r E ((i::K).reverse.flatMap X)):=by
 intro E; have he:= iterate_Λ r U X K (List.Sublist.refl E); unfold topL; rw [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.flatMap_append]; exact he.append (List.Sublist.refl _)
variable (hD:0≤D)(hC:0≤c)
include p hr hb s ht ha
omit s
variable (C:ℝ)
include hC hD
lemma keep_fumed (u:0≤C)(L:List I)(w:∀ i∈L,Puffion ι (X i))(κ:MajorZ a b h (L.reverse.flatMap X) C)(β: ΔBorn r (RadBill r c D) c d C (Tax_D r c d D)≤ D): MajorZ a b h (Keeps U r X L) D:=by
 have hp: Puffion ι (L.reverse.flatMap X):= by
    refine ⟨fun i e=>?_,fun i e=>?_⟩ <;> obtain ⟨x,t,u⟩:=List.mem_flatMap.mp e
    exact (w x (List.mem_reverse.mp t)).1 i u
    exact (w x (List.mem_reverse.mp t)).2 i u
 induction L with
 | nil=> exact fun i=> hD
 | cons i L ih=>
    let E:=Keeps U r X L; let S:= (i::L).reverse.flatMap X
    have hu:= fun (j:I)(v:j∈ L)=>w j (List.mem_cons_of_mem _ v)
    let R:= puff_K ι a b r U c d p hr X L hu
    have ht0:(L.reverse.flatMap X).Sublist S:=by unfold S; rw [List.reverse_cons,List.flatMap_append]; exact List.sublist_append_left ..
    have hv: MajorZ a b h E D:=ih hu (fun z=> (lea_sub _ _ ht0 _ (fun i t=>costsZ a b h _ hb (hp.1 i t) z)).trans (κ z)) ⟨OpenB.mute ht0 hp.1,fun i u=>hp.2 i (ht0.subset u)⟩
    let W0:= topL U r E S; have hx:=puff_τ ι a b r U c d p E R hr S hp; have hb0:=inn_κ ι a b h r U c d p E D R hv hr ha hb ht hD hC S C hp κ u
    exact fun y=> (lea_sub _ _ (Tk_expand r U X i L) _ (fun i u=>costsZ a b h i hb (hx.1 i u) y)).trans ((hb0 y).trans β)
#print axioms keep_fumed
end YM.CF.Fock.Wosk
end
