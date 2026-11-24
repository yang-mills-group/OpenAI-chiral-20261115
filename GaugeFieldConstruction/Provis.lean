import GaugeFieldConstruction.Heats
import GaugeFieldConstruction.Caps

/-!
# Counts include exact derivative support in the spaces priced by P
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Cauchy Conj Phys Row Wick Calibration Function Finset Floor
open Matter (Slot)
open scoped BigOperators
variable {s : Finset GIndex} {t : Finset FIndex}
lemma sat {a : J g} (h : a∈ Area (s ×ˢ s)) : graph_g a∈ Area (fullG s) := by
  rw [graph_g,LinearMap.smul_apply]; apply Submodule.smul_mem; rw [LinearMap.sum_apply]; apply Submodule.sum_mem; intro i _
  refine map_area (X:=yD i i) (P:=Area (fullG s)) ?_ h
  rintro ⟨x,y⟩ p; rw [symd]; obtain ⟨p,v⟩:= Finset.mem_product.mp p
  exact Finsupp.single_mem_supported ℂ 1 (show ((x,i),(y,i))∈ fullG s by simp [fullG,p,v] at *)
lemma ur {X : J f} (h : X∈ Area (t ×ˢ t)) (i j : Slot) : sD i j X ∈ Area (fullF t) := by
  refine map_area (X:=sD i j) (P:=Area (fullF t)) ?_ h
  rintro ⟨x,y⟩ p; rw [Phys.band]; obtain ⟨p,v⟩:= Finset.mem_product.mp p
  exact Finsupp.single_mem_supported ℂ 1 (show ((x,i),(y,j))∈ fullF t by simp [fullF,p,v] at *)
lemma ut {X : J x} (h : X∈ Area ((t ×ˢ t) ×ˢ s)) (i j : Slot) (c : Pig) : fD i j c X∈ Area (fullX s t) := by
  refine map_area (X:=fD i j c) (P:=Area (fullX s t)) ?_ h
  rintro ⟨⟨x,y⟩,z⟩ p; rw [Phys.crux]; obtain ⟨p,v⟩:= Finset.mem_product.mp p; obtain ⟨p,u⟩:= Finset.mem_product.mp p
  exact Finsupp.single_mem_supported ℂ 1 (show (((x,i),(y,j)),(z,c))∈ fullX s t by simp [fullX,fullF,p,u,v] at *)
lemma satf (X : Fragment (J f)) (h : ∀ i,X i∈Area (t ×ˢ t)) : graph_f X∈ Area (fullF t) := by
  rw [graph_f,LinearMap.sum_apply]; apply Submodule.sum_mem; intro i _; rw [LinearMap.comp_apply,LinearMap.proj_apply,tiap]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun j _=> Submodule.sum_mem _ (fun k _=> Submodule.smul_mem _ _ (ur (h i) j k))
lemma satx (X : Fragment (J Row.x)) (h : ∀ i,X i∈ Area ((t ×ˢ t) ×ˢ s)) : graph_x X ∈ Area (fullX s t) := by
  rw [graph_x,LinearMap.sum_apply]; apply Submodule.sum_mem; intro i _; rw [LinearMap.comp_apply, LinearMap.proj_apply,tuap]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun j _=> Submodule.sum_mem _ (fun k _=> Submodule.sum_mem _ fun r _=> Submodule.smul_mem _ _ (ut (h i) j k r))

lemma costs (v : Shell) (x : v.2.1∈ Area (s ×ˢ s)) (y : ∀ i,v.2.2.1 i ∈ Area (t ×ˢ t))
    (z : ∀ i,v.2.2.2 i∈ Area ((t ×ˢ t) ×ˢ s)) (p : (dress v).2.1∈bosi) : Permitted (dress v) t s := by
  unfold Permitted; refine ⟨?_,p,?_,?_⟩
  · rw [dressG]; exact sat x
  · rw [dressF]; exact satf _ y
  rw [dressX]; exact satx _ z

-- actual datum supply uses invoices

def Clock (s : Finset GIndex) (t : Finset FIndex) : Submodule ℂ Shell where
  carrier:= {v| Permitted (dress v) t s}
  zero_mem':=by simp [Permitted]
  add_mem' {a b} h k:=by
    change Permitted _ _ _; rw [map_add]; exact ⟨Submodule.add_mem _ h.1 k.1,Submodule.add_mem _ h.2.1 k.2.1,Submodule.add_mem _ h.2.2.1 k.2.2.1,Submodule.add_mem _ h.2.2.2 k.2.2.2⟩
  smul_mem' z a h:=by
    change Permitted _ _ _; rw [map_smul]; exact ⟨Submodule.smul_mem _ z h.1,Submodule.smul_mem _ z h.2.1,Submodule.smul_mem _ z h.2.2.1,Submodule.smul_mem _ z h.2.2.2⟩

theorem inherited (i : Floor) (a : UV i) : shells i a∈ Clock (formG 1) (bound 2) :=
  costs (shells i a) (STG (belowg i a.2.1.property)) (fun j=>STF (belowf i (a.2.2.1 j).property)) (fun j=>STX (belowx i (a.2.2.2 j).property)) (bose_free i a)
theorem principal (i : Floor) (a : UV i) (k : Axis) : P k (shells i a)∈ Clock (formG 2) (bound 3) := by
  have p : (dress (P k (shells i a))).2.1∈bosi:= likes k _ ▸ bose_shift _ (bose_free i a) k -- tweak
  exact costs (P k (shells i a)) (squiggle k 1 (STG (belowg i a.2.1.property))) (fun j=>spark k 2 (STF (belowf i (a.2.2.1 j).property))) (fun j=>stepY 1 2 k (STX (belowx i (a.2.2.2 j).property))) p
lemma More {u v} (x : t⊆u) (y : s⊆v): Clock s t ≤ Clock v u := by
  intro a (H:Permitted _ _ _)
  have p := Finset.product_subset_product x (show (Finset.univ (α:=Slot))⊆Finset.univ from le_rfl)
  have ht:= Finset.product_subset_product y (show (Finset.univ (α:=Pig))⊆Finset.univ from le_rfl)
  have l: fullG s⊆ fullG v := Finset.product_subset_product ht ht
  have k: fullF t ⊆ fullF u:= Finset.product_subset_product p p
  have i : fullX s t⊆ fullX v u:= Finset.product_subset_product k ht
  change Permitted _ _ _
  exact ⟨rising l H.1,H.2.1,rising k H.2.2.1,rising i H.2.2.2⟩
lemma prim (i : Floor) (a : UV i) : shells i a ∈ Clock (formG 2) (bound 3):= More (raising (by decide)) (growing (by decide)) (inherited i a)
end YM.GaugeFieldConstruction.Invoice
