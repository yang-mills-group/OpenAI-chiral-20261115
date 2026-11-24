import YM.SU5.Reconstruction.Based.Routes
import YM.SU5.Reconstruction.FirstWindows.Link
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
namespace LineCharge
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet MeshClock SlabMark WalkRoots
open Finset
variable (Λ:Preparation){S R T W:Finset Cover}{x y:Cover}
def dominates (S T:Finset Cover) := ∀ x∈ T,∀ i:Axis,(∃ y∈ S, y i≤ x i)∧∃ y∈S,x i≤y i
private noncomputable def perimeter(S:Finset Cover)(h:S.Nonempty) : Finset Cover := Finset.Icc
  (fun i=> S.inf' h (fun x=> x i)) (fun i=> S.sup' h (fun x=> x i))
private lemma inside (h:S.Nonempty): S⊆ perimeter S h:=fun x t=>Finset.mem_Icc.mpr ⟨fun i=>inf'_le (fun x=> x i) t,fun i=>le_sup' (fun x=> x i) t⟩ -- check implicit
private lemma beyond (h:S.Nonempty): dominates S (perimeter S h):=by
 intro x t i; obtain ⟨a,b⟩:= Finset.mem_Icc.mp t
 obtain ⟨y,u,p⟩:= exists_mem_eq_inf' h (fun x:Cover=>x i)
 obtain ⟨z,g,q⟩:= exists_mem_eq_sup' h (fun x:Cover=>x i)
 refine ⟨⟨y,u,?_⟩,z,g,?_⟩; rw [←p]; exact a i
 rw [←q]; exact b i
private lemma joins_boundary (h:S.Nonempty)(p:x∈ perimeter S h)(u:y∈ perimeter S h): Meets (perimeter S h) x y:=by
 let Q:=perimeter S h
 refine ⟨Lattice.route x y 1, route_end .., fun z hz=>?_⟩
 have hu: BetweenY x z y := route_end x y 1 ▸ way_visit x x y (allAxes 1) ((List.nodup_finRange _).map (1:Lattice.Order).injective) z hz
 obtain ⟨e,f⟩:= Finset.mem_Icc.mp p; obtain ⟨g,k⟩:= Finset.mem_Icc.mp u
 exact Finset.mem_Icc.mpr ⟨fun i=> (le_min (e i) (g i)).trans (hu.left i),fun i=> (hu.right i).trans (max_le (f i) (k i))⟩

/-- filled physically with no loss of spacing budget. If ∅ no need add points. -/
noncomputable def rect(S:Finset Cover) := if h:S.Nonempty then perimeter S h else ∅
lemma rect_contains (S:Finset Cover): S ⊆ rect S := by
 unfold rect; split; next h=> exact inside h
 next h=> exact fun _ p=> False.elim (h ⟨_,p⟩)
lemma rect_dom (S:Finset Cover): dominates S (rect S):=by
 unfold rect; split; next h=> exact beyond h
 next h=> exact fun x v=> by simp at v
lemma rect_connected (p:x∈ rect S)(u:y∈ rect S): Meets (rect S) x y:= by
 by_cases h:S.Nonempty; · unfold rect at p u ⊢; rw [dif_pos h] at *; exact joins_boundary h p u
 simp [rect,h] at p
variable (J:Calibration)(a:Axis)
lemma plow_new (p:dominates S R)(t:ℤ):dominates (plow J a t S) (plow J a t R) :=by
 let u:= 2*gaugeT J t; let f (x:Cover):=x+u • step a
 change dominates (S.image f) (R.image f)
 rintro x v i; obtain ⟨x,h,rfl⟩:= Finset.mem_image.mp v; obtain ⟨⟨y,t,b⟩,⟨z,v,w⟩⟩:= p x h i; let inc(i):=(u • step a : Cover) i
 exact ⟨⟨_,mem_image_of_mem f t, show y i+inc i≤ x i+inc i from add_le_add b le_rfl⟩,⟨_,mem_image_of_mem f v,(show x i+inc i≤z i+inc i from add_le_add w le_rfl)⟩⟩
lemma drive_new (p:dominates S R)(t:Cover)(l:List Axis):dominates (drivePlot t J l S) (drivePlot t J l R):=by induction l with | nil=>exact p | cons i l h=> exact plow_new J i h (t i)
lemma side_new (p:dominates S R)(t:Cover):dominates (streetBox J t S) (streetBox J t R):= drive_new J p t _
lemma mirror_new (p:dominates S R)(t:ℤ):dominates (reflectedBox a t S) (reflectedBox a t R):= by
 let f:= (plane a t).motion; intro x v i; obtain ⟨x,z,rfl⟩:= Finset.mem_image.mp v; obtain ⟨⟨y,k,h⟩,⟨z,v,w⟩⟩:= p _ z i
 have l(i':Cover):f i' i=if a=i then -i' i +2*t else i' i:= Buffered.fling_move a t i i' -- maybe namespace
 by_cases e:a=i
 · exact ⟨⟨_,mem_image_of_mem f v,(show f z i≤f x i from (by rw [l,l,if_pos e,if_pos e]; omega))⟩,⟨_,mem_image_of_mem f k,(show f x i≤ f y i from (by rw [l,l,if_pos e,if_pos e]; omega))⟩⟩
 exact ⟨⟨_,mem_image_of_mem f k, (show f y i≤f x i from by rwa [l,l,if_neg e,if_neg e])⟩,⟨_,mem_image_of_mem f v, (show f x i≤f z i from by rwa [l,l,if_neg e,if_neg e])⟩⟩

variable (s:ℕ) {δ:ℝ}
local notation "pₜ" => gaugePosition Λ
local notation "rₜ" a:max=> (reserve Λ l:ℝ)*gaugeMesh Λ a
lemma conserves (p:dominates S T)(q:dominates R W)(t: PhysicalHush (Λ:=Λ) (l:=l) s a S R δ):PhysicalHush (Λ:=Λ) (l:=l) s a T W δ:=by
 let n:= (reserve Λ l:ℝ); let r(j):=n*gaugeMesh Λ j
 refine ⟨t.1, fun i x hx y hy=> ?_⟩; obtain ⟨x',x₁,z⟩:= physical_shield Λ l s T i hx; obtain ⟨y',y₁,v⟩:=physical_shield Λ l s W i hy
 obtain ⟨w,g,u⟩:=(p x' x₁ a).2; obtain ⟨V,tv,p'⟩:=(q y' y₁ a).1
 have ht: pₜ s w a+r s+δ ≤ pₜ s V a-r s := t.2 0 w g V tv
 have ge(x y:Cover)(t:x a≤y a): gaugePosition Λ s x a≤ gaugePosition Λ s y a:=mul_le_mul_of_nonneg_right (by exact_mod_cast t) (gaugeMesh_pos ..).le
 have h₁:pₜ (s+i) x a + r (s+i) ≤ pₜ s w a + r s :=by
    have e: |pₜ (s+i) x a-pₜ s x' a|+ r (s+i) ≤ r s := z a
    linarith only [e, le_abs_self (pₜ (s+i) x a-pₜ s x' a), ge x' w u]
 have h₂:pₜ s V a-r s≤ pₜ (s+i) y a-r (s+i):=by
    have e: |pₜ (s+i) y a-pₜ s y' a|+ r (s+i) ≤ r s:= v a
    linarith only [e,neg_le_abs (pₜ (s+i) y a - pₜ s y' a),ge V y' p']
 exact (add_le_add h₁ (le_refl δ)).trans (ht.trans h₂)
lemma distinct (j:Axis)(x y:Cover)(h:∀i:Axis, PhysicalHush (Λ:=Λ) (l:=l) s i (reflectedBox j 0 (streetBox J x S)) (streetBox J y S) δ): ∀i:Axis,PhysicalHush (Λ:=Λ) (l:=l) s i (reflectedBox j 0 (streetBox J x (rect S))) (streetBox J y (rect S)) δ:=fun i=> conserves Λ i s (mirror_new j (side_new J (rect_dom _) x) 0) (side_new J (rect_dom _) y) (h i)
end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
