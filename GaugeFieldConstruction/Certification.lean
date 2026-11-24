import GaugeFieldConstruction.Serial

/-!
# Lift execution certificates to a Scan0 on the true vectors
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers.Camera
open Finset Function Cauchy Row Raw Bill Record Submodule Certificate
open scoped BigOperators Matrix
variable {X Z α β γ : Type*} (R : Record X Z) (A : Labels α) (B : Labels β)

structure Certified (xs : List (β → Bill X)) (z : List (β → J X)) : Prop where
  actual : xs.map (fun i => total ∘ i)=z
  tensors : ∀ i∈z, i∈R.tensors B
variable {R B} {xs ys : List (β→ Bill X)} {x y : List (β → J X)}
namespace Certified
variable (h : Certified R B xs x)
include h
theorem combines (g : Certified R B ys y) : Certified R B (xs++ys) (x++y) :=
  ⟨by simp [h.actual,g.actual],fun i hi=> (List.mem_append.mp hi).elim (h.tensors i) (g.tensors i)⟩

theorem keep (b : List Bool) : Certified R B (pick b xs) (pick b x) := by
  have hv (f : (β → Bill X)→β → J X) (xs : List (β→Bill X)) (b : List Bool) : (pick b xs).map f=pick b (xs.map f) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x l ih=> cases b with
                      | nil=>rfl
                      | cons t B=> cases t <;> simp [pick,ih]
  have he (x : List (β → J X)) (b : List Bool) : ∀ i∈pick b x,i∈x := by
    induction x generalizing b with
    | nil=> cases b <;> simp [pick]
    | cons x l ih=> cases b with
                     | nil=>simp [pick]
                     | cons t b=> cases t
                                  · exact fun i h=> List.mem_cons_of_mem _ (ih _ _ (show i∈pick b l from h))
                                  intro i h
                                  exact (List.mem_cons).mpr ((List.mem_cons.mp (show _∈x::pick b l from h)).imp_right (ih _ _))
  exact ⟨by rw [hv,h.actual], fun i hi => h.tensors _ (he x b _ hi)⟩

theorem scope {T : Labels γ} (f : (β → Bill X)→γ → Bill X) (F : (β → J X) →ₗ[ℂ] γ → J X)
    (m : ∀ i, total ∘ (f i)= F (total ∘ i))
    (wide : ∀ i∈R.tensors B, F i∈R.tensors T) : Certified R T (xs.map f) (x.map F) := by
  refine ⟨?_ ,?_⟩
  · have e : (fun i : γ → Bill X => total ∘ i) ∘ f= F ∘ (fun i : β→ Bill X => total ∘ i) := funext m
    rw [← h.actual,List.map_map,List.map_map,e]
  intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact wide _ (h.tensors _ hj)

theorem accepted [DecidableEq β] [DecidableEq X] (l : List β) (n : l.Nodup) (p : Certificate.Hits B l)
    (s : List (Stub (β × X))) (b) (g : verify [] ((xs.map (bundleCost l)).map Bill.norm) b s=true) : Scan0 x b := by
  refine sends R B l n p x h.tensors _ ?_
  rw [← h.actual,List.map_map]
  have e : total ∘ bundleCost l=(fun d : β→Bill X => bundle l (total ∘ d)) :=
    funext fun i=> bundleAt l _ _ (fun _=>rfl)
  change Scan0 (List.map (fun d : β→Bill X => bundle l (total ∘ d)) xs) b; rw [← e,← List.map_map]; exact billed _ _ _ g
variable {d : Axis → Bill X → Bill X}

end Certified

section
variable [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α] [DecidableEq X]
theorem endorses (r : List (α×β)) (t : Picked ((A : Labels α).tensorProd B) r)
    {q : α → J X} (f : α→Bill X) (h : R.Reading A q) (hr : ∀ i,total (f i)=q i) :
    Certified R B (r.map (inspect A B f)) (r.map (Record.column B A q)) := by
  refine ⟨?_ ,?_⟩
  · rw [List.map_map, show (fun i : β → Bill X => total ∘ i) ∘ inspect A B f=Record.column B A q from
      funext fun a=> funext fun b=> inspect_c _ _ _ _ hr a b]
  rintro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have he : (Record.column B A q i) ∈ Record.allowed R B (space q) := by
    rw [Record.span_columns B h r t]
    exact subset_span (Set.mem_image_of_mem _ (by simp [hi]))
  exact he.1
end
end YM.GaugeFieldConstruction.Vouchers.Camera
