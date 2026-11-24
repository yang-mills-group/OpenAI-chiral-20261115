import YM.CF.BPress.Grid.Rim
/- FD mesh (max-barycentric variant). Err.All reach prices in physical pixels.
This subdivision is piecewise linear. Sample on integer grids; for producing an
extension it suffices to control pair prices there instead of on real simplexes. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Finset Metric Filter
open scoped Pointwise Topology BigOperators NNReal ENNReal Classical
variable {I:Type*}[Fintype I]{m:ℕ}
abbrev Ramp(I:Type*)(m:ℕ) := I → Fin (m+1)
namespace Ramp
variable (x y:Ramp I m)
abbrev right(m:ℕ):Fin (m+1):=⟨m,by omega⟩
abbrev supportT:Ramp I m→ Finset I:=fun F=>univ.filter fun i=> F i ≠ 0 -- omit x.
abbrev Live : Prop:=∃ i,x i=right m
def On (S:Finset I) : Prop:= Live x∧ supportT x⊆ S
def DistU (i j:Fin (m+1)):= i.val - j.val+(j.val-i.val)
abbrev d :ℕ:= univ.sup fun i=> DistU (x i) (y i)
lemma tick(i:I): DistU (x i) (y i) ≤ d x y:=le_sup (f:=fun i=>DistU (x i) (y i)) (mem_univ _)
lemma dusk {k:ℕ}: d x y ≤ k ↔ ∀ i, DistU (x i) (y i) ≤ k:= by simp [d]

lemma right_pos (p:0<m): right m≠0:= by simp only [right, ne_eq, Fin.ext_iff, Fin.val_zero]; omega
include I in
lemma wallet : d x y≤m:= (Ramp.dusk ..).mpr fun i=>by unfold DistU; have hx:= (x i).isLt; have hy:= (y i).isLt; omega
lemma symmetry : d x y=d y x:= by unfold d; exact Finset.sup_congr rfl fun i _=>  Nat.add_comm .. 
variable {x y} {U V:Finset I}
lemma mem_h(i:I):i∈supportT x ↔ x i≠0:=by simp [supportT]
lemma on_full (x:Ramp I m)(p: Live x) : On x univ:=⟨p,subset_univ _⟩
lemma bright(p:On x U)(v:U⊆V): On x V:=⟨p.1,p.2.trans v⟩
lemma exists_right (h:0<m)(u:On x U) :∃ i∈ U,x i=right m:=by obtain ⟨i,v⟩:= u.1; exact ⟨i,u.2 (mem_h _|>.2 (v ▸ right_pos h)),v⟩
def trim (x:Ramp I m) (V:Finset I):Ramp I m:= Set.indicator (V:Set I) x -- outside trivial
lemma inside{x:Ramp I m}{V:Finset I}{i:I}(p:i∈V): trim x V i=x i:= if_pos p
lemma outside{x:Ramp I m}{V:Finset I}{i:I}(p:i∉V):trim x V i=0:=if_neg p
lemma support_trim (x:Ramp I m)(V:Finset I):supportT (trim x V)= supportT x ∩ V:=by
 ext i; rw [mem_inter,mem_h,mem_h]; by_cases p:i∈V; rw [inside p]; simp [p]; rw [outside p]; simp [p]
lemma dark(p:On x V){i:I}(h:i∉ V):x i=0:=not_not.mp (fun g=>h (p.2 ((mem_h _).2 g)))
lemma together (p:On x U)(t:On y V)(v:d x y<m) : On (trim x V) (U ∩ V) ∧ d x (trim x V)≤d x y ∧ d (trim x V) y≤d x y:=by
 refine ⟨⟨?_ ,by rw [support_trim]; exact inter_subset_inter p.2 (Subset.refl _)⟩,(Ramp.dusk ..).2 ?_,(Ramp.dusk ..).2 ?_⟩
 · obtain ⟨i,y'⟩:= p.1; have hi:i∈V:=by
      by_contra w; have g:DistU (x i) (y i) < m:= lt_of_le_of_lt (tick x y i) v; rw [y',dark t w] at g; unfold DistU at g; simp only [Fin.val_zero] at g; change m-0+(0-m)< m at g; omega
   exact ⟨i,(inside hi).trans y'⟩
 · intro i; by_cases h:i∈V; rw [inside h]; unfold DistU; omega
   rw [outside h, ← dark t h]; exact tick x y i
 intro i; by_cases h:i∈ V; rw [inside h]; exact tick x y i; rw [outside h,dark t h]; simp [DistU]
-- book distances scale
abbrev δR(x y:Ramp I m):ℝ:= (d x y:ℝ)/(m:ℝ)
lemma δp : 0≤ δR x y:=by unfold δR; positivity
lemma δs : δR x y= δR y x:=by unfold δR; rw [symmetry]
-- full pair Price.Facets -- no continuity assumptions needed for meas extension.F
open BPress.Grid
abbrev Speed {V:Type*}[PseudoMetricSpace V](A:Set (Ramp I m))(F:Ramp I m→V)(p:ℝ):Prop:= ∀ x∈A,∀ y∈A,dist (F x) (F y)≤ p* δR x y
abbrev facet (D:Finset I):Set (Ramp I m):={x| On x D}
abbrev boundary (D:Finset I):Set (Ramp I m):={x| Live x∧supportT x ⊂ D}
abbrev full {V:Type*}[PseudoMetricSpace V](S:Finset I)(F:Ramp I m→V):=Speed (facet S) F
lemma enlarge {E:Type*}[PseudoMetricSpace E]{A B:Set (Ramp I m)}{F:Ramp I m→E}{a b:ℝ}(p:Speed A F a)(t:B⊆A)(v:a ≤ b):Speed B F b:=fun x hx y hy=> (p _ (t hx) _ (t hy)).trans (mul_le_mul_of_nonneg_right v δp)
lemma border (p:x∈boundary U) :On x U:= ⟨p.1, Finset.Subset.trans (Finset.Subset.refl _) (Finset.ssubset_iff_subset_ne.mp p.2).1⟩
-- Lift gluing cost: agreement at shared supports. If apart just diameter.
theorem join_cost {E:Type*}[PseudoMetricSpace E]{C:Set E}{F:Ramp I m→E} (u:Finset I)(p:0<m){a b:ℝ}(hz:0 ≤ b)(h:0≤a) 
    (hc:∀ x∈C,∀ y∈C,dist x y≤ b)(hy: Set.MapsTo F (boundary u) C)
    (w:∀ v ⊂ u,full v F a): Speed (boundary u) F (2*a+b):=by
 intro x h' y t; obtain ⟨c,l⟩:=h'; obtain ⟨k,v⟩:=t; by_cases he: d x y<m; swap; · rw [δR,show d x y=m from le_antisymm (wallet x y) (le_of_not_gt he),div_self (by positivity),mul_one]; exact (hc _ (hy ⟨c,l⟩) _ (hy ⟨k,v⟩)).trans (le_add_of_nonneg_left (by positivity))
 let f:=supportT x; let g:= supportT y; let z:= trim x g; obtain ⟨p,hq,gq⟩:= together (show On x f from ⟨c,Subset.refl _⟩) (show On y g from ⟨k,Subset.refl _⟩) he
 have hx: dist (F x) (F z)≤a*δR x y:=(w f l x ⟨c,Subset.refl _⟩ z (bright p inter_subset_left)).trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Nat.cast_le.mpr hq) (by positivity)) h)
 have hy: dist (F z) (F y) ≤ a*δR x y:= (w g v z (bright p inter_subset_right) y ⟨k,Subset.refl _⟩).trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Nat.cast_le.mpr gq) (by positivity)) h)
 refine (dist_triangle _ (F z) _).trans ?_; have hv:=mul_nonneg hz (δp (x:=x) (y:=y)); nlinarith only [hx,hy,hv]
end Ramp
end YM.CF.DPress.FD
