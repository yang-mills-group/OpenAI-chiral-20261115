import YM.CF.Fixed.Voltage.Tuple
/-! Any sweep symmetry systemic (cf Fixed.Stencil, generalizes it). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson Cube MeasureTheory Spire
open SU Lat Fock Scroll Tulip Skye Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
attribute [local instance] opCStarAlgebra

variable {N : Side} (s:Sweep N)
open Salt Ione
variable {U:UNI SpinIdx} (t:JetS s.s s.charge (detX s.s) U)
abbrev tintY (s:Sweep N)(U:UNI SpinIdx):= paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) N)
variable {Q:Sweep N→Prop} {p:BudgetPoint} {h d:ℝ}
include t
lemma exponent_review {F:RegBudget N} (H: IncX Q F p h d) (he: Q s) (uR : Pane N) :
    exponentL p F (flashA s uR)=tintY s U (exponentL p F uR):=by
  have hP (u:Scree.Hub N) : F (moveHub s u) (flashA s uR)=tintY s U (F u uR):= H.face s he _ t u uR
  unfold exponentL; rw [map_sum];
  rw [← Equiv.sum_comp (scope_q s) (fun v=>numbE p.threshold v.val.2 (F v) (flashA s uR))]; apply Finset.sum_congr rfl
  intro j _; unfold numbE; by_cases hx:pingS p.threshold j.val.2 uR
  · rw [Set.indicator_of_mem (show (flashA s uR)∈ _ from (glowA _ j.val.2 s uR).2 hx), Set.indicator_of_mem (show uR∈_ from hx)]
    exact hP j
  rw [Set.indicator_of_notMem (show (flashA s uR)∉ _ from mt (glowA _ j.val.2 s uR).1 hx), Set.indicator_of_notMem (show uR∉ _ from hx),map_zero]

omit t
private theorem forceMask (p : BudgetPoint) (u:Finset (Force N)) (V:Orbit N) :
    let H:= u.map (fanZ s).toEmbedding
    (coverF p H (flashA s V.1) ∧ Set.PairwiseDisjoint (H:Set (Force N)) (fun x=> x.val.1.val.2)) ↔
      coverF p u V.1 ∧ Set.PairwiseDisjoint (u:Set (Force N)) (fun x=> x.val.1.val.2) := by
  classical
  intro H
  let t:=fanZ s
  have hu:(H.biUnion fun j=>j.val.2)=actY s (u.biUnion fun j=>j.val.2):=by
    ext x; simp only [actY,H, Finset.mem_map,mem_biUnion]
    constructor
    · rintro ⟨_,⟨j,hj,rfl⟩,hx⟩
      obtain ⟨y,hy,eq⟩:= Finset.mem_map.mp hx
      exact ⟨y,⟨j,hj,hy⟩,eq⟩
    rintro ⟨y,⟨j,hj,hy⟩,eq⟩
    exact ⟨t j,⟨j,hj,rfl⟩, eq ▸ Finset.mem_map_of_mem _ hy⟩
  apply and_congr
  · unfold coverF; rw [hu, flagsA]; exact (_root_.Finset.map_injective _).eq_iff
  have hp (j k:Force N) : Disjoint (t j).val.1.val.2 (t k).val.1.val.2 ↔ Disjoint j.val.1.val.2 k.val.1.val.2 := Finset.disjoint_map _
  constructor
  · intro p a g b k u; exact (hp a b).1 (p (Finset.mem_map_of_mem _ g) (Finset.mem_map_of_mem _ k) (t.injective.ne u))
  intro p a g b k u
  obtain ⟨j,hj,rfl⟩:= Finset.mem_map.mp g; obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp k
  exact (hp ..).2 (p hj hl (fun r=>u (congrArg t r)))

include t
lemma fueled_review {F: ForceBudget N} (H:Dark Q F p h d) (he: Q s) (V:Orbit N)
    (hp:Injective (priorP V.2)) : fueled p F ((flashA s V.1,bun s V.2))= tintY s U (fueled p F V):=by
  classical
  have hf (x:Force N) : F (moveForce s x) ((flashA s V.1,bun s V.2))= tintY s U (F x V):= H.face s he _ t x V.1 V.2 hp
  let t:=fanZ s; let K:=Equiv.finsetCongr t; let A(x:Orbit N)(U:Finset (Force N)) : Prop:= coverF p U x.1 ∧ Set.PairwiseDisjoint (U:Set (Force N)) (fun x=> x.val.1.val.2)
  let f(x:Orbit N) (U:Finset (Force N)) := if A x U then ∏ j∈U, Scree.clamp p j (F j) x else 0

  have heq(x:Orbit N) : fueled p F x=∑ i:Finset (Force N), f x i :=by unfold fueled; congr!
  rw [heq,heq,map_sum,←Equiv.sum_comp K (f ((flashA s V.1,bun s V.2)))]
  apply Finset.sum_congr rfl; intro x _; unfold f; change _=
    tintY s U (if A V x then (_:Cipher N) else 0)
  have e : A ((flashA s V.1,bun s V.2)) (K x) ↔ A V x:= forceMask s p x V
  by_cases g: A V x; swap
  · rw [if_neg g, if_neg (mt e.mp g), map_zero]
  rw [if_pos g,if_pos (e.mpr g)]
  rw [show K x=x.map t.toEmbedding from rfl, Finset.prod_map,map_prod]
  apply Finset.prod_congr rfl; intro y _
  have hv : boundF (t.toEmbedding y) p ((flashA s V.1,bun s V.2)).1 ↔ boundF y p V.1 := by
    unfold boundF
    change pingS p.threshold (actY s y.val.1.val.2 \ actY s y.val.2) (flashA s V.1) ↔ _
    unfold actY; rw [←Finset.map_sdiff]; exact glowA ..
  by_cases b:boundF y p V.1
  · unfold Scree.clamp
    rw [if_pos (hv.mpr b), if_pos b]; exact hf y
  unfold Scree.clamp; rw [if_neg b, if_neg (mt hv.mp b),map_zero]

end YM.CF.Fixed.Voltage
