import YM.CF.Petal.Cabin
set_option linter.unusedSectionVars false

/-! Paying the inputs in the exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Branch NormedSpace Function Finset MeasureTheory Phase Sample Filter
variable {Y I M D E G : Type*} [DecidableEq Y] [Fintype Y] [DecidableEq I] [MeasurableSpace M] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [BorelSpace M] [Nonempty M] [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E] [TopologicalSpace D] [FirstCountableTopology D] [LocallyCompactSpace D] {μ : Measure M} [IsProbabilityMeasure μ] {L : Lodge Y E D G} {V : Cabin μ L}
variable {f : I → Mood Y D M →E} {X Q : I→Seal Y} {b : Branch.Field Y} {A : Seal I} {w : I→ℝ} {r : ℝ}
section mote
abbrev secA (x : E) := exp x-1
lemma ignition (K : Bell Y E) (X : Seal Y) (x : E) (p : x∈K.store X) (u : ℝ) (h : K.fare x≤ u) (v : u≤1/2) : secA x∈K.store X ∧ K.fare (secA x) ≤ 2*u := by
  let F : ℕ→E := fun n=> (n.factorial:ℝ)⁻¹ • x^n
  have he : 0≤u := (Bell.starL _).trans h
  have hv n : K.fare (F n) ≤ u^n := by
    have ht i : K.fare (x^i) ≤ u^i := by
      induction i with
      | zero=> rw [pow_zero,pow_zero,K.single]
      | succ i ih=> rw [pow_succ,pow_succ]; exact (K.times ..).trans (mul_le_mul ih h (Bell.starL _) (by positivity))
    unfold F; rw [K.scale,Real.norm_of_nonneg (by positivity)]; apply le_trans _ (ht n)
    exact mul_le_of_le_one_left (Bell.starL _) (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos n))
  obtain ⟨H,hx⟩:= Pool.sized u he (v.trans_lt (by norm_num))
  let P : ℕ→E := fun n=> F (n+1)
  have hh : Summable P := H.of_norm_bounded (fun i=> (K.normF _).trans (hv (i+1)))
  have ht : secA x=∑' i,P i := by
    unfold secA; rw [exp_eq_tsum ℝ]; change (∑' i,F i)-_= _; have hx := ((summable_nat_add_iff 1).mp hh).sum_add_tsum_nat_add 1
    rw [← hx, show ∑ i∈range 1, F i=1 by simp [F]]; abel
  rw [ht]; refine ⟨(K.wallL X).mem_of_tendsto hh.hasSum (Eventually.of_forall (fun s=>Subalgebra.sum_mem _ (fun i _=>Subalgebra.smul_mem (K.store X) (Subalgebra.pow_mem _ p _) (R:=ℝ) _))), (Bell.aceL _ _ (fun i=>hv (i+1)) H).trans ?_⟩ -- tune args
  rw [hx]; apply (div_le_iff₀ (by linarith)).mpr; nlinarith
lemma prod_fire (h : ∀ i∈A, Manifest V (f i) (w i) (X i) (Q i)) : Manifest V (fun x=>∏ i∈A,f i x) (heavy w A) (roof X A) (roof Q A) := by
  induction A using Finset.induction_on with
  | empty=> simp only [prod_empty,heavy,roof_empty]; exact Manifest.free
  | insert i A p ih=>
    have ht := (h i (mem_insert_self ..)).blend (ih (fun i q=>h i (mem_insert_of_mem q)))
    simp_rw [heavy,prod_insert p,roof,biUnion_insert]; exact ht
end mote
open Manifest
structure Team (L : Lodge Y E D G) (b : Branch.Field Y) (V : Cabin μ L) (X Q : I→Seal Y) (w : I→ℝ) (f : I→Mood Y D M→E) (A : Seal I) (r : ℝ) : Prop where
  positive : 0<r
  placed i (p:i∈A) : w i≠0 → Grove b (X i)
  allowed i (p:i∈A) : Manifest V (f i) (w i) (X i) (Q i)
  mass z : ∑ i∈ hose X z A,rent (r+2) (X i)*w i ≤ 1/8

def airport (V : Cabin μ L) (f : I→Mood Y D M→E) (i : Seal I) := motor V fun x=> ∏ j∈i, secA (f j x)
variable (H : Team L b V X Q w f A r)
include H
lemma per_one (p : I) (g : p∈A) : w p ≤1/2 := by
  by_cases k:w p=0; rw [k]; norm_num
  have hh : ∀ B, Grove b B → B.Nonempty := by intro B h; cases h <;> simp
  obtain ⟨z,hz⟩:= hh _ (H.placed p g k)
  have he : p∈hose X z A := mem_filter.mpr ⟨g,hz⟩
  have hv := H.mass z
  have hx := (single_le_sum (fun i (g:i∈hose X z A)=>mul_nonneg (rent_pos ..).le (H.allowed i (mem_filter.mp g).1).price) he).trans hv
  exact ((le_mul_of_one_le_left (H.allowed p g).price (rent_one (by linarith [H.positive]) _)).trans hx).trans (by norm_num)
lemma teamW (p : I) (g : p∈A) : Manifest V (fun x=>secA (f p x)) (2*w p) (X p) (Q p) := by
  letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have he := H.allowed p g; have ht x (u:x∈booth V) := ignition L.toBell (X p) (f p x) (he.stock x u) _ (he.avail x u) (per_one H p g)
  refine ⟨mul_nonneg (by norm_num) he.price,he.pad,fun x g=>(ht x g).2,fun x g=>(ht x g).1,(exp_continuous.comp_continuousOn he.ct).sub continuousOn_const, he.records,fun p q u l=> congrArg _ (he.same p q u l),fun g=>he.weights g,fun t x g=>?_⟩
  unfold secA; rw [map_sub,map_one,map_exp (L.rule t) (L.ct t),he.attire _ x g]
lemma crewW {S : Seal I} (u : S⊆A) : Manifest V (fun x=> ∏ i∈S, secA (f i x)) (heavy (fun i=>2*w i) S) (roof X S) (roof Q S) := prod_fire (fun i p=>teamW H i (u p))
lemma club : Offer L b A X (fun i=>2*w i) (airport V f) r := by
  refine ⟨fun i g l=>H.placed i g (right_ne_zero_of_mul l),fun S p=>(crewW H p).flush,fun x=>?_,fun i j p q u l x=>?_,fun i p=>(teamW H i p).price,fun x=>?_⟩
  · unfold airport motor bet; simp_rw [prod_empty]; rw [integral_smul_const,sails_all,one_smul]
  · unfold airport; simp_rw [prod_union u]; exact namepath (crewW H p) (crewW H q) l x
  simp_rw [mul_left_comm _ (2:ℝ), ←mul_sum]; apply (mul_le_mul_of_nonneg_left (H.mass x) (show 0 ≤ (2:ℝ) by norm_num)).trans; norm_num
lemma Floor_eq (x : D) : motor V (fun x=> exp (∑ i∈A,f i x)) x=Floor (airport V f) A x := by
  unfold motor Floor airport motor bet
  letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have he (y) : exp (∑ i∈A, f i (x,y))=∑ j∈A.powerset, ∏ k∈j, secA (f k (x,y)) := by rw [←prod_add_one,exp_sum]; simp [secA]
  simp_rw [he,smul_sum]
  exact integral_finsetSum _ (fun i l=>net_compact ((crewW H (mem_powerset.mp l)).cashG x))
theorem hospital {C : ℝ} (h : 0≤ C) (v : ∀ (x:Y) m, ((bay b x m).card:ℝ) ≤ C*((m:ℝ)+1)^4) : ∃ (K : Seal Y→D→E) (d : Seal Y→ℝ), Charge L b (r/2) (bulk r C*(1/3)) K d ∧ ∀ x:D, motor V (fun x=>exp (∑ i∈A,f i x)) x=exp (∑ S:Seal Y,K S x) := by
  obtain ⟨K,d,p,V⟩:= forest (club H) H.positive h v; exact ⟨K,d,p,fun x=> (Floor_eq H x).trans (V x)⟩
end YM.CF.Petal
