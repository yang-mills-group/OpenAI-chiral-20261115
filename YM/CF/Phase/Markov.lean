import YM.CF.Phase.Means

/-! Bounded-depth local random laws, finite-products convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Filter MeasureTheory Finset
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
namespace Sample
variable {I T : Type*} [DecidableEq I] [Fintype I] [MeasurableSpace T] [TopologicalSpace T] [CompactSpace T]
        [T2Space T] [SecondCountableTopology T] [BorelSpace T] [Nonempty T]
variable {μ : Measure T} [IsProbabilityMeasure μ]
lemma erase_one (F G : (I → T) → ℝ) (h : Continuous F) (u : Continuous G) (i : I) (p : ∀ v : I → T, ∫ t:T, F (Function.update v i t) ∂μ=1)
    (q : ∀ v : I→T, ∀ t:T, G (Function.update v i t)=G v) :
    (∫ v, F v*G v ∂Measure.pi (fun _=>μ)) = ∫ v, G v ∂Measure.pi (fun _=>μ) := by
  let j : I→Prop := (·=i)
  let Y := {a:I//a=i}; let Z := {a:I//¬a=i}
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I=>T) (·=i)
  have ht := (measurePreserving_piEquivPiSubtypeProd (fun _:I=>μ) (·=i)).symm e
  rw [← ht.integral_comp' (fun t=> F t*G t), ← ht.integral_comp' G]; change
    ∫ x, F (e.symm x)*G (e.symm x) ∂(Measure.prod _ _)=∫ x, G (e.symm x) ∂(Measure.prod _ _)
  rw [integral_prod_symm,integral_prod_symm]
  · congr 1; ext z -- tune
    let V := e.symm ((fun _=>Classical.arbitrary T),z)
    let Y := MeasurableEquiv.piUnique (fun _ : {a:I //a=i} => T)
    have hy0 := (measurePreserving_piUnique (fun _ : {a:I //a=i} => μ)).symm Y
    let fa := fun (l : Fintype {a : I//a=i}) => @Measure.pi {a : I//a=i} (fun _=>T) l _ (fun _ => μ)
    have he (l : Fintype {a : I // a=i}) : MeasurePreserving (⇑Y.symm) μ (fa l) := by
      convert! hy0 using 2
    -- next
    -- explicit fintype via subtype
    have hy := he (Subtype.fintype (·=i))
    rw [← hy.integral_comp' (fun x=> F (e.symm (x,z))*G (e.symm (x,z))), ← hy.integral_comp' (fun x=>G (e.symm (x,z)))]
    have heq (t:T) : e.symm (Y.symm t,z)= Function.update V i t := by
      ext k; by_cases g:k=i
      · subst k; simp only [Function.update_self]; simp [e,Y]
      simp [V,e,Y,g]
    simp_rw [heq,q]; rw [integral_mul_const,p]; simp
  · exact ht.integrable_comp_emb e.symm.measurableEmbedding |>.mpr (net_compact u)
  exact ht.integrable_comp_emb e.symm.measurableEmbedding |>.mpr (net_compact (h.mul u))

def density (A : Finset I) (f : I→(I→T)→ℝ) (v : I→T) : ℝ := ∏ i∈A, f i v
lemma dense_cont (A : Finset I) (f : I→(I→T)→ℝ) (h : ∀ i∈A, Continuous (f i)) : Continuous (density A f) := continuous_finsetProd _ h
-- normalization uses triangularity, including lack of dependencies on unassigned peers
lemma dense_norm (A : Finset I) (f : I→(I→T)→ℝ) (k : I→ℕ) (h : ∀ i, Continuous (f i))
    (g : ∀ i v, ∫ t:T, f i (Function.update v i t) ∂μ=1) (r : ∀ i j, i≠j → k i ≤ k j → ∀ v t, f i (Function.update v j t)=f i v) :
    ∫ v, density A f v ∂Measure.pi (fun _=>μ) = 1 := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · obtain ⟨i,hi,hk⟩ := exists_max_image A k hA
      rw [show density A f=f i*density (A.erase i) f by funext v; unfold density; change ∏ x∈A, f x v=_; nth_rw 1 [←insert_erase hi]; simp]; change ∫ v, f i v*_ ∂_=_
      rw [erase_one (f i) (density (A.erase i) f) (h i) (dense_cont _ f (fun i _=>h i)) i (g i), ih _ (erase_ssubset hi)]
      intro v t; exact prod_congr rfl fun j hj=>r j i (mem_erase.mp hj).1 (hk j (mem_erase.mp hj).2) v t
    simp [not_nonempty_iff_eq_empty.mp hA,density]
end Sample
end YM.CF.Phase
