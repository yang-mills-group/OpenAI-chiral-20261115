import GaugeFieldConstruction.Temples
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI
section
variable {n:Side}{α M:Type} [Fintype α][NormedCommRing M][NormedAlgebra ℂ M]
variable (z:α→Force n)(P:Hub n)(w:Bool)(x:α→M)(K:Base z P w→ M)(Ω:Support (More n))
def profileT (f:Finset α→ M) := ∑ A:Finset α with PriceI z Ω A∧Charcoal P w Ω∧(ashC P z A).Nonempty, f A
-- noncomputable erase witness A. choose spill over total all. $$
lemma mural (h:Finset α→ M)(v:∀ (i:Base z P w),K i=h i.val) : sparkJet Ω (PourUp z x) (PourUp (roost z P w) K) = profileT z P w Ω (fun A=> (∏ j∈(A\ashC P z A), x j)* h (ashC P z A)):=by
 let L:=roost z P w
 rw[prize_line,← Fintype.sum_prod_type' (α₁:=Finset α) (α₂:=Base z P w)]
 let X(r: Finset α × Base z P w): Prop:=PriceI (Combo z P w) Ω (r.1.disjSum {r.2}); let A:=univ.filter X
 suffices H:(∑ x'∈ A, (∏ i∈x'.1,x i)*K x'.2) = _ from Eq.trans ?_ H -- may unify wrong. replace
 · rw [show A=univ.filter X from rfl,sum_filter]
   congr
 unfold profileT
 apply sum_bij (fun a h=> a.1∪ a.2.val)
 · rintro ⟨x,y⟩ a; have hh:PriceI (Combo z P w) Ω (x.disjSum {y}):= (mem_filter.mp a).2; obtain ⟨q,t,f⟩:=mixed_spec.mp hh; exact mem_filter.mpr ⟨mem_univ _, q,claimA hh, by dsimp only; rw[f]; exact y.property.inhab⟩
 · rintro ⟨x,y⟩ a ⟨u,v⟩ b e; obtain ⟨_,h₁,e₁⟩:= mixed_spec.mp (show PriceI (Combo z P w) Ω (x.disjSum {y}) from (mem_filter.mp a).2); obtain ⟨_,h₂,e₂⟩:= mixed_spec.mp (show PriceI (Combo z P w) Ω (u.disjSum {v}) from (mem_filter.mp b).2); dsimp only at e
   rw[e] at e₁; have he:y=v:= Subtype.ext (e₁.symm.trans e₂); subst y; rw [show x=u from ?_]
   ext i; by_cases r:i∈v.val
   · exact ⟨fun p=> False.elim (Finset.disjoint_left.mp h₁ p r),fun p=> False.elim (Finset.disjoint_left.mp h₂ p r)⟩
   exact (show i∈ x↔ i∈ (u∪v.val) from (by rw [←e]; simp [r])).trans (by simp [r])
 · intro b h; obtain ⟨p,v,t⟩:= (mem_filter.mp h).2; let a':Base z P w:=⟨ashC P z b,coast_C p v t⟩; let d:=b\ a'.val; have he:d∪ a'.val=b:=Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
   exact ⟨(d,a'),mem_filter.mpr ⟨mem_univ _,mixed_spec.mpr ⟨he.symm ▸ p,disjoint_left.mpr (fun {i} p b=> (mem_sdiff.mp p).2 b), by rw [he]⟩⟩,he⟩
 rintro ⟨x,y⟩ a
 obtain ⟨h1,t,e⟩:=mixed_spec.mp (show PriceI (Combo z P w) Ω (x.disjSum {y}) from (mem_filter.mp a).2); dsimp only; rw[e,v,Finset.union_sdiff_cancel_right t]
#print axioms mural
end
end YM.CF.Scree.Ing
end
