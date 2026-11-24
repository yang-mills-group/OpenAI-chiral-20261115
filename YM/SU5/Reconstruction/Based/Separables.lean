import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Complex.Basic
/- linear finite-proof auxiliary. Don't assume operators commute. -/
set_option autoImplicit false
noncomputable section
open Function Finset
open scoped Topology BigOperators Classical
namespace YM.CF.Segregate
variable {X E:Type*}[DecidableEq X][AddCommGroup E][Module ℂ E]
lemma isolate_by_rot {Y:Finset X}{x:X}(p:x∈ Y)(v:X → E)
    (h:∀ i∈ Y,i≠x→∃ (U:E→ₗ[ℂ]E)(φ:X→ℂ), φ x≠φ i∧ ∀ j∈ Y,U (v j)=φ j • v j) (C : (∑ i∈ Y,v i)=0): v x=0:=by
 induction Y using Finset.strongInductionOn generalizing v with
 | _ Y ih=>
    by_cases b:Y={x}; · simpa only [b,sum_singleton] using C
    obtain ⟨y,t,w⟩:∃ y∈ Y,y≠ x:=by by_contra q; push Not at q; exact b (Finset.Subset.antisymm (fun i u=> by rw [q _ u]; exact mem_singleton_self _) (singleton_subset_iff.mpr p)) -- check implicit i binder
    obtain ⟨U,φ,d,hU⟩:= h y t w
    let T:=Y.erase y; have h':T⊂ Y:= erase_ssubset t; have hp:x∈ T:=mem_erase.mpr ⟨Ne.symm w,p⟩
    let J(i):=(φ i-φ y) • v i
    have sumJ:(∑ i∈ T,J i)=0:=by
       rw [← zero_add (∑ i∈ T, _),← show J y=0 from (by dsimp only [J]; rw [sub_self,zero_smul]), Finset.add_sum_erase Y J t]
       simp_rw [J,sub_smul,sum_sub_distrib]; rw [← Finset.smul_sum]; rw [(show (∑ i∈ Y,φ i • v i)= _ from (by exact (by
          trans ∑ i∈ Y,U (v i); exact sum_congr rfl fun i p=>(hU i p).symm; exact (map_sum U _ _).symm) : (∑ i∈ Y,φ i • v i)= U (∑ i∈ Y,v i)))]; simp [C]
    have t: J x=0:= ih _ h' hp J (fun i w u=>by obtain ⟨F,π,t,f⟩:= h i (mem_of_mem_erase w) u; exact ⟨F,π,t,fun i w=> by unfold J; rw [map_smul,f _ (mem_of_mem_erase w),smul_comm]⟩) sumJ
    exact (smul_eq_zero.mp t).resolve_left (sub_ne_zero.mpr d)
end YM.CF.Segregate
