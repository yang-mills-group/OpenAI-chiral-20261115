import YM.SU5.Selected.Rail.Keel
/-! # Synthesise negative samples. Later used at finite k for *same* frame.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
variable {k p:ℕ}(W:FaceL) (t:ℕ)
def keyboard (k p:ℕ)(W:FaceL)(t n:ℕ): EuclideanSpace ℂ (Fin p):=WithLp.toLp 2 (fun i:Fin p=> keystone k W (t+n+i.val))
local notation "g" k:max=> keyboard k p W t -- bind p variable previous
open Submodule
include W t
theorem unlock (z:k≥3): Submodule.span ℂ (Set.range (keyboard k p W t))=⊤ := by -- p explicit? section p earlier not used otherwise
 let U:= Submodule.span ℂ (Set.range (g k))
 apply orthogonal_eq_bot_iff.mp; refine (Submodule.eq_bot_iff _).mpr (fun a h=>?_); by_contra e; let Z:=a.ofLp; have he: Z≠0:=fun x=> e (WithLp.ofLp_injective 2 x)
 have ht(n:ℕ): ∑ i: Fin p, star (Z i)*(keystone k W (t+n+i.val))=0:=by
    rw [show (∑ i: Fin p, _) = inner ℂ a ((g k) n) from ?_]; · exact (mem_orthogonal' U a).mp h _ (subset_span (Set.mem_range_self _)) -- names
    rw [EuclideanSpace.inner_eq_star_dotProduct]; exact sum_congr rfl (fun i _=>mul_comm ..)
 obtain ⟨v,hp,u⟩:= ((tariff W Z z he).and (eventually_ge_atTop t)).exists
 let X i j:= star (Z i)*(keystone k W (4+v+(i:Fin p).val+(j:Fin p).val)*Z j)
 have hx(j:Fin p): ∑ i: Fin p, X i j=0:=by
    let n:=4+v+j.val-t; unfold X; simp_rw [show ∀ i:Fin p,4+v+i.val+j.val=t+n+i.val from fun i=> by unfold n; omega,←mul_assoc]; rw [←sum_mul,ht,zero_mul]
 change 0<(∑ i:Fin p, ∑ j:Fin p,X i j).re at hp; rw [sum_comm,sum_eq_zero (fun i _=> hx i),Complex.zero_re] at hp; exact lt_irrefl (0:ℝ) hp
lemma tenor (z:k≥3)(Y:Fin p→ℂ): ∃ f:ℕ →₀ ℂ, ∀ i:Fin p, Y i=∑ x∈f.support, f x* keystone k W (t+x+i.val):=by
 let v:=WithLp.toLp 2 Y; have hv:v∈Submodule.span ℂ (Set.range (g k)):=by rw [unlock W t z]; exact Submodule.mem_top
 rw [←Set.image_univ] at hv; obtain ⟨F,_,u⟩:=(Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv; refine ⟨F,fun i=>?_⟩; rw [show Y i=v.ofLp i from rfl,←u,Finsupp.linearCombination_apply,Finsupp.sum,WithLp.ofLp_sum]; rw [Finset.sum_apply]; exact sum_congr rfl fun j _=> rfl
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms unlock
#print axioms tenor
#check @tenor
