import Anomaly.Signal
import YM.SU5.Exchange.Seed.Pip
import YM.SU5.Exchange.Force.Cloud
/-! # Feed actual Force to OrbitRack
Maintain per-flag and halo qualification in this currency as well. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch
variable {n:Side}
local notation "Φ" => Force n

def top_rent (c : Φ → ℝ)(X : Aura n)(D:Support (More n)) : ℝ:=∑ i∈ motV X D,c i

lemma rent_old (p:BudgetPoint)(h L F:ℝ)(K:ForceBudget n)(s:ℕ)(g:FlagWidth p K s)
    (t:Mew.SanB K (giftK p L) p h (fun _=>F))(hx:0≤h) :
    ∃ r: Cadre.Tape (A:= Seat n), (∀ X,∀ D ⊆ (X:Aura n).val,Fray p h s X D (settleK K X D) (r X D)) ∧
      (∀ X:Aura n,r X ∅=0) ∧ ∀ o:Seat n,tallB (Cadre.roofL r 1) p.B L o ≤ chi_f p.order * F := by
  obtain ⟨C,u,v⟩:= t.bit -- tune layers
  let c:=fun i:Φ=> chi_f p.order*C i
  let R:=top_rent c
  have H(X:Aura n): R X ∅=0:=sum_eq_zero fun i w=> False.elim (i.property.1.ne_empty (mem_filter.mp w).2.2)
  refine ⟨R,?_,H,?_⟩
  · intro X D d
    refine Fray.sumP _ _ _ fun i w => ?_
    have ht : Fray p h s (lordD i) (extraD i) (K i) (c i):=⟨(Vow.rimP (u i) hx).2,g i⟩
    rwa [(mem_filter.mp w).2.1,(mem_filter.mp w).2.2] at ht
  intro o
  rw [Sour.age_t,show Sour.urnL R=0 from funext H, show tallB (0:Aura n→ℝ) _ _ _=0 from by simp [tallB]]
  rw [zero_add,one_mul]
  apply le_trans ?_ (mul_le_mul_of_nonneg_left (v o) (Vow.spicy_f _))
  let σ(i:Φ) := giftK p L i o * c i
  apply le_of_eq
  calc
    _ = ∑ i:Φ, σ i := ?_
    _ = chi_f p.order * ∑ i:Φ, giftK p L i o*C i := by unfold σ c; rw [mul_sum]; exact sum_congr rfl fun i _=>by ring
  unfold tallB Vow.hymn R top_rent
  simp_rw [sum_mul]
  -- instead of assuming any tally for EMPTY support, calculate exp with exactly these indices
  rw [←sum_fiberwise_of_maps_to (t:=(univ:Finset (Aura n))) (g:=lordD) (s:=univ) (fun _ _=>mem_univ _)] -- rew RHS
  rw [sum_filter]
  apply sum_congr rfl; intro X _
  let W:= univ.filter fun i:Φ=>lordD i=X
  by_cases g : o ∈ X.val
  · rw [if_pos g, ← sum_fiberwise_of_maps_to (s:=W) (t:=fullD X) (g:=extraD) (fun i w=> mem_filter.mpr ⟨mem_univ _,i.property.1,(mem_filter.mp w).2 ▸ (show extraD i ⊆ (lordD i).val from i.property.2)⟩)]
    apply sum_congr rfl; intro D v
    let Y:= motV X D
    rw [show motV X D=W.filter (fun i=> extraD i=D) from (by ext; simp [W, motV])]
    apply sum_congr rfl; intro i u; unfold σ giftK
    have he := (mem_filter.mp (show i ∈ Y from ?_)).2.1
    · rw [if_pos (show o∈i.val.1.val.2 from (show o∈ (lordD i).val from he.symm ▸ g))]; rw [show i.val.1.val.2=X.val from congrArg Subtype.val he]; exact mul_comm ..
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp u).1).2,(mem_filter.mp u).2⟩
  rw [if_neg g]; symm; refine sum_eq_zero fun i u=>?_; unfold σ giftK; rw [if_neg (show o∉_ from (show o ∉ (lordD i).val from (mem_filter.mp u).2.symm ▸ g)),zero_mul]
end YM.CF.Vow.TreasuryFog
