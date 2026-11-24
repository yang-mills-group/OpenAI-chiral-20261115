import Organdy.Walrus
import Organdy.Dune
import YM.SU5.Interaction.Draught.Heater
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Py Py.Rate LocalLimit Preparation Pitching.Focus
open Buffered.Afterglow.Tower.VacuumSelection

lemma warmLease {P:Spine}(t:P.FirstLease) :
    Heater P.par P.run:=by
  obtain ⟨n,C,v⟩:=t.tint
  obtain ⟨Pay,k0,g0,S,x,y,a,f,d,b,c,e,R⟩:=v.fromCrew
  exact warmDust P.run (R.fuels (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge x y f a b c) t.roster.prepared

open Vow
abbrev Ledger (p:BudgetPoint)(h:ℝ)(q:ℕ)(a:ℝ)(F:ForceBudget n): Prop :=
    ∃ r:Aura n→Support (More n)→ℝ,
      (∀ X:Aura n,∀ D⊆X.val,Fray p h (cipherK q) X D (settleK F X D) (r X D)) ∧
      ∀ o:Seat n,tallB (roofL r 1) p.B (p.supportExponent+1) o ≤ a

lemma dusty {F:ForceBudget n} (t:Dust F p h (cipherK q) 1 a) :
    Ledger p h q a F:=by
  obtain ⟨K,C,z⟩:=t
  refine ⟨C,fun X D hd=>?_,?_⟩
  · by_cases e:D.Nonempty
    · rw [z.card,eachFace _ _ _ e hd]
      exact z.fray _ _ hd
    rw [Finset.not_nonempty_iff_eq_empty.mp e,settle0,(z.dead _).2]
    exact ⟨Medal.zeroT,fun i t=>(t rfl).elim⟩
  rw [show roofL C 1=hymn C from ?_]
  · exact z.tall
  funext i
  unfold roofL Vow.hymn
  simp only [duty,ite_self,one_mul]
  symm
  apply sum_subset (fun j hj=>mem_powerset.mpr (mem_filter.mp hj).2.2)
  exact fun j t v=>if h':j.Nonempty then False.elim (v (mem_filter.mpr ⟨mem_univ _,h',mem_powerset.mp t⟩))
        else (Finset.not_nonempty_iff_eq_empty.mp h') ▸ (z.dead _).2
