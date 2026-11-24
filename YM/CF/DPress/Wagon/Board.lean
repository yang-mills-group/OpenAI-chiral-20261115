import YM.CF.DPress.Wagon.Mirror
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
/-! Result at one equal-slot orientation arbitrary integer start in ticks. `T.η`: circumference in plane grid ticks. Only two classes used; no functional properties needed besides cost and the conformance Cauchy step. -/
namespace Race.Credit
variable {T:Race n L}{A:Style T} (μ:Reward T A){ℒ:Fixed.Test n→ℝ} (p: Bound T ℒ){n0:ℕ}
def Upper (A:Style T)(ℒ:Fixed.Test n→ℝ)(B:List Bool)(v:ℝ):Prop:=∀ (a:ℤ)(b:Bool)(F:Fixed.Test n), Credit A a b B F →ℒ F ≤ v
include p
theorem law_clock (t:n0*A.w=T.η)(hp:Even n0)(g:∀ b, Upper A ℒ (List.replicate n0 b) (μ.fee b ^ n0)) : ∀ F:List Bool, F.length=n0 → Upper A ℒ F (μ.cost F) :=by
 obtain ⟨m,rfl⟩:= hp; let Q(X):= tariff A μ ℒ X; obtain ⟨X,h0,v⟩:= seat (ℒ:=ℒ) (m:=m) A μ; have he:0 < m:=by have hx:=T.height_p; by_contra! u'; have hz:m=0:=(by omega); simp only [hz,add_zero,zero_mul] at t; omega
 have ht: Q X ≤ 1:=by
    by_contra! u
    cases X with
    | nil=>rw [List.length_nil] at h0; omega
    | cons a U=>
       let y:=Q (a::U); let b:=List.replicate (m+m) a; have he := final_Q (x:=y) A μ p t v (zero_lt_one.trans u) (K:=1) (b:=a) (w:=U) ⟨h0,rfl⟩ he Nat.one_pos; have hp:y ≤ 1:=by
          rw [he.2]; refine csSup_le (Set.nonempty_of_mem (t_tar A μ b)) ?_; rintro i ⟨n,b',X,T,rfl⟩; rw [div_le_one (μ.cost_p _)]; rw [μ.constant]; apply g _ _ _ _ T -- g.Upper.Trial
       exact hp.not_gt u
 intro F h a b X p'; let Z:= (hard A μ p F a b X p').trans ((v F h).trans ht); exact (div_le_one (μ.cost_p _)).mp Z
end Race.Credit
end YM.CF.DPress.Wagon
#print axioms YM.CF.DPress.Wagon.Race.Credit.law_clock
