import YM.CF.Continuum.Winter
import YM.CF.Continuum.Square

/-! # Relative and normalized Hermiticity -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {m B N L : Side} {U Ω : UNI (Single N)} {x y z η : ℝ}
local notation "Λ" => CSide m B
variable {e v a η r C : ℝ} {j n : ℕ} {hj : Odd L.val}{Y : Pricing j L hj (Thread j)}
  {P : Grasp Y B e} {X : GramM (CSide m B)} {K : Loom (CSide m B)}
local notation "U" => partitionZ X P K
set_option quotPrecheck false
local notation "Uₓ" => fun i : Orbit Λ => Complex.exp (-X.v) • denZ X P K i -- tune quotPrecheck
lemma priorTag : ∀ᵐ i∂city N, Injective (priorP i.2) := (measurePreserving_snd («μ»:=prior group (More N)) («ν»:=depot N)).quasiMeasurePreserving.ae sepT
variable {C' : Hom.Credit}
variable (t : Hom.InterestX C' (CSide m B) X.J) (h0 : 1 ≤ j) (D : Pearl P) (Ft : Stamped j L hj Y)
  (H0 : Roof (CSide m B) v e n K) (F1 : IncX (fun _ => True) X.F X.p x y) (F2 : IncX (fun _ => True) X.slip X.p x z) (Fx : Dark (fun _ => True) X.K X.p x η) (hp : P.roundZ ≤ (CSide m B).val)
include t h0 D Ft H0 F1 F2 Fx hp
lemma relative_symmetry (i : Axis) : expectationsMirror m B i (moment Uₓ) := by
  apply by_density; exact (priorTag (N:=Λ)).mono fun y v=> density_turn C' t h0 D Ft H0 F1 F2 Fx i y v hp
lemma price_isReal : star (Complex.exp (-X.v)*U)=Complex.exp (-X.v)*U :=by
  have hv := relative_symmetry t h0 D Ft H0 F1 F2 Fx hp 3 ((allObs Λ).one_mem); rw [flipTime_one,read_ket_scalar,read_beam] at hv; exact hv.symm
lemma mirror_normal (i : Axis) : expectationsMirror m B i (finiteForm Y P X K) := by
  intro q h
  rw [relative, relative, star_div₀, price_isReal t h0 D Ft H0 F1 F2 Fx hp, relative_symmetry t h0 D Ft H0 F1 F2 Fx hp i h]
omit t h0 D Ft H0 F1 F2 Fx hp
end YM.CF.Window
