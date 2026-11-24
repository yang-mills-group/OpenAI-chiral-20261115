import Mathlib.Analysis.Matrix.PosDef
import YM.CF.BProof.Chess.Suit
import YM.CF.BProof.Fog.Fro
import YM.CF.Fixed.Functional
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Scroll Spire Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexOrder Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Skye Scree Bide Half Tulip
attribute [local instance] opCStarAlgebra
open Window.Unfit
variable {N L:Side}(i:Axis){s t h z w:ℕ}(p:0<w)
local notation "Gkt"=> shade N i true w
local notation "Wt"=> Fixed.reflectSweep N i
-- elementary root using positivity of quadratic wrt all pairs
section
open Matrix
lemma GramValve (A B X Y:ℂ)(u:∀ a b:ℂ,0≤ star a*a*A+star a*b*X+star b*a*Y+star b*b*B) : ‖X‖^2 ≤ ‖A‖*‖B‖:=by
 have h : 0 ≤ A:=by simpa using u 1 0
 have p:0 ≤ B:=by simpa using u 0 1 -- semicolon
 have hx(C:ℂ)(p:0≤C): (C.re:ℂ)=C:=Complex.ext rfl (Complex.nonneg_iff.mp p).2
 obtain ⟨D,g,rfl⟩ : ∃ D:ℝ, 0≤D∧ A= (D:ℂ):=⟨_,(Complex.nonneg_iff.1 h).1,(hx _ h).symm⟩; obtain ⟨R,k,rfl⟩ :∃ R:ℝ,0 ≤R∧B=(R:ℂ):=⟨_,(Complex.nonneg_iff.1 p).1,(hx _ p).symm⟩
 have hz : Y=star X:=by
    have ht:=(Complex.nonneg_iff.1 (u 1 1)).2; have he:= (Complex.nonneg_iff.1 (u 1 Complex.I)).2; simp [Complex.mul_im] at ht he; apply Complex.ext <;> simp <;> linarith
 subst Y; let V: Matrix (Fin 2) (Fin 2) ℂ:= !![(↑D :ℂ),X;star X,(↑R:ℂ)]; have ht:V.PosSemidef:=by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,fun x=>?_⟩
    · apply Matrix.IsHermitian.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [V] -- tune
    apply (u (x 0) (x 1)).trans_eq; simp only [dotProduct,Matrix.mulVec,V,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,Pi.star_apply, add_zero]; simp; ring
 have hh := ht.det_nonneg; rw [Matrix.det_fin_two] at hh; change 0 ≤ (↑D:ℂ)*(↑R:ℂ)-X*star X at hh; rw [Complex.star_def,Complex.mul_conj, ←Complex.ofReal_mul, ←Complex.ofReal_sub] at hh; have hv:0 ≤ D*R-Complex.normSq X:=(Complex.nonneg_iff.1 hh).1; rw [Complex.sq_norm,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg g, Real.norm_of_nonneg k]; linarith
end
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩

lemma allowAdd{S: Support (More N)}{F G:Obs N}(p:Allowed S F)(q:Allowed S G): Allowed S (F+G):=⟨ Girt.kitE F G (·+·) continuous_add p.bounded q.bounded,fun i j h=> congrArg₂ (·+·) (p.reads i j h) (q.reads i j h),fun i=>(p.modes_use i).add (q.modes_use i)⟩
lemma allowCash{S: Support (More N)}{F:Obs N}(p:Allowed S F)(a:ℂ): Allowed S (a • F):=⟨ Girt.pole_w F (fun x=>a • x) (continuous_const_smul _) p.bounded,fun i j h=> congrArg (a • ·) (p.reads i j h),fun i=>(p.modes_use i).scale _⟩
variable {S: Support (More N)}{X: Orbit N→ Phys N}{F G: Obs N}
lemma react(p:Envelope X)(a:Envelope F)(b:Envelope G): Fixed.functional X (F+G)=Fixed.functional X F+Fixed.functional X G:=by
 unfold Fixed.functional; simp_rw [Pi.add_apply,act_add,beamZ,inner_add_right]; exact integral_add (Law.pay (env_taste X (fun i=>F i.1) (lower F a) p)) (Law.pay (env_taste X (fun i=>G i.1) (lower G b) p))
lemma rost (p: Allowed S F): Allowed (univ : Support (More N)) F:= mode_p p (subset_univ _)
variable {X: Orbit N→ Phys N} (a:Allowed S F) (b:Allowed S G)
abbrev bellM (i:Axis)(F G : Obs N):= Fixed.reflectTest i false F* G
include a b
lemma bellE : Envelope (bellM i F G):=by apply (allowT _ (rost b)).bounded; rw [← Bide.origin i (plain a)]; exact rost (movement a rfl) -- Goal unif?
variable (X₀ : Envelope X)
include X₀
lemma plusY (R:Obs N)(x:Allowed S R): Fixed.functional X (bellM i (F+R) G) = Fixed.functional X (bellM i F G) + Fixed.functional X (bellM i R G):=by
 rw [show bellM i (F+R) G=bellM i F G+ bellM i R G from by unfold bellM; rw [Fixed.reflectTest_add,add_mul], react X₀ (bellE i a b) (bellE i x b)] -- ▸ direction?
lemma plusR (R: Obs N)(x:Allowed S R): Fixed.functional X (bellM i F (G+R))= Fixed.functional X (bellM i F G) +Fixed.functional X (bellM i F R):=by rw [show bellM i F (G+R)=_ from (mul_add ..),react X₀ (bellE i a b) (bellE i a x)]
lemma mercy (u:∀ F: Obs N,Allowed S F→ 0 ≤ Fixed.functional X (Fixed.reflectTest i false F*F)): ‖Fixed.functional X (Fixed.reflectTest i false F*G)‖^2 ≤ ‖Fixed.functional X (Fixed.reflectTest i false F*F)‖ * ‖Fixed.functional X (Fixed.reflectTest i false G*G)‖:=by
 apply GramValve _ _ _ (Fixed.functional X (bellM i G F)); intro c d; let y:= c • F; let z:= d • G; have h1: Allowed S y:=allowCash a c; have h2: Allowed S z:=allowCash b d; have hx:=u (y+z) (allowAdd h1 h2); change 0 ≤ Fixed.functional X (bellM i (y+z) (y+z)) at hx
 have hz (V W:Obs N)(c d:ℂ): Fixed.functional X (bellM i (c • V) (d • W))=star c*d *Fixed.functional X (Fixed.reflectTest i false V*W):=by
    unfold bellM; rw [Fixed.reflectTest_smul]; let t:= Fixed.reflectTest i false V; change Fixed.functional X ((star c • t)*(d • W))=_; rw [show (star c • t)*(d • W)=(star c*d) • (t*W) from ?_, Fixed.functional_cash]; ext1 y; simp only [Pi.smul_apply,Pi.mul_apply]; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
 rw [plusY i h1 (allowAdd h1 h2) X₀ z h2,plusR i h1 h1 X₀ z h2,plusR i h2 h1 X₀ z h2,hz,hz,hz,hz,← add_assoc] at hx; exact hx
end YM.CF.BProof.Chess
