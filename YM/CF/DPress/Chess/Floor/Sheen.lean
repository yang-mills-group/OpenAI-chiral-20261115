import YM.CF.DPress.Chess.Floor.Cross
import YM.CF.DPress.Chess.Floor.Shed
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Slit
open BPress
variable {A B:Fixed.Test n}{S:Support (More n)}{F:Orbit n→Phys n}
local notation "Ω"=> Fixed.functional F
lemma billσ (z:ℂ)(p:Boss n S A): Boss n S (z • A):=by
 obtain ⟨u,p⟩:=p; exact ⟨_, IsMark.factor (D:=‖z‖) p (c:=fun x=>z) (fun _ _ _=>rfl) measurable_const (fun _=>le_rfl) ⟩
lemma billA (p:Boss n S A)(h:Boss n S B):Boss n S (A+B):=by
 obtain ⟨i,p⟩:=p; obtain ⟨j,h⟩:=h; exact ⟨i+j, ⟨fun x y u=>congrArg₂ (·+·) (p.reads _ _ u) (h.reads _ _ u),fun t=>(p.even t).add (h.even t),p.borel.add h.borel,fun i=>(norm_add_le ..).trans (add_le_add (p.cost i) (h.cost i))⟩⟩
lemma weighP (z:ℂ) (A:Fixed.Test n) (F:Orbit n→Phys n): Fixed.functional F (z • A)= z*Fixed.functional F A:=by unfold Fixed.functional; simp_rw [Pi.smul_apply,act_smul,beamZ,inner_smul_right]; exact integral_const_mul ..
lemma currency (p:Envelope F) (h:Envelope A)(t:Envelope B): Fixed.functional F (A+B)= Ω A+Ω B:=by
 let f(A:Fixed.Test n)(x:Orbit n):= WeightR (A x.1) (F x); rw [Fixed.functional,show (fun x:Orbit n=> _)=(fun x=> f A x+f B x) from ?_,integral_add]; rfl; exact Env.integrableX (Porch.rent_C (Env.along h measurable_fst) p) (city _); exact Env.integrableX (Porch.rent_C (Env.along t measurable_fst) p) (city _); funext i; simp only [Pi.add_apply,act_add,beamZ,inner_add_right]; rfl
lemma cosh (z:ℂ) (A B:Fixed.Test n) : (peer W (A+z • B))*(A+z • B)= peer W A*A+ z • (peer W A*B)+(star z) • (peer W B*A)+(star z*z) • (peer W B*B):=by funext i; unfold peer; simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Wall.θ,theta_add,theta_smul,add_mul,mul_add,←Algebra.smul_mul_assoc]; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rw [mul_comm (star z)]; abel
lemma Arth (c:ℂ)(p:Envelope F)(v:∀ X:Fixed.Test n,Boss n S X→0 ≤ Fixed.functional F (peer W X*X))(a:Boss n S A)(b:Boss n S B) : ‖c* ((Ω) (peer W A * B))‖^2 ≤ ‖c*((Ω) (peer W A*A))‖*‖c*((Ω) (peer W B*B))‖:=by
 let g(V W₁:Fixed.Test n):= (Ω) (peer W V * W₁); have hv(z:ℂ):0 ≤ g A A+z*g A B+star z*g B A+(star z*z)*g B B:=by
    let V:=Fixed.functional F; let w{X Y:Fixed.Test n}(a:Boss n S X)(b:Boss n S Y):Envelope (peer W X*Y):= Law.prodP (peer_env W (Boss.window S a)) (Boss.window S b); let y{X: Fixed.Test n}(i:ℂ)(p:Envelope X): Envelope (i • X):=Girt.pole_w X _ (continuous_const_smul i) p; let m := v _ (billA a (billσ z b)); have ht{A B:Fixed.Test n}(a:Envelope A)(h: Envelope B):Envelope (A+B):= Law.addC a h; rw [cosh,currency p (ht (ht (w a a) (y z (w a b))) (y (star z) (w b a))) (y _ (w b b)),currency p (ht (w a a) (y z (w a b))) (y (star z) (w b a)),currency p (w a a) (y z (w a b)), weighP,weighP,weighP] at m; exact m
 have ht:= own (v _ a) (v _ b) hv; rw [norm_mul, mul_pow,norm_mul,norm_mul]; refine (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq ?_; ring
end Slit
end YM.CF.DPress.Chess
