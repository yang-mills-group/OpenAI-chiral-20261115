import YM.CF.Cour.Route
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {B L:Side}{n k:ℕ}{e t x u C A:ℝ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable{m X:Side}{T:Roam m X B}{F: Forest T.ratio}{G: Ratio (CSide m B) (CSide X B)}
variable{α Y:Type}[Fintype α][DecidableEq Y][Fintype Y]
lemma rootWide(hn:1 ≤ n)(L:Side):∃ K:ℝ,1 ≤ K ∧∀ e:ℝ,∀ b:0<e,∃ r:ℝ,0<r∧∀ {m M B:Side}{T:Roam m M B}(F:Forest T.ratio)(G:Ratio (CSide m B) (CSide M B)), G.count=L→∀ a:ℝ, K≤a → Fleck G b F r a n:=by
 obtain ⟨C,h,H⟩:=gleanA n; refine ⟨C,h,fun e b=>?_⟩; obtain ⟨v,hv,p,P⟩:= windA L b hn h; refine ⟨v,hv,fun {m M B T} F G he a g=>?_⟩
 have hV(y)(hy:‖y‖<v):= P G F he (fun x hx=>H F x (hx.trans p)) y hy; have hz(y)(hy:y∈ball 0 v): (frameT G b F y).val=hats F y:= congrArg Subtype.val (Pec.pear_even G b (show _∈ Broc.Rent0 G e from hV y (mem_ball_zero_iff.mp hy)))
 refine ⟨hV,?_⟩; intro z ht; let f:=hV z (mem_ball_zero_iff.mp ht); obtain ⟨hp,hl⟩:= H F z ((mem_ball_zero_iff.mp ht).le.trans p); constructor
 · intro i; apply ((hp i).mono g).germ; filter_upwards [isOpen_ball.mem_nhds ht] with y hy; change _=fund ((frameT G b F y).val.1 i); rw [hz _ hy]; rfl
 intro i; apply ((hl i).mono g).germ; filter_upwards [isOpen_ball.mem_nhds ht] with y hy; change _=fund ((frameT G b F y).val.2 i); rw [hz _ hy]; rfl
end YM.CF.Cour
