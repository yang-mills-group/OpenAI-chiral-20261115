import YM.CF.BPress.Vesper.Forges
import YM.CF.BPress.Pf.Brooks
/-! eq:B-Oexpect prices Part covariance. Read arguments on any voucher domain supporting Group/Stoke; true income applied after. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Palmer Fock Pastry Pine Pf Vesper Spin Spin.Pledge Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement -- check
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {I D Y :Type}[LinearOrder I][Fintype I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]
variable {P : Stage Y I D Empty} {X Y':D→Finset I}{A T:Raw D I}{C C':D→ℝ→Op I}{h d ε r:ℝ}
variable {R B F H:Pledge} (x:SpinIndex)
def ζP (C M:Pledge):Pledge:= (((C.scales ‖Lily.fract‖).bond (unary.plus M)).bond (unary.scales ‖Lily.fract‖)).bond M
lemma voteC(K T:Pledge){X Y':Raw D I}(p:K.Costs P X)(t:T.Costs P Y'): let Q:=ζP K T; Q.Costs P (fun i=>dad (X i) (Y' i) x)∧ Q.Costs P (fun i=> mom (Y' i) x):=by
 intro Q; let W:=K.scales ‖Lily.fract‖; let N:=unary.plus T; cases x with|none=>exact ⟨Costs.up (Costs.smul (Costs.neg (Costs.transpose p)) _) (((bond_lel W N).trans (bond_lel ..)).trans (bond_lel ..)),Costs.up (Costs.smul Costs.one _) ((bond_ler (W.bond N) _).trans (bond_lel ..))⟩| some x=>cases x; exact ⟨Costs.free, Costs.up (Costs.stars t) (bond_ler ..)⟩; exact ⟨Costs.up (Costs.sub Costs.one t) (((bond_ler W N).trans (bond_lel ..)).trans (bond_lel ..)), Costs.free⟩ -- tune
abbrev δLoan(X Y':D→ Finset I)(A T:Raw D I)(C:D→ℝ→ Op I) (a b:SpinIndex):Raw D I:= fun i=> fees (cutM (X i)) (cutM (Y' i)) (shun I (X i) (Y' i)) (mood (A i) (T i)) (C i 2) (A i) a b

theorem penny (h:0≤d)(u:0<ε)(p:0≤r)(q:r<1)(R B F H:Pledge):∃ S:Pledge,∀ {I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{X Y':D→Finset I}{A M:Raw D I}{C C': D→ℝ→Op I}, RealBook.Stoke X Y' A M C C' b R B F H ε r d→∀ a z:SpinIndex,S.Costs b (δLoan X Y' A M C a z):=by
 obtain ⟨W,w⟩:=buy_tilt R B h; obtain ⟨K,k⟩:=contexts_budget F F (unary.plus (F.plus F)) W H (ζP H R) u h r p q; refine ⟨K,?_⟩; intro I D Y _ _ _ _ _ _ b X Y' A M C C' S a z
 have ht:= Currency.subview (f:=C) 1 2 (by norm_num [PartH]) S.walk2; have he:= voteC a H R ht S.am; have hx:= voteC z H R ht S.am
 have hv:= w (v:=fun _=>1) S.cap (Spin.Hole.tuned_one _ (1:ℝ) (by simp)) S.am S.wm (fun x=>(S.peak x).proj) fun i=>(S.peak i).she -- tune
 exact k S.cap S.pA S.pB (Costs.sub Costs.one (Costs.plus S.pA S.pB)) hv ht (fun i=>(S.peak i).drum) he.1 he.2 hx.1 hx.2 -- tune shun

end YM.CF.BPress.Spark
