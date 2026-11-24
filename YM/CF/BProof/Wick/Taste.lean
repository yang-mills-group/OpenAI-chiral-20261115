import YM.CF.BProof.Wick.Mint
import YM.CF.BProof.Stint.Credit
/-! matrix cost for sweep derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory Stint
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I D G Y:Type}[Fintype I][LinearOrder I][Fintype Y][DecidableEq Y][TopologicalSpace D]
variable {L c:ℝ}(h:0≤L)
include h
theorem sweepPrice (a t l:Pay): ∃ p:Pay,∀ {I D G Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{u:Tag b}{A T:Raw D I}{v:D→ℝ}, Capacity b L→Earn a u u A→ Earn t u u T→ Earn l u u (fun i=>v i • 1)→ (∀ i,Gust (A i) (T i)) → Earn p u u (fun i=>rug (A i) (T i) (v i)):=by
 let s:=Pay.simple; let f:= (s.add (l.mul t)).mul a; obtain ⟨k,X⟩:=inverseCost (by norm_num : 0<(1:ℝ)) h ((f.mul f).add (s.add a)); refine ⟨f.mul (k.mul f),?_⟩; intro I D G Y _ _ _ _ _ _ b u A T v t₁ t₂ t₃ t₄ x; let F(i):= slit (A i) (T i) (v i)
 have ht:Earn f u u F:=((Earn.one u).plus (t₄.pil t₃)).times t₂
 exact ht.times ((X t₁ ((ht.adj.times ht).plus ((Earn.one u).minus t₂)) (fun i=> (Eq.le (one_smul ℝ (1:Op I))).trans ((x i).bound _))).times ht.adj)
omit h in
def paySh (a p q r s t u:Pay) := let K:=Pay.simple.add (p.add q); let Z:= r.mul q; let V:=K.add (Z.wage ‖(2:ℝ)‖); ((V.mul t).add (q.mul (a.add t))).mul (u.mul s)
theorem shuck {a p q r s t u v w:Pay} {b:Stage Y I D G}{k:Tag b}[Nonempty I]{A P Q:Raw D I}{τ:D→ℝ}(g:Capacity b L)(X:Club L c a p q r s t u v w)(xA: Earn a k k A)(xP: Earn p k k P)(xQ: Earn q k k Q)(xT: Earn r k k (fun i=>τ i •1))(xU:∀ i,‖τ i‖≤1)(xB:∀ i,Board (A i) (P i) (Q i) c): Earn (paySh a p q r s t u) k k (fun i=> shutter (A i) (P i) (Q i) (τ i)) ∧ Earn v k k (fun i=>floorH (A i) (P i) (Q i) (τ i)):=by
 obtain ⟨hs,hT,hu,hv,H⟩:= X.applies g xP xQ xA xT xU xB; refine ⟨?_,hv⟩
 have ht:Earn _ _ _ _:= (xT.pil xQ).wage (c:=2) le_rfl; have hp(i:D): (2:ℝ) • (τ i • Q i)=(2*τ i) • Q i:= (mul_smul ..).symm; simp_rw [hp] at ht; let Y:=(((Earn.one k).minus (xP.plus xQ)).plus ht).times hT; exact (Y.plus (xQ.times (xA.minus hT))).times (hu.times hs.adj)
end YM.CF.BProof.Wick
