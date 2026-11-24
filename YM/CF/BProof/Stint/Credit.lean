import YM.CF.BProof.Align.House
import YM.CF.BProof.Stint.Functional
/-! B-matrix price for S assembles once margin holes purchased. Works also for
stretch parameter varying with a PLN currency before parameter integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (C c:ℝ)(hp:0≤C)(hz:0<c)
structure Club (C c:ℝ)(a p q r s t u v w:Pay) : Prop where
 applies {I Y Z G:Type} [Fintype Y] [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq Y] [TopologicalSpace Z] {b:Branch.Stage Y I Z G} {k:Branch.Tag b} (H:Capacity b C) {A P Q:Raw Z I}{τ:Z→ℝ}(xP:Earn p k k P)(xQ:Earn q k k Q)(xA:Earn a k k A)(xT:Earn r k k (fun x=> τ x •1))(xU:∀ x,‖τ x‖≤1)(xB:∀ x,Board (A x) (P x) (Q x) c):
    let S:Raw Z I := fun x=>house (A x) (P x) (Q x) (τ x)
    Earn s k k S∧ Earn t k k (fun x=> wedgeP (A x) (P x))∧ Earn u k k (fun x=>(entered (A x) (S x))⁻¹) ∧ Earn v k k (fun x=> floorH (A x) (P x) (Q x) (τ x)) ∧ Earn w k k (fun x=>(entered (P x) (A x * P x))⁻¹)
variable {I Y G D:Type*}[Fintype I][DecidableEq I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{k:Tag b}{F:Raw D I}{τ:D→ℝ}
lemma Earn.pil {p q:Pay}(W:Earn p k k (fun x=>τ x • 1))(h:Earn q k k F) : Earn (p.mul q) k k (fun x=>τ x • F x):=by simpa only [Algebra.smul_mul_assoc,one_mul] using W.times h
section
include hp hz
theorem sphere (a p q r: Pay): ∃ s t u v w:Pay, Club C c a p q r s t u v w:=by
 let y:=a.mul p; obtain ⟨w,W⟩:= inverseCost hz hp ((y.mul y).add (Pay.simple.add p)); let t:=y.mul (w.mul y); let L:=Pay.simple.add (p.add q); let Z:=r.mul L; let k:=r.mul q; let H:=(p.add Z).add (r.mul k); let s:= (H.mul t).add ((L.add k).mul (a.add t)); obtain ⟨u,U⟩:=inverseCost (paid_pos hz) hp ((s.mul s).add (Pay.simple.add a)); refine ⟨s,t,u,s.mul (u.mul s),w,⟨?_⟩⟩; intro I Y D G _ _ _ _ _ _ b k h A P Q τ xP xQ xA xT xU xB S
 let F₁(x):= A x * P x; let V:= fun x => entered (P x) (F₁ x); let T(x):=wedgeP (A x) (P x); let K(x):=space (P x) (Q x); let Θ:=Earn.one k
 have hc:Earn y k k F₁:= xA.times xP; have hk:Earn L k k K:= Θ.minus (xP.plus xQ)
 have hw : Earn w k k (fun x=>(V x)⁻¹):= W h ((hc.adj.times hc).plus (Θ.minus xP)) (fun x=> (xB x).doorB)
 have hT: Earn t k k T := hc.times (hw.times hc.adj); have hQ:= xT.pil (xT.pil xQ); simp_rw [smul_smul,←pow_two (τ _)] at hQ
 have hs: Earn s k k S := (((xP.plus (xT.pil hk)).plus hQ).times hT).plus ((hk.plus (xT.pil xQ)).times (xA.minus hT))
 have ht:= U h ((hs.adj.times hs).plus (Θ.minus xA)) (fun x=> (xB x).house_gear (τ x) (xU x)); exact ⟨hs,hT,ht,hs.times (ht.times hs.adj),hw⟩
end
end YM.CF.BProof.Stint
