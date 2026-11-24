import YM.CF.BProof.Wick.Stint
/-! combining orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory Stint
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c r:ℝ}(h:0≤L)(e:0<c)(q:r<1)
include h e q
-- use ONE bought price for simplicity
lemma roll_cost (a:Pay): ∃ p:Pay,∀ {I D G Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b: Stage Y I D G}{t: Tag b}{A T P Q: Raw D I}{V Z V' Z':D→Line I}, Capacity b L→ Earn a t t A→ Earn a t t T→ Earn a t t P→Earn a t t Q→ Earn a (straw t) (straw t.reverseV) (divY V)→Earn a (straw t) (straw t.reverseV) (divY Z)→ Earn a (straw t) (straw t.reverseV) (divY V')→ Earn a (straw t) (straw t.reverseV) (divY Z')→(∀ i,Ride (A i) (T i) (V i) (Z i) (V' i) (Z' i) (P i) (Q i) c r)→ Earn p t t (rollF A T P Q V Z V' Z')∧ ∀ i, SumK (A i) (T i) (V i) (Z i) (V' i) (Z' i) (P i) (Q i) ∧ rolled (A i) (T i) (V i) (Z i) (V' i) (Z' i) (P i) (Q i) = (rollF A T P Q V Z V' Z' i).trace:= by
 obtain ⟨y,X⟩:=eatConst h; obtain ⟨l,E⟩:= sweepPrice h a a y; obtain ⟨s,t,u,v,w,W⟩:=Stint.sphere _ _ h e l a a y; obtain ⟨b,c,U⟩:=exPay h l a a q; obtain ⟨d',d,V⟩:=exPay h v a a q; obtain ⟨x,x',Y'⟩:= exPay h v a (paySh l a a y s t u) q; refine ⟨(((b.add c).add x).add d),?_⟩; intro I D G Y _ _ _ _ _ _ g M A T P Q V₁ V₂ F₁ F₂ H tA tT tP tQ tV₁ tV₂ tF₁ tF₂ R
 let S:= straw M; let k:= Ella_pay H; let X':=X (s:=M) H; let η(x:D×Time):=x.2.val; let K(x:D×Time):=rug (A x.1) (T x.1) x.2.val; have hK:Earn l S S K:= E k (jewel tA) (jewel tT) X' (fun i=> (R i.1).breeze)
 let W'(x:D):=crownP (A x) (T x); let u0:Time:=⟨0,walk0⟩; let u1:Time:=⟨1,walk1⟩; have ht:Earn l M M W':= est hK u1; let F:= shuck h k W (jewel ht) (jewel tP) (jewel tQ) (τ:=η) X' (fun x=>upt x.2.property) (fun i=>(R i.1).bridge); let M'(x:D):=floorH (W' x) (P x) (Q x) 0; have hM:Earn v M M M':=est F.2 u0
 have hp:Earn b S S (divY (partI A T V₁)):= (U k hK (jewel (est tV₁ u0)) (fun i=>(R i.1).rails i.2.val i.2.property)).1 _ (jewel tT)
 have hs:Earn c S S (divY (partJ A T V₁ F₁)):= (U k (jewel ht) tV₁ (fun i=>(R i.1).fires i.2.val i.2.property)).2 _ tF₁
 have hg:Earn x S S (divY (partK A T P Q V₁)):= (Y' k F.2 (jewel (est tV₁ u1)) (fun i=>(R i.1).sails i.2.val i.2.property)).1 _ F.1
 have hz:Earn d S S (divY (partM A T P Q V₂ F₂)):= (V k (jewel hM) tV₂ (fun i=>(R i.1).pores i.2.val i.2.property)).2 _ tF₂
 exact ⟨((((averaged hp).plus (averaged hs)).minus (averaged hg)).plus (averaged hz)), fun i=> can A T P Q V₁ V₂ F₁ F₂ i hp.cont hs.cont hg.cont hz.cont⟩
end YM.CF.BProof.Wick
