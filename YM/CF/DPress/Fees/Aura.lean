import YM.CF.DPress.Fees.Pillar
/- Summary.Aura.fees.
 Uniform primitive integrand.Phases.Stax.C. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Rails Wray Finance Receipt Rosy
open Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{a L h θ b:ℝ} {S:Aura n}
variable {U:Type}[AddCommGroup U][Module ℂ U]
namespace Moral
-- billΣ for any system per S. witness. can reserve all vector.Price at fixed c_φ.*.
abbrev κW(R:BudgetPoint)(t:ℝ)(o:Seat n)(S:Aura n) := if o∈ S.val then currency R.B t S.val else 0
lemma κW_p(P:BudgetPoint)(t:ℝ)(o:Seat n) (S:Aura n)(_:S∈univ):0≤ κW P t o S:=ite_nonneg (ccur ..) le_rfl
lemma abrasion (a:ℝ)(f:Aura n→ℝ)(e:Seat n): tallB f P.B a e=∑ i,κW P a e i*f i:=by simp_rw [κW,ite_mul,zero_mul]; rw [←sum_filter]; apply sum_congr rfl; intro i p; rw [mul_comm] -- tune
variable (P) (θ) (F:Aura n→ Credit U) (A:Aura n→ Dial U) (Q:∀ i,Finance (F i) (A i))
def Wage: Credit (Aura n→ U):= fun x v=> ∃ f:Aura n→ℝ,(∀ i,F i (x i) (f i)) ∧ ∀ i:Seat n,tallB f P.B θ i≤v
abbrev Lifts := CurrencyP A (κW P θ)
variable {f:Aura n→ U}
include Q
lemma pre_funds : Transactions F (κW P θ) f a ↔ Wage P θ F f a:=by
 constructor; rintro ⟨u,w,v,h⟩; exact ⟨w,fun i=> v i (mem_univ _),fun i=>by rw [abrasion θ w i (P:=P)]; exact h i⟩; rintro ⟨w,g,p⟩; simp_rw [abrasion θ w _ (P:=P)] at p; exact ⟨le_trans (sum_nonneg fun i t=> mul_nonneg (κW_p _ _ _ i t) ((Q i).priceQ _ (g _))) (p 0),w,fun i _=>g i,p⟩ -- tune unaction.
lemma earnings : Finance (Wage P θ F) (Lifts P θ A):= Finance.anti _ _ _ (Income F A (κW P θ) (κW_p P θ) Q) (fun _ _=> pre_funds P θ F A Q)
variable (e:0≤θ)
include e
lemma affordability (k: Wage P θ F f a)(i:Aura n): F i (f i) a:= by
 obtain ⟨o,u⟩:= i.property; exact spending F A (κW P θ) (κW_p P θ) Q (pre_funds P θ F A Q|>.2 k) i ⟨o,by rw [κW,if_pos u]; exact steady e i.val P.B⟩
omit e
lemma credit0 (Z:ℂ→ Aura n→ U)(w:∀ z∈ank L, Wage P θ F (Z z) a)(v:timely (L:=L) A Z)(q:1<L) : Wage P θ F (Z 1-Z 0) (a/(L-1)):= (pre_funds P θ F A Q).1 (results F A _ (κW_p P θ (n:=n)) Q Z (fun i p=> (pre_funds P θ F A Q).2 (w i p)) v q)
omit Q
variable (h)
abbrev L0 (x:Aura n) : Credit (Copy n) := fun v => Medal P x.val ∅ v h
lemma halle (v:1≤h)(X:Aura n): Finance (L0 P h X) (shield P h X.val ∅):=capM P h X.val ∅ v
abbrev PactF(P:BudgetPoint)(t:ℝ)(h:ℝ): Credit (Pax n) := Wage P t (L0 P h)
abbrev house0(P:BudgetPoint)(t:ℝ)(h:ℝ): Dial (Pax n):= Lifts P t (fun i=>shield P h i.val ∅)
variable (v:1 ≤ h)
include v
lemma fortune : Finance (PactF (n:=n) P θ h) (house0 P θ h):= earnings _ _ _ _ (halle P h v) -- tune n param
include e
lemma kfund (f:Pax n)(u: PactF P θ h f a)(i:Aura n): Medal P i.val ∅ (f i) h a:= affordability _ _ _ _ (halle P h v) e u i
lemma wage_c (f:ℂ → Pax n)(g:∀ z∈ank L, PactF P θ h (f z) a)(Q:∀ i:Aura n,Listen L (fun z=> f z i) (γGood P i.val))(k:1<L): PactF P θ h (f 1-f 0) (a/(L-1)):=credit0 _ _ _ _ (halle P h v) f g (fun i=>armorB P h i.val ∅ v _ (by simpa only [sdiff_empty] using Q i) (fun z p=> kfund _ _ _ e v _ (g z p) i) k) k -- tune param proof
end Moral
end YM.CF.DPress.Fees
