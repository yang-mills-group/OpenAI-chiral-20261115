import YM.CF.BProof.Weights.Agenda
import YM.CF.BProof.Charge.Till

/- NPL pledge, signs preserved. `F₂` three terms; severe ledger external. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Weights
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot Mapping House Pricing Prox Moment Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
local notation "G"=> SU.group
variable {s c': Side}(Y:Yard s)(S:Hall s)(g:Ratio c' s)
variable (M:ℝ→ℕ)(T:PathData G)(θ β:ℝ){R y w v κ:ℝ}{c:Clip}{K:Chart G}{P: Pub G}(p:Model K P c Y.short M R y κ)(u:Room Y (M y))(t:T.Bounds c w R v)(h:θ∈Set.Icc (1/2) 2)(q:BudgetPoint)(k:ValidR c q (M y))(C:ℝ){K':ℕ}{j α:ℝ}(vβ:y≤2*β)(e:β≤2*y)(hq:q.threshold=thresh y)(A:Agenda Y S g K P K' C M c w R κ y j α)
variable (x:Pawn Y)
def lightG := (∑ b,tabs Y S M T θ β p q x b)+(∑ i, issueW Y M T θ p u t h x i)+swage (p:=p) Y S M T θ (fogBill (y:=y) M T β t q k) x
abbrev highG := ∑ b∈x.sev,burn Y S M T θ β p u t h q x b
abbrev rent (y:ℝ)(M:ℝ→ℕ)(R w v:ℝ) := Charge.rate (thresh y) (2*y) w R v (M y)
def wallet (y:ℝ)(W:ℕ)(P:Pub G)(M:ℝ→ℕ)(c:Clip)(R w v C:ℝ)(d:ℕ)(j α:ℝ):= tabPay W P c M R C d y α+WPay P c d W R M y j α+κ_bound d W j α (Weights.rent y M R w v)
lemma sum_ex : Release.cut P Y T θ y p.X q β x.sev x.gauss (Pawn.put S x y T θ p.X)-Charge.left Y (Pawn.put S x y T θ p.X) (fogBill (y:=y) M T β t q k) = lightG Y S M T θ β p u t h q k x+ highG Y S M T θ β p u t h q x:=by unfold lightG highG; rw [cut_price (u:=u) (t:=t) (h:=h)]; unfold swage; ring -- tune
abbrev Layer := (Y.Col⊕ Finset Y.Col) ⊕ Support s
include vβ e A hq t
lemma furnish : Nonempty (Ledger Y S g M T θ p (Layer Y) (lightG Y S M T θ β p u t h q k) α (wallet y g.count.val P M c R w v C Y.short j α)) := by
 let Q:= fogBill (s:=s) (y:=y) M T β t q k; have hg:0≤R:= budget_nonneg t.three; have hp:0≤v:= budget_nonneg t.two
 have hu:0≤β:=by have :=A.stamp.early; linarith; -- break
 have H: Q.fine (3*j) (Weights.rent y M R w v):= by
    have hx:= Charge.weak_p c q T (M y) β t k s; apply Moment.Toll.weaken _ _ hx A.weak; rw [hq]; apply Charge.rate_le w R v t.width _ (coin_pos ..).le _ hg hp; rw [abs_of_nonneg hu,abs_of_nonneg (by linarith : 0 ≤ 2*y)]; exact e
 obtain ⟨s⟩:= convey Y S g M T θ β p u t h q C k vβ hq A e; obtain ⟨U⟩:= Weights.issue Y S g M T θ p u t h C A; obtain ⟨Z⟩:= Weights.earn (p:=p) Y S g M T θ u t C A _ H
 exact ⟨(s.add U).add Z⟩
omit vβ e A hq t -- t not incl?
variable {g}
lemma fiscal (L:ℝ→ℕ)(u:PL fun y=>(M y:ℝ))(e:PL fun y=>(L y:ℝ))(c:Clip)(R w v C a:ℝ)(d:ℕ)(h:0<d)(p:Pub G)(j:ℝ→ℝ)(k:PL fun y=>(j y)⁻¹) (t:∀ y,0<j y)(l:∀ y,j y≤1)(H:NPL fun y=> Weights.rent y M R w v) : NPL (fun y=>wallet y (L y) p M c R w v C d (j y) a):=by
 let x(y):= (L y:ℝ); let X:= NPL; let F(y):= ((root_port d 1 (L y):ℕ):ℝ); have hp : PL (fun y=>ply (L y) 1 a):=by unfold House.ply; push_cast; exact ((PL.mul (PL.const _) (e.pow 3)).mul (PL.const _)) -- tune `Table` NPL
 have hx := Mapping.factor_table 4 (up 1) (fun y=>root_port d 1 (L y)) j a ?_ k t l; swap;· unfold root_port; push_cast; exact (PL.const _).mul (e.pow 3)
 have hy:= Mapping.factor_table 4 (expense 0) (fun y=>(L y)^3) j a (by push_cast; exact e.pow 3) k t l
 exact (((hp.muln (tabN M u p c R C d h)).add ((j_tail c d M R h u).2.mulp hy)).add (H.mulp hx)) -- tune
end YM.CF.BProof.Weights
