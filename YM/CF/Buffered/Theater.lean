import YM.CF.Buffered.Anaphora
import YM.CF.Buffered.Microloan
/-!
# On the manuscript cone at the legal pivot with comparison partners, apply Bill-E.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 27000
set_option maxHeartbeats 590000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open Mail Mail.Grok Ballad Ballad.Markwalk Wings Py
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{C: Conveyor K}{J:Tiling K}{x k:ℕ}{V:SpanCal K}(W:Printed K C J V){e:ℝ}(p:Venue V e)(Z:Rates p J)(z:ℤ)(G:Rented p J z) (X:LacePoint K C J)
open Bilinear
local notation "P"=> W.narrative.hist
private lemma contractu (S:Histories K) (u:0<e) : ∀ᶠ n in atTop, ∀ m:Side,K.Allowed m n→∀ b:Bool,
 ‖S.cap («m»:=m) n ((Original.primary K).goal b)- atZero K.P (S.warm m n) (S.loom m) ((Original.primary K).goal b)‖ ≤ e ∧
 S.cap n ((Original.primary K).goal (N:=K.c m) b) = (if b then S.cap n ((word K * thetaK K (word K)) m) else S.cap n (word K m))-Melody.compare b:= by
 let A:=|Melody.cuts K.vertex 0|+1; have he:0<A:=by unfold A; positivity
 filter_upwards [cone_ratio S (show 0<e/A by positivity), Corollary.cuts S,S.paid,eventually_gt_atTop 0] with n H p' t hv; intro m r b
 have hx:= H m r _ (Melody.global (Original.primary K) (N:=K.c m) b).env _ (square_cost (Original.primary K) (m:=m) b); rw [div_mul_cancel₀ _ he.ne'] at hx
 let x:= word K * thetaK K (word K); let f:=if b then x else word K
 have hp: TestFamily K false f:=by
    unfold f; split; exact ((allowed K false).forget).mul ((allowed K false).forget).ref
    exact (allowed K false).forget
 have ht:((Original.primary K).goal b (N:=K.c m)) = f m + (-Melody.compare b) • (1:Mark (K.c m)):=by rw [Original.tune, sub_eq_add_neg,neg_smul]; unfold f; split <;> rfl
 obtain ⟨i,v⟩:= Granted.paid (Shots.cap_grant (t m r).1) 0 hv
 refine ⟨hx,?_⟩; rw [show (if b then S.cap n (x m) else S.cap n (word K m))= S.cap n (f m) by unfold f; split<;> rfl, ht,Histories.cap,atZero]; rw [mark_add v (hp.paid.choose_spec.support m).env ((AtSupport.oneM univ).smulM _).env i,mark_smul,markvac,add_div, ← show S.cap n (f m)=_ from rfl]; rw [show _ * _ / _ = - Melody.compare b from ?_]; rw [sub_eq_add_neg]
 · rfl
 exact mul_div_cancel_right₀ _ ((p' m r).2.1 0 (Nat.zero_le _)) -- tune
include Z W G X
-- full on sharp at all periods; both strict; cap assembler at the chosen z not changed with n
lemma billE : BillInput (P) e:=by
 filter_upwards [showtime W p Z z G X, contractu P (half_pos p.p)] with n A Q; intro m h
 have ht(b:Bool) : ‖(if b then (P).cap n ((word K * thetaK K (word K)) m) else (P).cap n (word K m))- Melody.compare b‖ < e:=by
    obtain ⟨q,t⟩:=Q m h b; rw [←t]; exact (norm_le_norm_sub_add _ _).trans_lt ((add_le_add q (A m h b)).trans_lt (by linarith [p.p]))
 exact ⟨ht false, ht true⟩
variable {C':Process K}{E:Family K→ℂ} {b:Bool} (t:Settled W.narrative.hist C' b E)
/-- Buffered corollary, using real heat partners. The payer only needs the *receipts* on histories and the local draws. Bill-E is NOT assumed. -/
theorem word_conclusion (Y:Tol e) : E (word K) ≠ 0 ∧ Eligible K b (Corollary.centered t) ∧ 0 < E (thetaK K (Corollary.centered t)*Corollary.centered t) ∧ 0 < Real.sqrt (E (thetaK K (Corollary.centered t)* Corollary.centered t)).re:= Corollary.output Y t (billE W p Z z G X)
omit Z G X
include t W
/-- Same progression, no Bill-E conditions for pure form Gram conclusion or unit diagonal. -/
theorem gram {I:Type*}[Fintype I] (F:I→ eligible K b) : E 1=1 ∧ Matrix.PosSemidef (Matrix.of fun i j=>E (thetaK K (F i).val * (F j).val)):= Corollary.gram_full _ _ t F -- tune
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.word_conclusion
#print axioms YM.CF.Buffered.Concert.gram
