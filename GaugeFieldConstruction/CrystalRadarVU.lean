/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.ΜiraJournalVU
import GaugeFieldConstruction.CrystalStationVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
lemma expenseSelectAllRC (R:Paper)(e : Axis→Bool)(h:∀ f:Panels,∀ i:Axis,R (moves (Signed.mirror i) f)= signValue (e i)*R f) (f:Grouping)(w:Axis→ℝ)(n): sent R (mailsAllRC w f n)= sent R (mailsAllRC w (fun i=> modeSelVU (e i) (f i)) n):=by
 refine (mapAllModeVU _ _ e ?_).trans ?_
 · intro f i; rw [sent_at,polarVU]; exact h ..
 congr 1; ext1 i; exact modeWidthVU (fuelAllRC (w i) n) (f i) (e i)
variable {G : Gauge} {L : Register G} {S : Table L}
lemma portraitFixedAllRC (V : ∀ i,Chamber S i) (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (J : Stress S) (C : Conserved P H.spin J) (Y : RawTensor H.spin J) {D : ℕ} {R : Series} (hR : Portrait J D R)
    (a b c d i: Axis) (f : Grouping) (hf : Far (f i)) (hF : ∀ j, Ends (f j))
    (w : Axis → ℝ) (he : w i=0) (hw : ∀ i,w i ≤ 0) (δ : ℝ) (hδ : 0<δ) :
    BudgetAllRC δ (fun n => sent (R a b c d) (mailsAllRC w f n)) := by
 let e:= axes a b c d
 let g: Grouping:=fun i=> modeSelVU (e i) (f i)
 refine (fixedAllRC V H P hp ho J C Y hR a b c d i g (modeFarVU hf _) (fun j=>modeEndsVU (hF j) _) (fun j _=>modeRefVU _ _) w he hw δ hδ).same (Eventually.of_forall fun n=> Eq.symm (expenseSelectAllRC (R a b c d) e ?_ f w n))
 intro f i
 let s:= Signed.mirror i
 have ht:=hR.Hs s a b c d f; change _ * R a b c d (moves s f)=R a b c d f at ht
 have hl: colorSign s a*colorSign s b*(colorSign s c*colorSign s d) = signValue (e i) := by
    rw [← spar_at,← spar_at]; cases hh:spar a b i <;> cases hu:spar c d i <;> simp [signValue,e,axes,hh,hu]
 rw [hl] at ht; rw [←ht,←mul_assoc,sign_sq,one_mul]
#print axioms portraitFixedAllRC
end YM.NSF.Outer
end
