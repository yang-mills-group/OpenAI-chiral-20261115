import YM.CF.Vow.Move
import YM.CF.Mica.Near

/-! Lit expenses of the activated Reg entries. No D qualifications
are needed for their assignment budgets (unlike other uses of lit).
Equal to the elected masked value on every litres domain.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Zephyr
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray

open Vow Ione
variable {n:Side}
local notation "Pos"=>Support (More n)

abbrev consult (X:Pos) (F:InkD n)(D:Pos): InkD n:=
 if Disjoint X D then F else 0

structure LitReg (P: BudgetPoint)(X:Pos)(F:InkD n)(h v:ℝ): Prop where
 shirt (D:Pos): ThemeR X (oV (consult X F D))
 charges:∃ c:Raid (Dwell n), 0≤c ∧ joinV (stake h) c ≤ v ∧ ∀ (A D :Pos) (Y:Pos) (U:Orbit n),
           X⊆A→pingS P.threshold (A\D) U.1→ WorthB P U Y (oV (consult X F D)) c

lemma nullshirt (X:Pos): ThemeR X (oV (0:InkD n)) := by
 refine ⟨fun _ _ _ _=>rfl,fun _=> Flour.trivial, ?_,fun _ _=>?_⟩
 · change Measurable (fun _=>0)
   exact measurable_const
 simp only [oV,Pi.zero_apply,map_zero]

variable {P:BudgetPoint}{h v:ℝ}

lemma nullworth {c:Raid (Dwell n)}(q:0≤c)(U:Orbit n)(Y:Pos): WorthB P U Y (oV (0:InkD n)) c:= by
 let w: WorthB P U Y (oV (0:InkD n)) 0 := Woody.empty 0
 exact ⟨w.own,fun i=> ⟨(w.haveP i).1,(w.haveP i).2.trans (q _)⟩⟩

theorem consult_bill {i:Scree.Hub n}{F:InkD n} (p:PressB P i F h v)(g:0≤h):
    LitReg P i.val.2 F h (chi_f P.order * v):= by
 obtain ⟨t,c,r,e,y⟩:= rimR p g
 refine ⟨fun D=>?_, c,r,y,fun A D Y U b d=>?_⟩
 · unfold consult
   split
   · exact t
   · exact nullshirt _
 unfold consult
 split
 next z =>
   apply e U _ (empty_subset _)
   rw [sdiff_empty]
   exact grow_b (subset_sdiff.mpr ⟨b,z⟩) d
 exact nullworth r U Y

/-- Exact consultation, incl for ties outside final support. -/
lemma plugged {F:InkD n}{X A D:Pos}(p:X⊆A): Set.EqOn (consult X F D) (numbE P.threshold X F)
   (Rue.litres P.threshold A D):= by
 intro V t
 unfold numbE consult
 by_cases h:Disjoint X D
 · rw [if_pos h,Set.indicator_of_mem]
   exact grow_b (subset_sdiff.mpr ⟨p,h⟩) t.1
 rw [if_neg h, Pi.zero_apply, Set.indicator_of_notMem]
 exact fun y=>h (Disjoint.mono_right t.2 (ping_le y))

/-- Even outside consulted domains, actual masks respect
the positive-degree projection. -/
lemma positive_read (P:BudgetPoint) (X:RegBudget n) (i:Scree.Hub n) (V:Pane n):
    numbE P.threshold i.val.2 (head_L X i) V = blind_E (numbE P.threshold i.val.2 (X i) V) :=by
 unfold numbE; simp only [Set.indicator]
 split
 · rfl
 apply pimp_Q; intro j; rw [shelter_Q]; split <;> rfl

#print axioms plugged
#print axioms consult_bill
end YM.CF.Zephyr
