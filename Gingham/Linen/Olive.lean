import Gingham.Linen.Birds
import Gingham.Linen.Fledgling
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
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
open Ione


open Vow Swell Trees
variable {p:BudgetPoint} {n:Side} {h a q:ℝ}

-- PressB doesn't depend on supportExponent. Raisin swap all fields
lemma pressBack {i:Scree.Hub n} {F:InkD n}
 (u: PressB p.raisin i F h a):PressB p i F h a where
 term:=u.term
 fitted:=u.fitted
 measureV:=u.measureV
 gaugeV:=u.gaugeV
 worth:=by
   obtain ⟨y,v,t,z⟩:= u.worth
   exact ⟨y,v,fun U r i=>⟨v i,(t U r i).paid,(t U r i).token⟩,z⟩


/-- Reg incidence provision, with lit uses as well. G arbitrary: apply to R.F in strictly positive exterior degree. -/
structure Quills (G:RegBudget n)(p:BudgetPoint)(h A:ℝ):Prop where
  -- weight budget + symmetry
  focus: ∃ c: Scree.Hub n→ℝ, (∀ X, LitReg p X (G X) h (c X)) ∧
      ∀ y, Λpay p.B (brighten p) y holdH c ≤ A
  face (s:Sweep n) (U:_) (g: JetS s.s s.charge (detX s.s) U) (X :_) (V:Pane n):
      G (moveHub s X) (flashA s V) =
         paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (G X V)


variable {d:ℝ}{f:ℕ→ℝ}{m:ℕ}{F:RegBudget n}

lemma Quills.mono {g:ℝ}(r: Quills F p h d)(k:d≤g): Quills F p h g:=
 ⟨by obtain ⟨y,v,w⟩:=r.focus; exact ⟨y,v,fun i=>(w i).trans k⟩,r.face⟩

def nesting (f:ℕ→ℝ) (b:ℕ) := (1+chi_f 6)*(bird f b)
lemma poly_nesting (u:PolyBill f): PolyBill (nesting f) :=
 (PolyBill.const (add_nonneg zero_le_one (spicy_f 6))).mul (poly_bird u)

/-- Both expenditure (bill_shop) and accuracy (dleaf) in the same lit incidence budget. -/
lemma Glazes.branches (r:p.order=6) (hi:0≤h) (u: PolyBill f)
    (size:max 40 m ≤p.B)
    (deficit: Real.exp (-1/4*(p.B:ℝ))≤q)
    (low:IncX Utrue F p h d)
    (zl:d≤2*q)
    (high: Glazes F p h m (f p.B)):
    Quills (frosting F) p h (nesting f p.B * q):=by
 obtain ⟨J,t,j⟩:=high
 obtain ⟨v,hv,vm⟩:=low.weight
 obtain ⟨w,hw,wm⟩:= t.weight
 have mins:∀ i, PressB p i (frosting F i) h (mixB p v w i):=by
    intro i; unfold mixB; split
    · exact frost (hv i)
    rename_i g
    rw [←j i (lt_of_le_of_lt ((le_max_right ..).trans size) (lt_of_not_ge g))]
    exact frost (pressBack (hw i))


 refine ⟨⟨fun i=>(1+chi_f p.order)*mixB p v w i,fun i=> light (mins i) hi,fun y=>?_⟩, frost_sweeps low⟩
 let e:= 1+chi_f p.order
 have vm':∀ z, χbank p p.supportExponent z anchorH holdH v≤2*q:=by
   intro z; apply le_trans _ ((vm z).trans zl)
   unfold χbank; rw [sum_filter]; simp_rw [@eq_comm _ _ z]
   rfl
 have wm':∀ z, χbank p p.raisin.supportExponent z anchorH holdH w≤ f p.B:=by
   intro z; apply le_trans _ (wm z)
   unfold χbank; rw [sum_filter]; simp_rw [@eq_comm _ _ z]
   rfl
 refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left
     (ruffle ((le_max_left ..).trans size) _ (u.positive _) deficit
        (fun i=>pressFloor (hv i) hi) (fun i=>pressFloor (hw i) hi) vm' wm' y)
     (show 0≤e from add_nonneg zero_le_one (spicy_f _))) (by rw [nesting, ←r]; exact le_of_eq (mul_assoc ..).symm))
 apply le_of_eq
 unfold Λpay
 rw [mul_sum]; exact sum_congr rfl fun i _=>mul_left_comm _ e _

