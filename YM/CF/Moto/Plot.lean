import YM.CF.Hype.Migrate
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Bake Vow Larch
variable {F G: Pax n}{K:Cusp n}{f g: Copy n}
variable (U: Orbit n)
variable {ι:Type*}[DecidableEq ι](W:Finset ι)(X Y Z:ι→Aura n)(F:ι→ Copy n)(G:ι→ InkD n)(A:ι→ℝ)
-- sum charges with localized movement.M. countable finite here.lag. Anchor orientation.Lo.Bold. incidence contamination $.Zκ.Translent.
-- WHEN SOURCE BASE singleton Atlas shift to common.T1. Plan. no target invoice. stroke collects Flags. ROOT.Weight payable.Y.P.M. 
variable (H:Aura n)(hU:∀ i∈W,(X i).val⊆ H.val)(hV:∀ i∈W,Medal P (X i).val ∅ (F i) h (A i))(hp:0≤ h)(S:ℝ)(hy:(∑ i∈W,A i)≤ S)
def ρ_s : Cusp n:= soot_T W X (fun _=> H) (fun _=> H) F
local notation "K"=> ρ_s W X F H
local notation "Do"=> (Pi.single H S:Aura n→ℝ)
include hU hp hV hy
lemma lampP : Anuk K Do P h:=by
 have hf(i)(p:i∈W):0≤ A i:= (hV _ p).wage hp
 have he:0≤ S:= (sum_nonneg hf).trans hy
 refine ⟨?_,fun j u v t=>?_⟩
 · intro i; by_cases p:i=H; · rw [p,Pi.single_eq_same]; exact he
   rw [Pi.single_eq_of_ne p]; exact le_rfl
 unfold ρ_s soot_T stroke
 have h1(i)(p:i∈W)(D:Support (More n))(v:D.Nonempty)(t:D⊆ H.val):Medal P H.val D (flick (X i) (F i) D- flick H (F i) D) h (A i):=by
    rw [show flick H (F i) D=0 from if_neg (fun b=>v.ne_empty (disjoint_self.mp (Finset.disjoint_of_subset_right t b))),sub_zero] -- simpler
    exact flick_M _ _ (hU _ p) hp (hV _ p) _
 refine Medal.big (migrate _ _ W A v h1 j t) ?_ ; by_cases p:H=j
 · rw [←p,Pi.single_eq_same]; try simp only [ite_true,↓reduceIte]; exact hy
 simp only [if_neg p,Pi.single_eq_of_ne (Ne.symm p),sum_const_zero]; exact le_rfl
omit hV hp hy
lemma pay_f(p:FleetS P.threshold U.1) : march P H (∑ i∈ W,F i) U+ fuelV P K U=∑ i∈ W,march P (X i) (F i) U:=by rw [len_T]; exact propC U W _ _ _ F hU (fun _ _=>Subset.refl _) p
lemma mark_l (i:Aura n)(D:Support (More n))(t:i≠ H): K i D=0:=by unfold ρ_s soot_T stroke chasmR; simp_rw [Finset.sum_apply, Pi.single_eq_of_ne t, Pi.zero_apply,sum_const_zero] -- tune
end YM.CF.Moto
