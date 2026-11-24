import YM.SU5.WakeFields.FairWitness
import YM.SU5.Exchange.Force.Cloud
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Rue
namespace TreasuryFog
open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open Roots Py
open scoped YM.CF.Mew

-- subtraction expense. Can ask with any weights
lemma SanEase {J : Type} {F G:ForceBudget n} (μ : Force n→J→ℝ) (H : SanB F μ P h (fun _=>a)) (T : SanB G μ P h (fun _=>b)) : SanB (F-G) μ P h (fun _=> a+b) := by
 obtain ⟨f,t,u⟩:=H.bit; obtain ⟨g,r,z⟩:=T.bit; refine ⟨f+g,fun i=> ?_,fun j=>?_⟩
 · have ht:=dom_h i _ _ (t i) (dúe i _ (r i) (-1))
   rw [norm_neg,norm_one,one_mul,neg_one_smul,←sub_eq_add_neg] at ht; exact ht
 simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (u _) (z _)
lemma storeWidth {F G : ForceBudget n}(u : ℕ)(p:FlagWidth P F u)(t:FlagWidth P G u) : FlagWidth P (F-G) u := by
 intro i V w; by_cases v:F i V=0
 · apply t i V; intro z; apply w; rw [Pi.sub_apply,Pi.sub_apply,v,z,sub_zero]
 exact p i V v

namespace Furrow
variable {I : Type} [Fintype I] [LinearOrder I]
variable {F : Mew.Key I→ ForceBudget n}
    {K : Key I→ Rinse (Seat n) (Copy n)}
    {Y W : Key I → Aura n→ ℝ}{J : Key I → Aura n→ Support (More n)→ℝ} {M : Key I→ Bag n}
    {C:Occlus P} {q : ℕ} {σ : I→Seat n}
variable (L : Furrow σ C q F h K Y W J M) (p : 1 ≤ h) (u : ℕ)(τ : Ids n)
include L p
variable {t : ℕ}(pT:Force_M P.B σ t) (z : Key I)(U : ∀ i, ‖z i‖ ≤ 2)
lemma deepShelf (a:ℝ)(w: 4 ≤ Real.exp a)(s: 0≤a)(b:9*a*t ≤ C.η*(P.B:ℝ)^2)(D:Force_M P.B σ t) (u':∀ i,‖z i‖ ≤ 2) :
    IncX primeU (rim_C σ (spaceD P F K u τ) z) P h (sigma (C.η+C.η) P.B*yσE P C) := by
 apply ForgeInc
 have v':9*a*t ≤ ((C.η+C.η)/2)*(P.B:ℝ)^2:= by rw [show (C.η+C.η)/2=C.η from by ring]; exact b
 refine manyCircuit σ D _ (L.regPort u p τ) z 2 u' (C.η+C.η) a P.supportExponent one_le_two (by linarith) s (add_nonneg C.hη.le C.hη.le) (zero_lt_one.trans_le p) (fun i v=>?_) v'
 rw [←add_assoc]; exact ⟨_,(L.lowLens u p τ i v).1⟩
lemma litShelf (a:ℝ)(w:4 ≤ Real.exp a)(s:0≤a)(b:6*a*t ≤ C.η*(P.B:ℝ)^2)(D:Force_M P.B σ t)(u':∀ i,‖z i‖ ≤ 2) :
    Dark primeU (bustle σ (placePort P F K u) z) P h (Real.exp (a*t)*(yσF P C+yσF P C)) := by
 apply SanDark
 let τ' := Classical.arbitrary (Ids n)
 refine forceCircuit σ D _ (L.deltaPort u p) z 2 u' C.η a P.supportExponent one_le_two (by linarith) s C.hη.le (zero_lt_one.trans_le p) (fun i v=>?_) b
 exact SanEase _ (F:=spacePort P F K u i) (G:=spacePort P F K 0 i) ⟨_,(L.lowLens u p τ' i v).2⟩ ⟨_,(L.lowLens 0 p τ' i v).2⟩
lemma portalWidth : FlagWidth P (bustle σ (placePort P F K u) z) (cipherK q) := by
 let Δ:=placePort P F K u; have ht(z:Key I)(v:z∈hill I)(u:ℕ): FlagWidth P (spacePort P F K u z) (cipherK q):=
    glowWidth _ _ _ (fun x d w=> (L.rackPay u p z v x d w).loaf)
 have hc(i:Key I)(v:i∈hill I):FlagWidth P (Δ i) (cipherK q):= storeWidth _ (ht i v u) (ht i v 0)
 intro i x v; unfold bustle at v; rw [Finset.sum_apply, Finset.sum_apply] at v
 obtain ⟨b,h,r⟩:= exists_ne_zero_of_sum_ne_zero v
 have he : νΦK Δ b i x≠0:= fun p=> r (by
    change pine b z • νΦK Δ b i x=0; rw [p, smul_zero])
 by_contra g; apply he; change tipI _ _=0; rw [show tipI _ _ = _ from (lace_C (Mew.Cue I b) (f:=fun z=> Δ z i x) (g:=fun _=>0) (fun z v=>by by_contra t; exact g ((hc z v) i x t)) roots)]; exact tip_0 _
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.deepShelf
#print axioms YM.CF.Vow.TreasuryFog.Furrow.litShelf
#print axioms YM.CF.Vow.TreasuryFog.Furrow.portalWidth
