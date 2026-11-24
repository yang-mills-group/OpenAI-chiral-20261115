import YM.SU5.WakeFields.OriginPermit
import YM.SU5.WakeFields.TellerMint
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
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open scoped YM.CF.Mew
open Jet Yaw Nor Prism Font Wray Roots Oise Dial
namespace Furrow
variable {I : Type} [Fintype I] [LinearOrder I]
variable {n : Side} {P : BudgetPoint}
    {F F' : Mew.Key I→ ForceBudget n}
    {K : Key I→ Rinse (Seat n) (Copy n)}
    {Y W : Key I → Aura n→ ℝ}{J : Key I → Aura n→ Support (More n)→ℝ} {M : Key I→ Bag n}
    {C:Occlus P} {q : ℕ} {h : ℝ} {σ : I→Seat n}
variable (L : Furrow σ C q F h K Y W J M) (c : ℕ)(p : 1 ≤ h)
open Bake
include L p
-- read ∂E_Z before wake projection at V. allow *mask scope only* on ζ.
open Py
variable (τ:Ids n)
lemma primeVoid (i:I)(X:Aura n)(V:Orbit n)(u:σ i∉ X.val) :
    tipI (fun z=> K z X ∅ X 1 V) [i]=0 := by
 let f:=fun z=> K z X ∅ X 1 V
 have ht:Hush σ X.val f:=fun z v w p t=> congrArg (fun g:Copy n→ Copy n=>g 1 V) (Shelf.stipend L.figure X ∅ X (L.visit X).1 _ v _ p t)
 let A : Flood 1 f:= Shelf.raises (I:=I) L.figure V X X ∅ (F:=fun _=>(1:Copy n)) (Flood.ground (zeroR _)) (L.visit X).2
 exact Neon.husht_B σ X.val f ht A.riv _ i u (by simp)

-- selective.Staff.Chosen threshold outside predicate all coefficients must already vanish on pings.
abbrev countRoot (P: BudgetPoint)(o:I→Seat n)(F': Key I→ RegBudget n)(Z:I→Finset (Aura n))(i:I) : RegBudget n:=
    fun X=> if X.val.1=o i∧lagE X∈Z i then (X.val.2.card:ℂ) • νΦX F' {i} X else 0

variable (A:I→Finset (Aura n))
local notation "Ωc"=> spaceD P F K c τ
local notation "αE"=> countRoot P σ Ωc A
lemma rootAt (Z:I) (X:Aura n)(k:1≤c)(U:Pane n)(t: pingS P.threshold X.val U)
    (ξ:X∈A Z)(h:Scree.Hub n)(g:lagE h=X)(v:h.val.1=σ Z):
    αE Z h U=tipI (fun z=>K z X ∅ X 1 (U,τ)) [Z] := by
 subst X; rw [countRoot,if_pos ⟨v,ξ⟩]; let V:= (U,τ); let Y':=lagE h; let K':=tipI (fun z=>K z Y' ∅ Y' 1 V) [Z]
 have he:νΦX Ωc {Z} h U=bassH (lagE h) • K':=by
    rw [νΦX]; simp_rw [gemI,Mew.Cue,Finset.sort_singleton]; change tipI (fun z=> bassH Y' • spaceG P F K c z Y' (U,τ)) [Z] = _
    simp_rw [← Complex.coe_smul]; rw [tip_C (L.simpleFlow c p Y' (U,τ)),L.primePort c p Z k Y' (U,τ) (hates (by rw [sdiff_empty]; exact t))]
 rw [Pi.smul_apply,he,←Complex.ofReal_natCast,Complex.coe_smul]; exact smul_inv_smul₀ (show (Y'.val.card:ℝ)≠0 from by exact_mod_cast (card_pos.mpr Y'.property).ne') _
lemma rootShape (Z:I)(k:1 ≤ c) (v:∀ (X:Aura n),σ Z∈X.val → X∉ A Z→∀ U:Pane n,pingS P.threshold X.val U→ tipI (fun z=>K z X ∅ X 1 (U,τ)) [Z]=0) : SpanTip P (countRoot P σ (spaceD P F K c τ) A Z) (σ Z) K τ Z := by
 refine ⟨?_,fun X U _=> L.primeVoid p Z X (U,τ)⟩
 intro X U t; unfold countRoot; by_cases q:X.val.1=σ Z
 · by_cases e: lagE X∈A Z
   · exact (show αE Z X U = _ from (L.rootAt c p τ A Z _ k U t e X rfl q).trans (if_pos q).symm)
   rw [if_neg (by simp [e]), if_pos q, v _ (q ▸ X.property) e _ t]; rfl
 rw [if_neg (by simp [q]),if_neg q]; rfl

abbrev payAnchor (P:BudgetPoint)(C:Occlus P):ℝ:= (Sour.spanV P.B*C.η⁻¹)*yσE P C
lemma anchor_nonneg : 0 ≤ payAnchor P C := by
 unfold payAnchor yσE; apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le)); apply mul_nonneg; swap; exact mul_nonneg C.hγ.le (inv_nonneg.mpr (sub_nonneg.mpr C.degree0.le)); unfold Nor.reserveT coin_n stilK; have hp:= C.hη.le; positivity
lemma anchorCircuit (Z:I) : IncX primeU (αE Z) P h (payAnchor P C) := by
 let v:=P.supportExponent+C.η; let w:=P.supportExponent+C.η+C.η
 have a : ForgeB (νΦX Ωc {Z}) (filmK P w) P h (fun _=>yσE P C):= onset_t _ (zero_lt_one.trans_le p) (filmK P w) (fun i z=>filmHue ..) (fun i=>⟨_,filmHon ..⟩) _ (fun z v=>⟨_,(L.lowLens c p τ z v).1⟩) (fun i x=> (L.regPort c p τ i).2 x) (Cue I ({Z}:Finset I))
 obtain ⟨f,hf,H⟩:=a.bit; let g(i:Scree.Hub n):= (i.val.2.card:ℝ)*f i; have he(i):0 ≤ f i:= Roots.gradeE _ _ (hf i) (zero_le_one.trans p)
 apply ForgeInc; refine ⟨g,fun i=> ?_,fun j=>?_⟩
 · unfold g countRoot; split; next p=> simpa only [Complex.norm_natCast] using (súe i _ (hf i) (i.val.2.card:ℂ))
   exact Hope.hi_p (Vale.rinse ..) (mul_nonneg (Nat.cast_nonneg _) (he i))
 unfold payAnchor; refine le_trans ?_ (mul_le_mul_of_nonneg_left (H j) (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le))); rw [mul_sum]; refine sum_le_sum fun i _=> ?_; unfold filmK g; split_ifs with q; swap; · simp
 let X:=lagE i; change tact P.supportExponent P.B X *((X.val.card:ℝ)*f i) ≤ _*(tact w P.B X* _)
 let b:=Sour.spanV P.B*C.η⁻¹; have hb:= (shelf_pay (k:=P.B) (s:=P.supportExponent) C.hη X).trans (mul_le_mul_of_nonneg_left (tact_para (le_add_of_nonneg_right C.hη.le) X) (show 0 ≤ b from mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le)))
 have hh:X.val.card*tact P.supportExponent P.B X ≤ b*tact w P.B X:=hb; change _ ≤ b*_; linarith only [mul_le_mul_of_nonneg_right hh (he i)]

-- sets for resilience.Map. `externalize` predicate all Large.Mark. condition check from M in launch.
lemma deadAt (X:Aura n)(p:∀ z∈hill I,M z X=0)(i:I)(U:Orbit n) : tipI (fun z=>K z X ∅ X 1 U) [i]=0:=by
 refine (lace_C _ (f:=fun z=>K z X ∅ X 1 U) (g:=fun _=>0) (fun z u=>?_) roots).trans (tip_0 _)
 apply Subtype.ext; change (_:Cipher n).val=_
 rw [(L.figure z u).actsF X ∅ X 1 U, p z u]; unfold coll_T; split_ifs <;> simp only [Pi.zero_apply,zero_mul,Sault.rind,map_zero, Subalgebra.coe_zero]
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.rootShape
#print axioms YM.CF.Vow.TreasuryFog.Furrow.anchor_nonneg
#print axioms YM.CF.Vow.TreasuryFog.Furrow.anchorCircuit
