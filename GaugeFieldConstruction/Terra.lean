import GaugeFieldConstruction.Cache

/-!
# (95)-(101) transfer for a shared S extraction
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module RawBank Stage Row
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One
attribute [local instance] iG iF iX iU iT2 iW2 iV iS

variable {S : City} {P:Axis→Across} {L : Sheds S P}
variable (C:Supplies L) {u : ℕ→Carat} (H:Blush S atTop u)
local notation "Ls"=> Tot S P L
private instance ftS:Module.Finite ℂ ↥SymT:= finiteInvariant .. -- already private ftS maybe
private instance stS:Module.Finite ℂ ↥(Tot S P L):= @FiniteDimensional.finiteDimensional_submodule ℂ SymT _ _ _ _ _

def desks (u:Carat) (d : Floor) (t:Tot S P L) (Ω:Ortho.Skew) : Module.End ℂ (UV d):= (lens u d).symm.toLinearMap ∘ₗ ((C.Y d t Ω) ∘ₗ (lens u d).toLinearMap)

structure Dawn (L:Sheds S P) (C:Supplies L) (u:ℕ→Carat) where
  bill: Scope L
  tect : Tot S P L
  unit : C.heart bill tect=1
  only (x:Tot S P L) : C.heart bill x=1→x=tect
  d : District
  yes : Live d
  i : ℕ→ℕ
  mon : StrictMono i
  price : Dips ℂ atTop (fun k=> earning (u (i k)) ((u (i k)).κ^4 • tect)) (totalIx (payment d)).val
namespace Dawn
variable {C}
lemma fires (x:Dawn L C u): sbar L x.tect = x.tect:= sincere _ _ _ x.unit x.only
lemma alive (x:Dawn L C u): x.tect ≠ 0:= by
  haveI : Nontrivial ↥Ls:= finrank_pos_iff.mp (counts L x.bill).1
  intro p
  have h:=x.unit; rw [p,map_zero] at h
  obtain ⟨v,hv⟩:=exists_ne (0:Ls)
  exact hv (Eq.symm (LinearMap.congr_fun h v))
include H
lemma pays (v:Dawn L C u) (Ω) (i): Dips ℂ atTop (fun k=> desks C (u (v.i k)) i v.tect Ω) (enlarged v.d i Ω) := by
  let q:=u ∘ v.i
  have P:= rimmed (H.promo _ v.mon) C (fun k=> (q k).κ^4 • v.tect) (payment v.d) v.price i Ω
  apply dotted
  intro a
  refine Sailing.constant (P a) (Eventually.of_forall fun k=>?_)
  change horn C (q k) i ((q k).κ^4 • v.tect) Ω a= _; unfold horn; rw [smul_smul, ← mul_pow, inv_mul_cancel₀ (q k).nζ,one_pow,one_smul]; rfl
lemma comes (v:Dawn L C u) (i): Dips ℂ atTop (fun k=>levelP (C.theta v.tect) (u (v.i k)) i) (packΘ (payment v.d).1 (payment v.d).2 (basis i)):= by
  let q:=u ∘ v.i
  apply dotted; intro a; refine Sailing.constant (pledge (H.promo _ v.mon) C (fun k=> (q k).κ^4 • v.tect) (payment v.d) v.price i a) (Eventually.of_forall (fun k=>?_))
  change hip C (q k) ((q k).κ^4 • v.tect) _ _= _; unfold hip; rw [smul_smul,← mul_pow,inv_mul_cancel₀ (q k).nζ,one_pow,one_smul]; rfl
end Dawn
include H
-- The central transfer application. Suppressed q_81 assumptions ONLY beyond rank. Use on continuum S, don't apply on free both slots.
theorem stressAction : Nonempty (Dawn L C u) := by
  have y := supply_status L H.toViews
  obtain ⟨i,hi,Q,q⟩:= sweepA L H
  obtain ⟨d,t,h,T,p,q,g⟩:= Seeing.paidUnit (H.promo i hi) C y Q q
  exact ⟨⟨y,t,T,p,d,h,i,hi,q⟩⟩
#print axioms stressAction
end YM.GaugeFieldConstruction.Ember
