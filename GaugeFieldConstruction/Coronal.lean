import GaugeFieldConstruction.Aspen

/-!
# Status of U1–5. Symbol supply, finite structure theory, stress verification by point prices. This is conditional; requires existence estimates on those prices in the proposed use. Does not prove existence already of an S or its Schwinger reconstruction. Never substitute selected mixed expectation `S_x` to discharge `City S` without doing that work. `Reaches` is on kernels only within Conf.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6700
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Loft Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Row
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}

structure Ticket (u : ℕ→ Carat) (C: Supplies L) where
  dawn : Dawn L C u
  clarity : Typical C dawn.tect
  path: Valley dawn
lemma complete_ticket (h:Blush S atTop u) (p:∀ t: Tot S P L,t=sbar L t→ Typical C t): Nonempty (Ticket u C) := by
  obtain ⟨g⟩:= stressAction C h; have v:=p g.tect g.fires.symm; obtain ⟨P⟩:= returned g v h; exact ⟨⟨g,v,P⟩⟩
namespace Ticket
variable (p : Ticket u C)
-- financial stress tensor, actual, normalized, centered. printed at Four
abbrev J (i j:Axis): UV four:= pens p.dawn.tect.val i j
lemma active : p.dawn.d=Stage.All:=p.path.paysAll
lemma strict i j:p.J i j=p.J j i:=by rw [J,J,pens,pens,ordered_swap i j]
lemma taste (i j) : Calibration.centered (p.J i j) ∧ white (p.J i j):=p.dawn.tect.val.property.1 ..
lemma real_form (i j): shade _ (p.J i j)=p.J i j:= congr_fun (congr_arg (fun x:Tot S P L=> x.val.val) p.dawn.fires) (ordered i j)
lemma minted j : ∑ i:Axis,P i (p.J i j)=0:= (Bend.payW L.toBend ..).symm.trans (congr_fun (congr_arg Subtype.val (show Bend.sum _ L.toBend p.dawn.tect.val=0 from p.dawn.tect.property)) j)
lemma nonzero : ∃ i j,p.J i j≠0:= by
  by_contra! h; apply p.dawn.alive; apply Subtype.ext; apply Subtype.ext; ext1 i; have v:=h i.val.1 i.val.2; rw [J,pens,ordered_same] at v; exact v
-- signs Q2 
lemma price (i x) {n} (v : Fin n→ UV five) (k : Fin n) (f : Test n) (w : Bulb) (h:Bulb.Works w f k): Fathom.paid k i (S.spot v k (Calibration.lift four x)) f=
    ∑ b:Axis, S.tagged (update v k (Calibration.lift four x)) (Calibration.lift _ (p.J b i)) (Bulb.lace f (Bulb.LED w b) (h.cared b)):= by
  rw [p.path.on_conf x i n v f k w h]; rw [deconstant]; rfl
lemma conservation {n} (v : Fin n→UV five) (k) i:
    ∑ j:Axis,Fathom.paid k j (S.spot v k (Calibration.lift _ (p.J j i))) =0:= by
  simp_rw [← L.money]; rw [← map_sum,p.minted,map_zero]
-- UV transfer rates from 81, same p
lemma sharp (h:Blush S atTop u) (i j): Dips ℂ atTop (fun k:ℕ=>let g:=u (p.dawn.i k); (g.G four).c.symm (g.κ^4 • p.J i j)) (pens (totalIx (payment Stage.All)).val i j):= by -- namespace adjustment
  rw [← p.active]
  refine Sailing.constant (maps p.dawn.price (LinearMap.proj (ordered i j) ∘ₗ SymT.subtype)) ?_
  refine Eventually.of_forall fun k=>?_; let g:=u (p.dawn.i k); let x:= g.κ^4 • p.dawn.tect
  change (earning g x).val (ordered i j)=_
  apply (g.G four).c.injective
  rw [← t_pay,earned]; rw [(g.G four).c.apply_symm_apply]; rfl
end Ticket
#print axioms complete_ticket
#print axioms Ticket.conservation
#print axioms Ticket.price
end YM.GaugeFieldConstruction.Ember
