import YM.SU5.WakeFields.WaveRemainder
import YM.CF.Vp929.Match.Outcrop
import YM.CF.Rive.Muck

/-!
# The Rinse on previously perturbed customers
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Rive
attribute [local instance] opCStarAlgebra
variable {n:Side} {I : Type} [LinearOrder I] [Fintype I]
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault Mew
attribute [local instance] Rill.boreKSpace Rill.boreXN
open scoped YM.CF.Mew
variable {P : BudgetPoint} {K : Key I→ Rinse (Seat n) (Copy n)}
    {T : Key I → Cusp n} {M : Key I → Bag n} {σ : I→Seat n}
    {δ : ℕ} (u : ∀ z∈hill I,PictureT P δ (K z) (M z))

lemma liftMask {f : Key I→ Cipher n} {c : ℕ} (p : Flood c (fun z=>(f z).val)) : Flood c f := by
 let v:= yield_R f p.riv; refine ⟨v,fun i w=>?_⟩
 apply Subtype.val_injective; change Mew.sheen (tipI f i)=0; rw [←show tipI _ i=Mew.sheen (tipI f i) from sim_H v Mew.sheen i roots] -- maybe norm overload
 exact p.ebb i w

namespace Shelf
open PowerSeries
include u
lemma raises {d : ℕ} {F : Key I → Copy n} (V : Orbit n)
    (X Y : Aura n) (D : Support (More n))
    (p : Flood d (fun z=>F z V)) (q : ∀ U : Orbit n,Flood 1 (fun z=> M z Y U)) :
    Flood (d+1) (fun z=> K z X D Y (F z) V) := by
 apply liftMask; by_cases a:Bias.αt Y X D δ
 · let W(z):= coll_T P X D (M z Y) V; have ht:Flood 1 W:= by
      unfold W coll_T; split; exact q _; exact Flood.null _
   let B:= (Pastry.cane (Dwell n)).eval.toContinuousLinearMap
   have v:= (ht.times (p.transport Mew.sheen)).transport B; rw [Nat.add_comm] at v
   apply v.cong; intro z p; exact ((u z p).actsF ..).trans (if_pos a)
 apply (Flood.null _).cong; intro z p; exact ((u z p).actsF ..).trans (if_neg a)

lemma music (X : Aura n) (D : Support (More n)) (q : D ⊆ X.val)
    (T0 : ∀ i D, D⊆i.val→∀ V:Orbit n,River (fun z=>T z i D V))
    (M0 : ∀ i U,Flood 1 (fun z=>M z i U)) (c : ℕ) (V : Orbit n) :
    Flood c (fun z=> (PowerSeries.coeff c (Cadre.chip (K z) (T z) X D)) V) := by
 induction c using Nat.strong_induction_on generalizing D X with
 | h i ih =>
   cases i with
   | zero => simp_rw [Cadre.peg]; exact Flood.ground (T0 _ _ q V)
   | succ i =>
     have h(z:Key I): coeff (i+1) (Cadre.chip (K z) (T z) X D)=((i:ℝ)+1)⁻¹ • coeff i (Cadre.stepL (K z) (Cadre.chip (K z) (T z)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
     simp_rw [h, Pi.smul_apply, ←Complex.coe_smul, Cadre.ore, Finset.sum_apply]; apply Flood.scaler; apply Flood.total; intro Y _; apply Flood.total; intro F p; apply Shelf.raises u _ _ _ _ _ (M0 Y); simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; apply Flood.total; intro j w; let N(x:Aura n):= j x; have v: (∑ i∈ F,N i)=i:= (mem_finsuppAntidiag.mp w).1
     exact v ▸ Flood.purchase F (fun k z=> (coeff (j k) (Cadre.chip (K z) (T z) k (D∩k.val))) V) N (fun k s=> ih (j k) (Nat.lt_succ_of_le ((single_le_sum (fun i _=> Nat.zero_le (j i)) s).trans_eq v)) k _ inter_subset_right)

lemma stipend (X : Aura n) (D : Support (More n)) (Y : Aura n)
    (q : Hush σ Y.val (fun z=> M z Y)) :
    Hush σ Y.val (fun z=> K z X D Y) := by
 intro z v w p e; funext f U; apply Subtype.ext; change (K z _ _ _ f U).val=_
 rw [(u z v).actsF, (u w p).actsF, show M z Y=M w Y from q _ v _ p e]
lemma hush (X : Aura n) (D : Support (More n)) (q : D ⊆ X.val) (c : ℕ)
    (T0 : ∀ (i:Aura n) D, D⊆i.val→ Hush σ i.val (fun z=>T z i D))
    (M0 : ∀ i:Aura n,Hush σ i.val (fun z=>M z i)) :
    Hush σ X.val (fun z=> coeff c (Cadre.chip (K z) (T z) X D)) := by
 induction c using Nat.strong_induction_on generalizing D X with
 | h i ih=>
   cases i with
   | zero=> simp_rw [Cadre.peg]; exact T0 _ _ q
   | succ i=>
     have h(z:Key I): coeff (i+1) (Cadre.chip (K z) (T z) X D)=((i:ℝ)+1)⁻¹ • coeff i (Cadre.stepL (K z) (Cadre.chip (K z) (T z)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
     simp_rw [h,Cadre.ore]
     intro z vz w vw e; apply congrArg; apply sum_congr rfl; intro Y y; refine sum_congr rfl (fun F v=> ?_)
     have he : Y.val ⊆ X.val:= by rw [(Cadre.drum_p ..|>.mp v).2.2]; exact subset_union_left
     rw [show K z X D Y=K w X D Y from stipend u X D Y (M0 Y) z vz w vw (fun i t=> e i (he t))]
     apply congrArg; rw [coeff_prod,coeff_prod]; exact sum_congr rfl (fun j l=> prod_congr rfl (fun k s=> ih _ ((single_le_sum (fun i _=> Nat.zero_le (j i)) s).trans_lt ((mem_finsuppAntidiag.mp l).1.trans_lt (Nat.lt_add_one _))) k _ inter_subset_right _ vz _ vw (fun i t=> e i (hush_Y X D q Y F v k s t))))
end Shelf
end YM.CF.Sour
#print axioms YM.CF.Sour.Shelf.hush
#print axioms YM.CF.Sour.Shelf.music
