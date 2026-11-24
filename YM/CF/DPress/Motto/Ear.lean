import YM.CF.DPress.Plaque.Band
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Taxi Larch Ione
namespace WagesC
variable {n:Side}{k:ℕ}(P:BudgetPoint){a b h d:ℝ}{L:ℕ} (w: Wings k P a n)
-- no representation changes on Plaquettes.P.
abbrev pureQ (α:ℝ) (o:Point n): InkD n:= α • fund o
abbrev αLan (α:ℝ) : RegBudget n:=fun i=> if i=hup i.val.1 then pureQ α i.val.1 else 0
variable (z:ℝ)
open Salt
lemma mold_E (s:Sweep n)(v:Point n): moveHub s (hup v)=hup ((boxA s).symm v):=Subtype.ext (Prod.ext rfl (moving_halo s v).symm)
include w
lemma paysτ(v:Point n): PressB P (hup v) (pureQ z v) h (|z| * (grade P k a*P.threshold^2)):= scale_E _ (budgetPump P w v (hup v) (Subset.refl _) (separation_self v|>.trans_le (Nat.zero_le k)) ) _ -- syntax
local notation "νb" => grade P k a* P.threshold^2
omit w
lemma ξface : Ru Utrue (αLan (n:=n) z):=by
 intro s t U v i F; unfold αLan; have hp(i:Scree.Hub n): i= hup i.val.1 ↔ moveHub s i = hup (moveHub s i).val.1:= Iff.trans (Haro.pure_s s|>.eq_iff |>.symm) (by rw [mold_E (s:=s)]; rfl)
 by_cases h:i=hup i.val.1; swap; · rw [if_neg (mt (hp i|>.2) h),if_neg h]; exact (map_zero _).symm
 rw [if_pos (hp i |>.1 h),if_pos h]
 simp only [pureQ,fund,Pi.smul_apply]; rw [show (feeW (moveHub s i).val.1 (flashA s F):ℝ)=_ from stampW s F i.val.1]; change z • moldV n _= paintR _ _ _ (z • _); rw [map_smul]; apply congrArg; symm
 let S:= prepU (castX s) U (xtra s.charge) n; change paintR s.charge (detX s.s) S ((feeW _ F) • (1:Cipher _))= _; rw [map_smul,map_one]; rfl
include w
abbrev ρtax (a:ℝ)(k:ℕ)(P:BudgetPoint):=Real.exp P.supportExponent*grade P k a
lemma widthP : IncX Utrue (αLan (n:=n) z) P h (ρtax a k P*|z| * P.threshold^2):=by
 let C:= grade P k a*P.threshold^2; let S:= fun i:Scree.Hub n=> if i = hup i.val.1 then |z| * C else (0:ℝ)
 have hE(i:Scree.Hub n):PressB P i (αLan z i) h (S i):=by
    unfold S αLan; split; · rename_i p; exact p.symm ▸ paysτ P w z i.val.1
    exact Vale.rinse ..
 refine ⟨⟨S,hE,fun x=>?_⟩,ξface z⟩; rw [sum_eq_single (hup x)]; swap
 · intro k _ p; by_cases p':k.val.1=x; · unfold S; rw [if_pos p'.symm,if_neg (show k≠ hup k.val.1 from (by simpa only [p'] using p))]; simp [BudgetPoint.mass]
   rw [if_neg (Ne.symm p')]
 swap
 · exact fun h=> (h (mem_univ _)).elim
 unfold S; rw [if_pos rfl,if_pos rfl]; let a':= (hup x).val.2; have ht:P.mass a' (|z| * C)≤ Real.exp (P.supportExponent)* (|z| * C):=by
    refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (mul_nonneg (abs_nonneg _) ?_); exact mul_le_of_le_one_right P.exponent_pos.le (by exact_mod_cast (covers P w x)); exact (Fees.capE P 1 (hup x) le_rfl).priceQ _ (budgetPump P w x (hup x) (Subset.refl _) (separation_self x|>.trans_le (Nat.zero_le k))) -- tune no h requirement? from budgetP at h=1 no met NormX
 refine ht.trans_eq ?_; unfold C ρtax; ring
omit w
lemma freeH(o:Point n): fund o 1=0:=by unfold fund; rw [Plaque.fee_one,map_zero]
lemma δOne(i:Scree.Hub n): αLan z i 1=0:=by unfold αLan; split; rw [pureQ,Pi.smul_apply,freeH,smul_zero]; rfl
end WagesC
end YM.CF.Py.Kay
