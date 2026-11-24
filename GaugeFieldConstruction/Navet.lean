import GaugeFieldConstruction.Creels
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
variable {M:Tulip.Male}
open scoped ComplexConjugate
noncomputable section
set_option maxRecDepth 3500
-- use implicit norm fixed TC as used in comV
abbrev fena(f:yardLot):ℝ:= ‖f‖
lemma brew_e(f:yardLot):∀ i, ‖f i‖ ≤ fena f:=fun i=> norm_le_pi_norm _ _
lemma weigh_z (X:Pal)(i:lotV) : fena (ηZ X i) ≤ ‖X‖:=by unfold fena ηZ; rw [Pi.norm_single] -- likely Norm choose Matrix
lemma OLine(P:PalOne)(x:Views): ‖P.2.1 x‖≤CostOle P*‖x‖:=by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](V:Ole E F)(x:E),‖V.2.1 x‖ ≤ CostOle V*‖x‖ from by intro _ _ _ _ _ _ V x; exact (V.2.1.le_opNorm x).trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (norm_nonneg _))) P x -- tune
lemma OLine₂(P:PalOne)(x y:Views): ‖P.2.2.val x y‖≤CostOle P* ‖x‖* ‖y‖:=by exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](V:Ole E F)(x y:E), ‖V.2.2.val x y‖≤CostOle V* ‖x‖* ‖y‖ from by
 intro _ _ _ _ _ _ V x y
 exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ((V.2.2.val.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (norm_nonneg _))) (norm_nonneg _))) P x y
lemma read_Z (P:PalOne) : fena (Ωlane P) ≤ CostOle P:= (weigh_z P.1 neutralK).trans (ModuleB.odeG P)
lemma leg_Z (P:PalOne) : fena (Ωleg P) ≤ (Fintype.card slice:ℝ) * (2*CostOle P):=by
 unfold Ωleg; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun i=> (2:ℝ)*CostOle P) _).trans; · simp
 intro i _; let A:= P.2.1 (voltS i); let K:= (-Complex.I) • A; have he: ‖K‖= ‖A‖:=by unfold K; rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
 have ht: ‖K‖ ≤ CostOle P:= he.le.trans ((OLine P (voltS i)).trans (mul_le_of_le_one_right (Ole_non _) tipN))
 change ‖ηZ K (some i,none)-ηZ K neutralK‖ ≤ _
 rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add ((weigh_z ..).trans ht) ((weigh_z ..).trans ht)) -- tune
abbrev railC:ℝ:= Fintype.card (slice ×slice) * (2*(2* ‖(-1/2:ℂ)‖))
lemma ray_Z (P:PalOne) : fena (Ωray P) ≤ railC*CostOle P:=by
 unfold Ωray; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun i=> (2:ℝ)*(2* (‖(-1/2:ℂ)‖*CostOle P))) _).trans; · simp only [sum_const,card_univ,nsmul_eq_mul, railC]; exact (le_of_eq (by ring)) -- recurring
 intro i _; let A:=P.2.2.val (voltS i.1) (voltS i.2); let K:= (-1/2:ℂ) • A; let c:=‖(-1/2:ℂ)‖*CostOle P; have hx:0≤CostOle P:= Ole_non _; have ht: ‖A‖≤ CostOle P:= (OLine₂ P _ _).trans ((mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hx tipN) (norm_nonneg _)).trans (mul_le_of_le_one_right hx tipN))
 have hg(a b:lotV): fena (ηZ K a-ηZ K b)≤ 2*c:=by
    have he: ‖K‖≤ c:= ((show ‖K‖=‖(-1/2:ℂ)‖*‖A‖ from norm_smul ..).le.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))); rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add ((weigh_z ..).trans he) ((weigh_z ..).trans he))
 change ‖spinD i.1 i.2 K‖≤ 2*(2*c); rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add (hg _ _) (hg _ _))
-- cost signal
private def HopeX (A:Pal): ℂ→L[ℝ] Pal:= ContinuousLinearMap.restrictScalars ℝ ((ContinuousLinearMap.id ℂ ℂ).smulRight A)
private lemma ZK_d (A:Pal) : tautF (HopeX A) ≤ ‖A‖:=by
 apply ContinuousLinearMap.opNorm_le_bound; · exact norm_nonneg _
 intro p; change ‖p • A‖≤ ‖A‖*‖p‖; rw [norm_smul,mul_comm]
variable (o:Skye.Seat n)
lemma shot_x (k:lotV)(A:Pal)(u:20<n.val): CostOle (signalK o k A) ≤ ‖A‖* (48:ℝ)^2:=by
 let Z:=ξK o k; let P:=bookP Z 1; apply (post_cost P (HopeX A)).trans; have hv(i:Cover)(p:lateral i≤4): (separation o (node (parked o i)):ℝ) ≤12:=by exact_mod_cast spot_gap o i p u
 have hz: ‖Z‖ ≤48:= (peak_shifts o (measuresN o k).1 (measuresN o k).2 12 (hv _ (knot_rad k).1) (hv _ (knot_rad k).2)).trans (by norm_num)
 exact mul_le_mul (ZK_d A) ((fundK Z 1 hz (by norm_num)).trans (by simp only [norm_one,mul_one]; exact le_rfl)) (Ole_non P) (norm_nonneg _) -- tune
lemma notes_d (f:yardLot)(u:20<n.val): CostOle (comV o f) ≤ (Fintype.card lotV:ℝ)*(fena f*48^2):=by
 unfold comV; apply (weights_n ..).trans; apply (sum_le_sum (g:=fun i=> fena f*48^2) _).trans; · simp
 intro i _; exact (shot_x o _ _ u).trans (mul_le_mul_of_nonneg_right (brew_e f i) (by norm_num))
lemma mint_mult (x y:ℝ): mintPay (x*y)=mintPay x*y:=by unfold mintPay; ring
abbrev tannin:ℝ:=mintPay ((Fintype.card lotV:ℝ)*48^2)
lemma mint_Z :0≤ tannin:=by
 have hc:0 ≤ (Fintype.card lotV:ℝ)*48^2:=mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _); have hz:0≤ (4:ℝ):= by norm_num
 exact mul_nonneg (mul_nonneg hz (Ole_non (bladeL false))) (mul_nonneg (mul_nonneg hz (BP_u false)) (mul_nonneg (mul_nonneg hz hc) (mul_nonneg (mul_nonneg hz (BP_u true)) (Ole_non (bladeL true)))))
lemma marsC (f:yardLot)(u:20<n.val) : CostOle (mkD o M f) ≤ tannin*fena f:=by
 let b:= CostOle (markJet o (notesK o f 1) 1); have hp: b ≤ (Fintype.card lotV:ℝ)*48^2* fena f:=by unfold b; rw [stamps o f one_ne_zero]; exact (notes_d o f u).trans_eq (by ring)
 rw [← billMore o M f (h:=1) one_ne_zero]; exact (costmint o M _ hp).trans_eq (mint_mult ..)
abbrev legP:ℝ:= (Fintype.card slice:ℝ)*2
abbrev doll₁:ℝ:=1+tannin
abbrev doll₂:ℝ:= (1+tannin* legP) * doll₁
lemma pali_g1 (f:PalOne)(u:20<n.val): CostOle (grainD (M:=M) o f) ≤ doll₁ * CostOle f:= by
 unfold grainD doll₁; rw [add_mul,one_mul]; exact (polV_sub ..).trans (add_le_add le_rfl ((marsC o _ u).trans (mul_le_mul_of_nonneg_left (read_Z f) mint_Z))) -- tune
lemma leg_p : 0≤ legP:=by unfold legP; positivity
lemma pali_g2(f:PalOne)(u:20<n.val): CostOle (gainT (M:=M) o f) ≤ doll₂*CostOle f:=by
 unfold gainT doll₂; apply (polV_sub ..).trans; let G:= grainD (M:=M) o f; have ht: CostOle G ≤ doll₁ * CostOle f:=pali_g1 o f u
 have hx:fena (Ωleg G)≤legP*(doll₁*CostOle f):= ((leg_Z G).trans_eq (show (Fintype.card slice:ℝ)*_= legP*CostOle G from (mul_assoc ..).symm)).trans (mul_le_mul_of_nonneg_left ht leg_p)
 have hg: CostOle (mkD o M (Ωleg G)) ≤ tannin*(legP*(doll₁*CostOle f)):= (by exact ((marsC o (Ωleg G) u).trans (mul_le_mul_of_nonneg_left hx mint_Z))) -- syntax
 apply (add_le_add ht hg).trans_eq; ring
abbrev QuiltB:ℝ:=1+legP*doll₁+railC*doll₂
lemma rail_p : 0≤ railC:=by unfold railC; positivity
lemma Cushion (V:PalOne)(u:20<n.val) : fena (fieldX M o V)≤ QuiltB*CostOle V:=by
 let T:=grainD (M:=M) o V; let G:=gainT (M:=M) o V; unfold fieldX
 have h1: fena (Ωleg T)≤ legP*doll₁* CostOle V:=by rw [mul_assoc]; exact ((leg_Z T).trans_eq (show _=legP*CostOle T from (mul_assoc ..).symm)).trans (mul_le_mul_of_nonneg_left (pali_g1 o V u) leg_p)
 have h2:fena (Ωray G)≤railC*doll₂*CostOle V:=by rw [mul_assoc]; exact (ray_Z G).trans (mul_le_mul_of_nonneg_left (pali_g2 o V u) rail_p) -- tune
 apply le_trans (b:= ‖Ωlane V+Ωleg T‖+‖Ωray G‖) (norm_add_le ..); apply (add_le_add ((norm_add_le ..).trans (add_le_add (read_Z V) h1)) h2).trans_eq; unfold QuiltB; ring
end -- noncomp
end Layout
end Lenten
end YM.CF.TableF
end
