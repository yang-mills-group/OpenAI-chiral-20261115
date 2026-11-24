import YM.SU5.SatinWard.Resolution.Fresca
import ForceSatin.Falcon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
variable (D:Division) {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ}(C:Checked q t g d a k m)
local notation "Z₁"=> Openc (More N) d
open Salt
open Pannier.Chancel BPress BPress.Spin Papyrus.Franc.SatinForce
-- L1. preserve.S wires.B
noncomputable def frameR {ι:Type}[Fintype ι][DecidableEq ι](A:Op ι):ℝ:= ∑ i,∑ j, ‖A i j‖
lemma frameP (A:Op Γ) : 0≤frameR A:= sum_nonneg fun i _=>sum_nonneg fun j _=> norm_nonneg _
private lemma RFormula (β:Type*)[Fintype β]{ι:Type}[Fintype ι][DecidableEq ι] (A:β→Op ι):frameR (∑ i,A i) ≤ ∑ i,frameR (A i):=by
 unfold frameR; simp_rw [Matrix.sum_apply]; conv_rhs=> rw [sum_comm]
 refine sum_le_sum (fun i _=>?_); rw [sum_comm (s:=(univ:Finset β))]; exact sum_le_sum fun j _=> norm_sum_le .. -- syntax next-line
lemma estimateR {V:Toll Γ}{S:Sa N}{A:Branch.Raw Z₁ Γ} (p:Suite (badge _) (bail N d) (bail N d) S V A)(x:Z₁): frameR (A x) ≤ ledgerV V:= sum_le_sum (fun i _=> sum_le_sum (fun j _=> ((p.expo i j).bounded x))) -- infer Raw
lemma guideR (hp:0 < a)(o:Seat N)(F:SOp N)(h:Soak o F a b d)(x:Z₁):frameR (F x.val) ≤ b:=by
 obtain ⟨H,W,h,t,e,g⟩:=h; rw [g x]; refine (RFormula _ _).trans ((sum_le_sum (fun i _=>(estimateR (h i) x).trans ?_)).trans e); exact le_mul_of_one_le_left (sum_nonneg (fun k _=> sum_nonneg (fun j _=>(h i).nonn k j))) (Branch.rent_one hp.le i) -- _
variable (U:Pane N)(b₀:Site N)
local notation "Ω"=> LitCurrent.expiry (4*a) v
local notation "E♭" β:max=> (centHat D b₀ E t q k β)
local notation "G"=> offsetMask q.B b₀
include C
lemma lakeLife (i:FaceDir): frameR ((E♭ i) U) ≤ LitCurrent.expiry (4*a) v:=by
 let W:=grantJ D E (b₀,i); let V:Orbit N:=(U,Classical.arbitrary _); have hx:moored (node b₀) W:=E.moorJ (b₀,i); change frameR (live t q k b₀ W V.1)≤_; rw [noTag b₀ W C hx]; split; swap; · unfold frameR; simp only [Matrix.zero_apply,norm_zero,sum_const_zero]; exact soakCostNN (totals W C.hint hx k).1.pay
 exact guideR C.hint (node b₀) _ (totals W C.hint hx k).1.pay (roller C.angle C.roof V)
omit C
variable (ζ:ℝ) (hScope:∀ i∈ leaks (offsetMask q.B b₀),SU.group.chord (U i) ≤ ζ)
include hScope C
variable (Y:Orbit N) (hY:Y.1=U)(π:pingS q.threshold (offsetMask q.B b₀) Y.1) (W:StageTree N d (4*a) v)(hp:moored (node b₀) W)
local notation "Φ"=>roller C.angle C.roof
local notation "Ψ"=> mintN N C.angle
include hY π hp
-- Pointwise variations for kept nonzero W at endpoints.A.Zone.Board.
lemma ripS(x:Edge (Seat N))(Z:Sa N)(p:(Z.card<k))(i j:Single N)(h:W.W Z i j≠0)(w:x∈leaks Z)(pζ:0≤ζ): ‖(Φ Y).val x- (Ψ).val x‖ ≤ sphereRate*ζ:=by
 let z:= reaches_walk b₀ W C hp Z i j p h Y π; have hc': Z ⊆ G:=(halo_subset (m+10) _).trans (reachesHead b₀ W C hp _ _ _ p h); obtain ⟨p,l⟩:= (Finset.mem_filter.mp w).2
 have hx: SU.group.chord (U x) ≤ ζ:= hScope _ (mem_filter.mpr ⟨mem_univ _, hc' p, hc' l⟩); have he: t Y x=U x:= by rw [←hY]; exact z x p l
 have hb:0<sphereRate:= sphereRate_cost.positive; have Z: ‖brand (U x)-brand 1‖≤ sphereRate*ζ:=by rw [Prod.norm_def]; refine (max_le (sphereRate_cost.bot (U x) 1) (sphereRate_cost.top (U x) 1)).trans ?_; rw [BPress.chord.one]; exact mul_le_mul_of_nonneg_left hx hb.le
 apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb.le pζ)).2; intro z; change ‖profile _ _ z-profile _ _ z‖≤_; unfold profile; cases z <;>simp only [Bool.false_eq_true, ↓reduceIte,←star_sub,norm_star,he]; exact Z; exact Z
lemma adaptR(Z:Sa N)(p:Z.card<k)(i j:Single N) (pζ:0≤ζ): ‖W.F Z () (Φ Y) i j-W.F Z () Ψ i j‖ ≤ ((4*(k:ℝ)*sphereRate * ζ)/d)* (W.W Z i j):=by
 let e:ℝ:=4*(k:ℝ)*sphereRate; let H:=W.W Z i j; let z1:=(W.coat Z|>.1 ()).expo i j; have v:z1=z1:=rfl; have hb:0≤H:=(W.coat Z|>.1 ()).nonn i j
 by_cases h:W.W Z i j=0; · exact le_trans (z1.variation ..) (by rw [h]; simp) -- goals
 let c:=(leaks Z); have hf:c.card ≤ k*4:=le_trans (card_le_card (show leaks Z⊆ Z×ˢ(univ:Finset Axis) from fun i hi=>mem_product.mpr ⟨(mem_filter.mp hi).2.1,mem_univ _⟩)) (by rw [card_product,card_univ,show Fintype.card Axis=4 from by decide]; omega)
 apply le_trans (z1.variation ..); change H * (fare Z _ _ /|d|) ≤ _*H; rw [abs_of_pos C.angle,mul_comm H]; refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ C.angle.le) hb; unfold fare; refine (sum_le_sum (s:=c) (fun x u=> ripS q t C U b₀ ζ hScope Y hY π W hp x Z p i j h u pζ)).trans ?_ -- args D unused.Tune. gcongr. proof.B
 rw [sum_const,nsmul_eq_mul]; have hx:(c.card:ℝ) ≤ (k:ℝ)*4:=by exact_mod_cast hf
 exact (mul_le_mul_of_nonneg_right hx (mul_nonneg sphereRate_cost.positive.le pζ)).trans_eq (by ring)
lemma reviseR (pζ:0≤ζ): frameR ((beforePing W k (profile (t Y)))-(beforePing W k (profile (1:Pane N)))) ≤ LitCurrent.expiry (4*a) v * (4*(k:ℝ)*sphereRate*ζ/d):=by
 let x:=Φ Y; let Z:= 4*(k:ℝ)*sphereRate*ζ/d; have hZ:0 ≤ Z:=div_nonneg (mul_nonneg (mul_nonneg (by positivity) sphereRate_cost.positive.le) pζ) C.angle.le; let C':= (totals W C.hint hp k).1.pay; have he:= saw_line W hp (show 0<4*a by linarith only [C.hint]); rw [mul_comm (LitCurrent.expiry ..)]; apply le_trans _ (mul_le_mul_of_nonneg_left he hZ); change frameR (beforePing W k x.val-beforePing W k (Ψ).val) ≤ Z*_; rw [beforePing,beforePing,dif_pos x.property,dif_pos (Ψ).property]; unfold retain Swell.tallyC; rw [←sum_sub_distrib,mul_sum]; refine (RFormula _ _).trans (sum_le_sum (fun i _=>?_)); split_ifs with w; swap; · simp only [frameR,sub_self,Matrix.zero_apply,norm_zero,sum_const_zero]; exact mul_nonneg hZ (mul_nonneg (Branch.rent_pos ..).le (sum_nonneg (fun α _=>sum_nonneg (fun j _=>(W.coat i|>.1 ()).nonn α j))))
 calc
  _ ≤ Z * ledgerV (W.W i):=by unfold ledgerV; simp_rw [mul_sum]; exact sum_le_sum (fun α _=>sum_le_sum (fun j _=>adaptR q t C U b₀ ζ hScope Y hY π W hp i w α j pζ))
  _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sum_nonneg (fun α _=>sum_nonneg (fun j _=>(W.coat i|>.1 ()).nonn α j))) (Branch.rent_one (by have he:= C.hint; positivity:0≤4*a/2) i)) hZ
#print axioms reviseR
omit hY π hp
local notation "Λ"=> (4*(k:ℝ)*sphereRate*ζ/d)
def labV(ξ v:ℝ)(k:ℕ)(ζ d:ℝ):ℝ:= LitCurrent.expiry (4*ξ) v * (4*(k:ℝ)*sphereRate*ζ/d)
lemma executeR (i:FaceDir)(H:pingS q.threshold (offsetMask q.B b₀) U) (pζ:0≤ζ): frameR (centHat D b₀ E t q k i U-centHat D b₀ E t q k i 1)≤ labV a v k ζ d:=by
 let Y:Orbit N:=(U,Classical.arbitrary _); let W:=grantJ D E (b₀,i); let Z:Orbit N:=(1,Classical.arbitrary _); let X:= Φ Z; have hp:moored (node b₀) W:=E.moorJ (b₀,i); change frameR (live t _ _ _ W Y.1-live _ _ _ _ W Z.1) ≤ _; rw [noTag b₀ W C hp,noTag b₀ W C hp]; have hZ:pingS q.threshold (offsetMask q.B b₀) Z.1:=ping_f q _; have h:pingS q.threshold (offsetMask q.B b₀) Y.1:=H
 rw [if_pos h,if_pos hZ,runs _ W C hp Z hZ 1 (mintN _ C.angle) rfl (fun _ _ _ _ _ _ _ _=>rfl)]; exact reviseR q t C U b₀ ζ hScope Y rfl h W hp pζ
#print axioms executeR
end AuroraX
end YM.CF.LitCurrent
