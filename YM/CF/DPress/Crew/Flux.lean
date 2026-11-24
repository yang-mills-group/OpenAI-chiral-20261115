import YM.CF.DPress.Crew.Burst
import Mathlib.Topology.MetricSpace.Contracting
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay Glyph Nacre Docket Tutor
variable {N:Side}{P:BudgetPoint}{h W a b c t M L u e:ℝ}{T S:BeatL N}{D:Docket P}{q:ℕ}{F:Scree.Loom N}(A:BondL T S (body_Q 1) b c a e)(v:Room F P e u h q)
variable {K:ℝ}{X Y:Cusp N}(G:RegBudget N)(τ:Ids N) (j:ℕ)(m:Male)(χ:Finset (Scree.Hub N))
open Flight -- ASCII
namespace Resident
local notation "rΩ"=> Tutor.RadP P W h K
local notation "Ld"=> StackL
variable (H:Tutor P h W a b c)(p:pureB A 1) (w0:0<K)(tK:Ride P h a b c M D)(hK:Tutor.RadP P W h K≤M)(hk:D.Tr≤K/32) (uK:1≤j)(hc0:liveB χ)(hz:∀ i:Scree.Hub N,coverNumber P.B i.val.2≤1 → i∈χ) (Q: Resident D X q h)
open DPress.Fees Moral Rosy
open scoped NNReal YM.CF.Mew -- Mew for Billing tactics outside?
variable (vG: IncX Utrue G P h K)
local notation "Fq"=> imageS A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG
include H Q w0 tK hK hk uK hc0 vG p
abbrev Υc : ℝ≥0:= ⟨(3:ℝ)/256,by norm_num⟩
lemma constrained : ContractingWith Υc Fq:=by
 refine ⟨(by change (3:ℝ)/256<1; norm_num),LipschitzWith.of_dist_le_mul fun i t=>?_ ⟩ -- use
 let Z:D.Pair h 0 X X (cipherK q):=by constructor; exact le_rfl; exact zero_le_one; exact Q.lane; exact Q.lane; rw [sub_self,zero_mul]; exact (fortune (n:=N) _ _ _ H.boot).zero_p; rw [sub_self,zero_mul]; exact (νreg (n:=N) _ _ _ true H.boot).zero_p; exact fun _=>rfl
 have hp:=H.bright w0; have hz:IncX Utrue (G-G) P h (K*0/4):=by rw [sub_self,mul_zero,zero_div]; exact ⟨(billP (n:=N) _ H.boot).zero_p.weight,rust⟩ -- weight projection of def red
 have he:= αQt A v G τ j m χ H p w0 tK hK hk uK hc0 Q t i Q G hz Z; rw [←imageX _ _ _ _ _ _ _ H p w0 tK hK hk uK hc0 Q vG i,←imageX _ _ _ _ _ _ _ H p w0 tK hK hk uK hc0 Q vG t,mul_zero,zero_add] at he
 have hm(U V:ΘS rΩ):dist U V=‖riseV U-riseV V‖:=by change dist (riseV U) (riseV V)=_; rw [dist_eq_norm]
 rw [hm,hm]; refine ((div_le_iff₀ hp).1 he).trans_eq ?_; rw [show ‖riseV i-riseV t‖ = hΔ i t*RadP P W h K from (Flight.balance i t hp).symm]; change _=(3/256:ℝ)*_; ring
omit H Q w0 tK hK hk uK hc0 vG p
lemma completeT (t:ℝ): CompleteSpace (ΘS t):=by
 letI: CompleteSpace Θ:= FiniteDimensional.complete ℝ _; haveI : IsClosed {v:Θ| ‖v‖ ≤ t}:= isClosed_le continuous_norm continuous_const; exact IsClosed.completeSpace_coe (s:={v:Θ| ‖v‖ ≤ t})
include H Q w0 tK hK hk uK hc0 vG p
def starH : ΘS (RadP P W h K):=by letI:= Cad.nonzero ((H.bright w0).le); letI:= completeT (RadP P W h K); exact ContractingWith.fixedPoint Fq (constrained A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG)
local notation "Yp" => starH A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG
lemma βs : (Fq) (Yp)=Yp:=by letI:= Cad.nonzero ((H.bright w0).le); letI:= completeT (RadP P W h K); exact (constrained A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG).fixedPoint_isFixedPt
lemma shop : Settle A v G τ j m χ X (Yp).val:=(congrArg riseV (βs A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG)).symm.trans (imageX ..) -- tune direction
lemma onto(i:ΘS rΩ)(u:Settle A v G τ j m χ X i.val): i=Yp:=by
 letI:= Cad.nonzero ((H.bright w0).le); letI:= completeT (RadP P W h K); exact (constrained A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG).fixedPoint_unique (Subtype.ext (Subtype.ext ((imageX A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG i).trans u.symm))) -- u.symm invalid
-- shrink under smaller-ball permission; need posit≥0, choose need ζfoot fall
lemma ushop (s:ℝ)(u:0<s)(qL: s≤K)(t':D.Tr ≤ s/32)(g:IncX Utrue G P h s): ‖(Yp).val‖ ≤ RadP P W h s:=by
 have zξ:RadP P W h s≤ RadP P W h K:= div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left qL (by have t':= H.heat; positivity)) (by positivity)
 let f:= starH A v G τ j m χ H p u tK (zξ.trans hK) t' uK hc0 Q g; let z:ΘS rΩ:= ⟨f.val,f.property.trans zξ⟩; rw [← onto A v G τ j m χ H p w0 tK hK hk uK hc0 Q vG z (shop ..)]; exact f.property
end Resident
end YM.CF.Sour.Heath
