import YM.SU5.Reconstruction.Quanta.Garret
import YM.SU5.FiniteGaugeData.Tower.Weft
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open Reed (Fine think)
open Fock Pastry Tenant
namespace Garret
abbrev Odds (S:Finset Cover):= Tokens S true
/-! Pay Odd tokens, generalizing Tower/Weft. -/
variable (S:Finset Cover)(Z₀:Calibration)
def composeO (a:Odds S→Purse S):Family Z₀:=∑ v:Odds S,note Z₀ (a v).val (tagWord S v.val)
lemma compO_test (a:Odds S→Purse S):InTest Z₀ true S true (composeO S Z₀ a):=by
 refine InTest.sum _ _ fun (v:Odds S) _=>?_
 have ht:= note_t Z₀ (tagWord S v.val) (a v).property (brand S v.val); rw [v.property] at ht; exact ht
noncomputable def flavor (F:Family Z₀):Odds S→PairsC→ℂ:= if h:InTest Z₀ true S true F then fun v=> ((tokenC S Z₀ h).choose v).val else 0
lemma flavor_paid (F:Family Z₀)(q:Odds S):Coeff true S (flavor S Z₀ F q):=by
  unfold flavor; split
  next v=> exact ((tokenC S Z₀ v).choose q).property
  next=>exact ⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩
lemma flavor_pays {F:Family Z₀}(x:InTest Z₀ true S true F):F=composeO S Z₀ (fun q=>⟨flavor S Z₀ F q,flavor_paid S Z₀ F q⟩):=by
 have ht: (fun q=> (⟨flavor S Z₀ F q,flavor_paid S Z₀ F q⟩:Purse S))=(tokenC S Z₀ x).choose:=by ext v p; dsimp; rw [show flavor S Z₀ F v p=_ from congrFun (congrFun (dif_pos x: flavor S Z₀ F=_) v) p]
 rw [ht]; exact (tokenC S Z₀ x).choose_spec
variable (n:Side)(p:Tivoli S (Z₀.c n))
local notation "φ"=> tint S Z₀ n p
lemma native_page {F:Family Z₀}(h:InTest Z₀ true S true F)(q:Odds S)(x:PairsC): φ (F n (replant S (Z₀.c n) x)) q=flavor S Z₀ F q x:=
 (charged_both S Z₀ n p (fun q=>⟨flavor S Z₀ F q, flavor_paid S Z₀ F q⟩) (flavor_pays S Z₀ h) _ q).trans ((flavor_paid S Z₀ F q).locus _ _ (fun i v _=> tail S (Z₀.c n) (p.hosp) _ _ v) (fun i v _=> tail S (Z₀.c n) (p.hosp) _ _ v))
lemma flavor_parts {F G:Family Z₀}(t:InTest Z₀ true S true F)(u:InTest Z₀ true S true G)(z:ℂ)(q:Odds S)(x:PairsC): flavor S Z₀ (z • F+G) q x=z* flavor S Z₀ F q x+flavor S Z₀ G q x:=by
 obtain ⟨n,h⟩:= employed S Z₀
 let g:=t.smul z -- field synt?
 rw [← native_page S Z₀ n h ((InTest.smul z t).add u),←native_page S Z₀ n h t,←native_page S Z₀ n h u]; exact lengthline ..
lemma flavor_zero (q:Odds S):flavor S Z₀ 0 q=0:=by
 obtain ⟨n,h⟩:= employed S Z₀; funext x; rw [← native_page S Z₀ n h InTest.zero]; apply norm_eq_zero.mp; exact le_antisymm ((quoteToken S Z₀ n h 0 q).trans_eq (by rw [norm_zero])) (norm_nonneg _)
lemma flavor_scale {F:Family Z₀}(t:InTest Z₀ true S true F)(z:ℂ)(q:Odds S)(x:PairsC): flavor S Z₀ (z•F) q x=z*flavor S Z₀ F q x:=by simpa only [add_zero,flavor_zero S Z₀,Pi.zero_apply] using flavor_parts S Z₀ t InTest.zero z q x
lemma flavor_sub {F G:Family Z₀}(t:InTest Z₀ true S true F)(u:InTest Z₀ true S true G)(q:Odds S)(x:PairsC):flavor S Z₀ (F-G) q x=flavor S Z₀ F q x-flavor S Z₀ G q x:=by rw [sub_eq_neg_add,←neg_one_smul ℂ G,flavor_parts S Z₀ u t,neg_one_mul,←sub_eq_neg_add]
lemma pay_flavor {F:Family Z₀}{y:ℝ}(p:InTest Z₀ true S true F)(h:pay F y)(q:Odds S)(x:PairsC): ‖flavor S Z₀ F q x‖≤ y:=by
 obtain ⟨n,t⟩:= employed S Z₀; rw [←native_page S Z₀ n t p]; exact (quoteToken S Z₀ n t ..).trans (h ..)
lemma flavor_rate {F:Family Z₀}{y:ℝ}(h:InTest Z₀ true S true F)(x:∀ q:Odds S,∀ i, ‖flavor S Z₀ F q i‖≤y):pay F ((Fintype.card (Odds S):ℝ)*y):=by
 intro t z; rw [flavor_pays S Z₀ h]; unfold composeO; simp_rw [Finset.sum_apply]; apply ((norm_sum_le ..).trans (sum_le_sum fun i _=> (pitched ..).trans (x ..))).trans; rw [sum_const,card_univ,nsmul_eq_mul]

section ship
variable {t:Side} (h:Z₀.c n=t)
def chargeOp(Q:FC (Single t)):Odds S→ℂ:=fun q=> φ (fold_op h.symm Q) q
lemma possession {F:Family Z₀}(v:InTest Z₀ true S true F)(q:Odds S)(x:PairsC):
 chargeOp S Z₀ n p h (ship h (F n) (replant S t x)) q=flavor S Z₀ F q x:=by
 rw [←native_page S Z₀ n p v,chargeOp]; apply congrArg (fun d=>φ d q); apply coherence
where coherence {c d:Side}(h:c=d)(F:Mark c)(X:PairsC)(S:Finset Cover): fold_op h.symm (ship h F (replant S d X)) = F (replant S c X):=by subst c; rfl
lemma charged_out (x:FC (Single t))(q:Odds S):‖chargeOp S Z₀ n p h x q‖≤‖x‖:= (quoteToken S Z₀ n p ..).trans_eq (norm_fold _ _)
where norm_fold{c d:Side}(e:c=d)(x:FC (Single c)): ‖fold_op e x‖=‖x‖:=by subst d; rfl
lemma charge_jump (x y:FC (Single t))(q:Odds S):chargeOp S Z₀ n p h (x-y) q= chargeOp S Z₀ n p h x q-chargeOp S Z₀ n p h y q:=by
 rw [sub_eq_neg_add,←neg_one_smul ℂ y,chargeOp,fold_ar, Tower.lengthline,neg_one_mul,←sub_eq_neg_add]; rfl
where fold_ar{c d:Side}(h:c=d)(x y:FC (Single c))(z:ℂ): fold_op h (z • x+y)=z • fold_op h x+fold_op h y:=by subst c; rfl

end ship

lemma native_determines {F G:Family Z₀}{n:Side}(p:Tivoli S (Z₀.c n)){b:Bool}(h:InTest Z₀ true S b F)(g:InTest Z₀ true S b G)(k:F n=G n):F=G:=by
 cases b
 next=> exact box_ext Z₀ S h g p.hosp k
 next=>
   nth_rw 1 [flavor_pays S Z₀ h, flavor_pays S Z₀ g]; apply congrArg (composeO S Z₀); funext q; apply Subtype.ext; funext i; change flavor S Z₀ _ _ _=flavor S Z₀ _ _ _; rw [← native_page S Z₀ n p h, ← native_page S Z₀ n p g,k]
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.possession
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.flavor_pays
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.native_determines
