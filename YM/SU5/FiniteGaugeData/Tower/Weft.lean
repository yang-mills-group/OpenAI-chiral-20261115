import YM.SU5.FiniteGaugeData.Tower.Bouquets
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
/-!
# Function faces of the local algebra

Opposite the board of representatives on input Touch prices, we can work in
an equivalent dual norm on *upper* outputs on hospitable plates. Include
the casts of presentation exactly.
-/
open Reed (Fine think)
open Fock Pastry Tenant
variable (S:Finset Cover)(Z₀:Calibration)
def compose (a:Evens S→Purse S):Family Z₀:=∑ v:Evens S,note Z₀ (a v).val (tagWord S v.val)
lemma comp_test (a:Evens S→Purse S):InTest Z₀ true S false (compose S Z₀ a):=by
 refine InTest.sum _ _ fun (v:Evens S) _=>?_
 have ht:= note_t Z₀ (tagWord S v.val) (a v).property (brand S v.val); rw [v.property] at ht; exact ht
noncomputable def banner (F:Family Z₀):Evens S→PairsC→ℂ:= if h:InTest Z₀ true S false F then fun v=> ((circulation S Z₀ h).choose v).val else 0
lemma banner_paid (F:Family Z₀)(q:Evens S):Coeff true S (banner S Z₀ F q):=by
  unfold banner; split
  next v=> exact ((circulation S Z₀ v).choose q).property
  next=>exact ⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩
lemma banner_pays {F:Family Z₀}(x:InTest Z₀ true S false F):F=compose S Z₀ (fun q=>⟨banner S Z₀ F q,banner_paid S Z₀ F q⟩):=by
 have ht: (fun q=> (⟨banner S Z₀ F q,banner_paid S Z₀ F q⟩:Purse S))=(circulation S Z₀ x).choose:=by ext v p; dsimp; rw [show banner S Z₀ F v p=_ from congrFun (congrFun (dif_pos x: banner S Z₀ F=_) v) p]
 rw [ht]; exact (circulation S Z₀ x).choose_spec
variable (n:Side)(p:Tivoli S (Z₀.c n))
local notation "φ"=> costume S Z₀ n p
lemma native_sheet {F:Family Z₀}(h:InTest Z₀ true S false F)(q:Evens S)(x:PairsC): φ (F n (replant S (Z₀.c n) x)) q=banner S Z₀ F q x:=
 (recovered S Z₀ n p (fun q=>⟨banner S Z₀ F q, banner_paid S Z₀ F q⟩) (banner_pays S Z₀ h) _ q).trans ((banner_paid S Z₀ F q).locus _ _ (fun i v _=> tail S (Z₀.c n) (p.hosp) _ _ v) (fun i v _=> tail S (Z₀.c n) (p.hosp) _ _ v))
omit p in
lemma employed (S:Finset Cover)(Z₀:Calibration):∃ n:Side,Tivoli S (Z₀.c n):= ((separates Z₀ (tips S)).mono (fun n v=> (⟨⟨v⟩⟩:Tivoli S (Z₀.c n)))).exists
lemma banner_parts {F G:Family Z₀}(t:InTest Z₀ true S false F)(u:InTest Z₀ true S false G)(z:ℂ)(q:Evens S)(x:PairsC): banner S Z₀ (z • F+G) q x=z* banner S Z₀ F q x+banner S Z₀ G q x:=by
 obtain ⟨n,h⟩:= employed S Z₀
 let g:=t.smul z -- field synt?
 rw [← native_sheet S Z₀ n h ((InTest.smul z t).add u),←native_sheet S Z₀ n h t,←native_sheet S Z₀ n h u]; exact linearity ..
lemma banner_zero (q:Evens S):banner S Z₀ 0 q=0:=by
 obtain ⟨n,h⟩:= employed S Z₀; funext x; rw [← native_sheet S Z₀ n h InTest.zero]; apply norm_eq_zero.mp; exact le_antisymm ((biotech S Z₀ n h 0 q).trans_eq (by rw [norm_zero])) (norm_nonneg _)
lemma banner_scale {F:Family Z₀}(t:InTest Z₀ true S false F)(z:ℂ)(q:Evens S)(x:PairsC): banner S Z₀ (z•F) q x=z*banner S Z₀ F q x:=by simpa only [add_zero,banner_zero S Z₀,Pi.zero_apply] using banner_parts S Z₀ t InTest.zero z q x
lemma banner_sub {F G:Family Z₀}(t:InTest Z₀ true S false F)(u:InTest Z₀ true S false G)(q:Evens S)(x:PairsC):banner S Z₀ (F-G) q x=banner S Z₀ F q x-banner S Z₀ G q x:=by rw [sub_eq_neg_add,←neg_one_smul ℂ G,banner_parts S Z₀ u t,neg_one_mul,←sub_eq_neg_add]
lemma pay_banner {F:Family Z₀}{y:ℝ}(p:InTest Z₀ true S false F)(h:pay F y)(q:Evens S)(x:PairsC): ‖banner S Z₀ F q x‖≤ y:=by
 obtain ⟨n,t⟩:= employed S Z₀; rw [←native_sheet S Z₀ n t p]; exact (biotech S Z₀ n t ..).trans (h ..)
lemma banner_rate {F:Family Z₀}{y:ℝ}(h:InTest Z₀ true S false F)(x:∀ q:Evens S,∀ i, ‖banner S Z₀ F q i‖≤y):pay F ((Fintype.card (Evens S):ℝ)*y):=by
 intro t z; rw [banner_pays S Z₀ h]; unfold compose; simp_rw [Finset.sum_apply]; apply ((norm_sum_le ..).trans (sum_le_sum fun i _=> (pitched ..).trans (x ..))).trans; rw [sum_const,card_univ,nsmul_eq_mul]

section ship
variable {t:Side} (h:Z₀.c n=t)
def paintOp(Q:FC (Single t)):Evens S→ℂ:=fun q=> φ (fold_op h.symm Q) q
lemma delivery {F:Family Z₀}(v:InTest Z₀ true S false F)(q:Evens S)(x:PairsC):
 paintOp S Z₀ n p h (ship h (F n) (replant S t x)) q=banner S Z₀ F q x:=by
 rw [←native_sheet S Z₀ n p v,paintOp]; apply congrArg (fun d=>φ d q); apply coherence
where coherence {c d:Side}(h:c=d)(F:Mark c)(X:PairsC)(S:Finset Cover): fold_op h.symm (ship h F (replant S d X)) = F (replant S c X):=by subst c; rfl
lemma charged_cast (x:FC (Single t))(q:Evens S):‖paintOp S Z₀ n p h x q‖≤‖x‖:= (biotech S Z₀ n p ..).trans_eq (norm_fold _ _)
where norm_fold{c d:Side}(e:c=d)(x:FC (Single c)): ‖fold_op e x‖=‖x‖:=by subst d; rfl
lemma paint_jump (x y:FC (Single t))(q:Evens S):paintOp S Z₀ n p h (x-y) q= paintOp S Z₀ n p h x q-paintOp S Z₀ n p h y q:=by
 rw [sub_eq_neg_add,←neg_one_smul ℂ y,paintOp,fold_ar, Tower.linearity,neg_one_mul,←sub_eq_neg_add]; rfl
where fold_ar{c d:Side}(h:c=d)(x y:FC (Single c))(z:ℂ): fold_op h (z • x+y)=z • fold_op h x+fold_op h y:=by subst c; rfl

end ship
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.delivery
#print axioms YM.CF.Buffered.Afterglow.Tower.banner_sub
