import YM.SU5.Selected.Cor.Pavilion
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Stencil (pulseNode pval)
open Rubric
open Afterglow Afterglow.Tapestry
attribute [local instance] opCStarAlgebra
-- narrow neutral algebra including products. Need separate ambient eval & comm proof. keep support. Compare Nation.
open Commission
namespace Mezz
set_option synthInstance.maxSize 26000
attribute [local instance] opCStarAlgebra
open Stencil (load label)
variable (A:Mezz)(K:Calibration)(e:A.Legate)
open Afterglow.Tower.SlabMark
attribute [local instance] opCStarAlgebra
local notation "V₀"=> A.Broad
variable {W:Window.Family}(F:Sermon A K W)
local notation "σ"=> Rubric.Marble K W A.Zumba (A.coast_b true) (A.coast_b false)
local notation "mK"=> ruler K.B
local notation "β"=> A.Broad
-- center ingredients for final. full expression always gauge-invariant. 
namespace Sermon
variable (s:Finset A.Lot)(b:Bool)
local notation "λₖ" s:max b:max=> Liturgy A K e F s b
abbrev luxury (V:Buffered.Family K)(Z:Finset Cover) : Prop:= InTest K false Z false V ∧ Neutral K V ∧ Tower.mirror K 0 0 (Tower.mirror K 1 0 V)=-V
include e
lemma Liturgy_lux (h:Odd s.card): luxury K (λₖ s b).val (A.coast_b b):=by
 have hv:=Marble.assign (arm_scope A K e F s b _ (fun i _=> A.shore_enroll ..)); refine ⟨?_,Commission.grown _,?_⟩
 · refine (show cameo (s.card*lv_one b) (s.card*lv_one (!b))=false from ?_) ▸ hv; unfold cameo; cases b <;> simp [lv_one,Nat.not_odd_iff_even]; all_goals first| apply Even.mul_left (by decide) | grind
 rw [arm_spin,h.neg_one_pow,neg_one_smul]
-- selected cut at ruler*m. lower stencil chronology. Per-day theorem; all supports beyond given buffer. extra slab coherence.
variable (d:A.BlockDay)
omit e
local notation "δₜ" => (10:ℤ)* A.ℓ.val
def declination (d:A.BlockDay): ℤ:= (A.leftP d true-δₜ)/mK -- binder notation danger δ refers A already
local notation "Y↑" => A.yard
include e
variable (x:addgap K ≤ A.ℓ.val)
include x
lemma schedule : A.rightP d false + δₜ≤ mK*declination A K d ∧ mK*declination A K d+ δₜ≤ A.leftP d true:=by
 let k:= A.leftP d true-δₜ; have hf:= A.horizon d e; have ht:= ruler_gene K.B; have hp:= Int.emod_add_mul_ediv k (mK); have hw:= Int.emod_lt_of_pos k ht; have hv:= Int.emod_nonneg k ht.ne'; unfold k at *; have hm:mK ≤ 10*A.ℓ.val:= by unfold addgap stepgap at x; unfold ruler; omega
 unfold declination; omega
omit e x
local notation "X₁" u:max=> (s.filter (fun i=>i.1< u)) -- earlier all earlier
local notation "X₂" u:max=> (s.filter fun i=>i.1≤ u) -- broader: creators included layer. 
local notation "Y₁" u:max=> (s.filter fun i=> ¬i.1 < u)
local notation "Y₂" u:max=> (s.filter fun i=> ¬i.1 ≤ u)
def regCard := (s.filter fun x=>x.1=d).card
noncomputable def stagD := (λₖ (X₁ d) true) * (λₖ (X₂ d) false) -- fix notation
noncomputable def stagU:= (λₖ (Y₁ d) true) * (λₖ (Y₂ d) false)
local notation "X'"=> mK*declination A K d
def toyL := A.Broad.filter fun w=> w 3+δₜ ≤ X'
def toyR:= A.Broad.filter fun w=> X'+δₜ ≤ w 3
#print stagD
local notation "f₀"=> stagD A K e F s d
local notation "g"=> stagU A K e F s d
#print Finset.card_filter_add_card_filter_not
local notation "P₀"=> toyL A K d
local notation "P₁"=> toyR A K d
include e x
lemma stall_left {w:A.BlockDay} (b:Bool) (h:if b then w<d else w≤d): A.yard w b ⊆ P₀:=by
 intro t k; refine mem_filter.mpr ⟨A.Core_subset ((A.yard_core w b e) k),?_⟩; have hz:= schedule A K e d x; have hv:=((A.yard_test ..).1 k).2.1
 by_cases p:w<d; · have ht:= A.yards_progress e p b false; have hq:= A.slope_mid d false; omega
 cases b
 · change w ≤ d at h; have hp:w=d:= le_antisymm h (le_of_not_gt p); subst w; omega
 exact False.elim (p h)
lemma stall_right {w:A.BlockDay}(b:Bool)(h:¬ (if b then w<d else w≤d)): A.yard w b ⊆ P₁:=by
 intro t k; refine mem_filter.mpr ⟨A.Core_subset ((A.yard_core w b e) k),?_⟩; have hz:= schedule A K e d x; have hv:=((A.yard_test ..).1 k).1
 by_cases p:d<w; · have ht:= A.yards_progress e p true b; have hq:= A.slope_mid d true; omega
 cases b; exact False.elim (h (le_of_not_gt p)); change ¬ w<d at h; have hp:d=w:= le_antisymm (le_of_not_gt h) (le_of_not_gt p); subst d; omega
omit x e
lemma orderedCount(p:Odd (regCard A s d)) : Odd ((X₁ d).card + (X₂ d).card)∧ Odd ((Y₁ d).card+(Y₂ d).card):=by
 let G:=(s.filter fun i=>i.1=d)
 have h:(X₂ d)= X₁ d ∪ G:=by ext; simp only [mem_filter,mem_union,G]; constructor; rintro ⟨p,h⟩; exact (lt_or_eq_of_le h).elim (fun q=> Or.inl ⟨p,q⟩) (fun x=>Or.inr ⟨p,x⟩); rintro (p|p); exact ⟨p.1,p.2.le⟩; exact ⟨p.1,p.2.le⟩
 have hu:Disjoint (X₁ d) G:= disjoint_left.mpr fun x v w=> ne_of_lt ((mem_filter.mp v).2) ((mem_filter.mp w).2)
 have hn:(X₁ d).card+(Y₁ d).card=s.card:= card_filter_add_card_filter_not ..
 have hf:(X₂ d).card+(Y₂ d).card=s.card:= card_filter_add_card_filter_not ..
 rw [h,card_union_of_disjoint hu] at hf ⊢; change Odd G.card at p; rw [Nat.odd_iff] at p ⊢ -- goal AND rw hits both?
 rw [Nat.odd_iff]; omega
lemma pension (p : Odd s.card) : ∃ d:A.BlockDay, Odd (regCard A s d):=by
 let G(i:A.BlockDay):= regCard A s i; have hx:s.card=∑ i,G i:=Finset.card_eq_sum_card_fiberwise (f:=fun i:A.Lot=>i.1) (t:=univ) (fun i _=>mem_univ _)
 rw [hx] at p; by_contra! e; apply (Nat.not_even_iff_odd.mpr p); refine Finset.even_sum _ (fun i _=> ?_); exact Nat.not_odd_iff_even.mp (e i)
include e
lemma culmination : embrace A K e F s = f₀*g:=by
 rw [merge,stagD,stagU,mul_mul_mul_comm]; congr 1; all_goals unfold Liturgy; exact (prod_filter_mul_prod_filter_not ..).symm
private lemma shadowed (U T:Finset A.Lot) (X:Finset Cover) (p:∀ i∈ U,A.yard i.1 true ⊆ X)(q: ∀ i∈ T,A.yard i.1 false ⊆ X) (h:Odd (U.card+T.card)) :
    let v:=(λₖ U true)*(λₖ T false); v.val∈ σ X (10*U.card) (10*T.card) U.card ∧ luxury K v.val X:=by
 intro v; have ht:= Marble.grip (arm_scope A K e F _ _ _ p) (arm_scope A K e F _ _ _ q); simp only [lv_one,Bool.not_true,Bool.not_false,priorityR,Bool.false_eq_true,ite_false,ite_true,mul_comm _ (10:ℕ),mul_zero,mul_one,zero_add,add_zero] at ht -- simp potential perm lemma
 have hx:( (λₖ U true)*(λₖ T false)).val ∈ σ X (10*U.card) (10*T.card) U.card:= ht
 have hw:= Marble.assign hx; rw [show cameo (10*U.card) (10*T.card)=false from (by unfold cameo; simp [←mul_add]; exact Even.mul_right (by decide) _)] at hw; refine ⟨hx,hw,Commission.grown v,?_⟩
 unfold v; rw [Subalgebra.coe_mul,Tower.mirror_times,Tower.mirror_times,arm_spin,arm_spin,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul,←pow_add,h.neg_one_pow,neg_one_smul]
include x
local notation "K₀"=> luxury K
def stage_ready : Prop:= Odd (regCard A s d) -- remove e x include issues? remove
lemma seaWay (p:Odd (regCard A s d)): (f₀).val∈ σ (P₀) (10*(X₁ d).card) (10*(X₂ d).card) (X₁ d).card ∧ (g).val∈ σ (P₁) (10*(Y₁ d).card) (10*(Y₂ d).card) (Y₁ d).card ∧ luxury K (f₀).val (P₀) ∧ luxury K (g).val (P₁):= by
 have he:=orderedCount A s d p; have h₁:= shadowed A K e F (X₁ d) (X₂ d) (P₀) (fun i h=> stall_left A K e d x _ (by exact (mem_filter.mp h).2)) (fun i h=> stall_left A K e d x _ (by exact (mem_filter.mp h).2)) he.1
 have h₂:= shadowed A K e F (Y₁ d) (Y₂ d) (P₁) (fun i h=> stall_right A K e d x _ (by exact (mem_filter.mp h).2)) (fun i h=> stall_right A K e d x _ (by exact (mem_filter.mp h).2)) he.2
 exact ⟨h₁.1,h₂.1,h₁.2,h₂.2⟩
end Sermon
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Sermon
#print axioms schedule
#print axioms pension
#print axioms culmination
#print axioms seaWay
