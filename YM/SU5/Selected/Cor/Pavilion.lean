import YM.SU5.Selected.Cor.Penman
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
local notation "V₀"=> A.Broad
local notation "L"=> A.Lot
--local notation "m₀" => Marble K W A.Zumba (A.coast_b true) (A.coast_b false) -- W not scoped yet, remove
local notation "Φ" => Prize K (V₀)
variable {W:Window.Family}(F:Sermon A K W)
local notation "η"=> Marble K W A.Zumba (A.coast_b true) (A.coast_b false)
--local notation "io" W:max=> F.arm A W
local notation "Fπ"=> F.summit A K e
-- need charge & separate and R. define `Pend` function λ on arms and views filter, then split succinctly. Realization gall.
variable (s:Finset A.Lot)
include e
namespace Sermon
noncomputable def Liturgy (b:Bool): Φ:= ∏ i∈s, (F.arm A b i K e)
noncomputable def embrace : Φ:= ∏ i∈ s, (F.summit A K e i)
local notation "μ" s:max b:max => Liturgy A K e F s b
lemma arm_scope (b:Bool)(X:Finset Cover)(h:∀ i∈s,A.yard i.1 b⊆X): (μ s b).val ∈ η X (s.card*lv_one b) (s.card*(lv_one (!b))) (s.card*priorityR b):=by
 induction s using Finset.induction_on with
 |empty=> rw [Liturgy,prod_empty,card_empty,zero_mul,zero_mul,zero_mul]; exact Marble.pure .polo
 | insert i s hi Hp=>
    let g:= Marble.wider (F.tone b i) (h i (mem_insert_self ..)); have hg:= Marble.grip g (Hp (fun j u=>h j (mem_insert_of_mem u))); -- note `let g; reducible?`
    rw [Liturgy,prod_insert hi, card_insert_of_notMem hi,add_mul,add_mul,add_mul,one_mul,one_mul,one_mul,add_comm _ (lv_one b),add_comm _ (lv_one (!b)),add_comm _ (priorityR b)]; exact hg
-- arms signs. uniform center both across `$Sol`. 
omit e in
private abbrev speed(F:Buffered.Family K):= Tower.mirror K 0 0 (Tower.mirror K 1 0 F) -- include e maybe A inadvertently? abbreviation includes e?
#print speed
lemma arm_spin (b:Bool): Tower.mirror K 0 0 (Tower.mirror K 1 0 ((μ s b).val))= (-1:ℂ)^s.card • (μ s b).val := by
 induction s using Finset.induction_on with
 | empty=> change speed K 1=_ • 1; unfold speed; rw [Tower.mirror_unit,Tower.mirror_unit,card_empty,pow_zero,one_smul]
 | insert i s hi h=>
    rw [Liturgy,prod_insert hi, Subalgebra.coe_mul]; rw [Tower.mirror_times,Tower.mirror_times,card_insert_of_notMem hi]; change speed K (lamp F b i)* speed K (μ s b).val=_; change speed K (μ s b).val=_ at h
    rw [h,show speed K (lamp F b i)= _ from admire F b i]; change -(lamp F b i)* _=(-1:ℂ)^(s.card+1) • (lamp F b i*(μ s b).val); rw [pow_succ,mul_neg_one,neg_smul,neg_mul,Algebra.mul_smul_comm] -- `SetLike`
-- package blood for law.
lemma merge : embrace A K e F s = (μ s true)*(μ s false):= by unfold embrace summit Liturgy; rw [prod_mul_distrib]
local notation "U" s:max=> (embrace A K e F s)
lemma knot_s : (U s).val∈ (η V₀) (10*s.card) (10*s.card) s.card:=by
 have hx(b:Bool):=(arm_scope A K e F s b (A.Broad) (fun i u=>subset_trans (A.yard_core i.1 b e) A.Core_subset)); have ht:= Marble.grip (hx true) (hx false); rw [merge, Subalgebra.coe_mul]; change _∈_; simpa only [lv_one,priorityR,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_true,ite_false,mul_zero,mul_one,add_zero,zero_add,mul_comm s.card 10] using ht
-- commune charter votes linear Lem.
omit e in
def jetAccount (x:ℕ): Finset (Finset L):= (Finset.univ: Finset L).powersetCard (load x)
local notation "Uπ"=> F.solitude A K e
omit e -- F not included? `omit` not included. Goal margin independent W.
local notation "β"=> Stencil.label (Finset.univ: Finset L).card A.vowP
noncomputable def hazardS (A:Mezz):ℝ:= 1+∑ i∈range A.vowP, ‖Stencil.label (Fintype.card A.Lot) A.vowP i‖*((jetAccount A i).card:ℝ) -- parameter order
noncomputable def honey (A:Mezz):ℝ:= ( (1:ℝ)/2)/(hazardS A)
lemma honey_fee (A:Mezz): 0< honey A:= by unfold honey hazardS; positivity
include e
variable {T:Buffered.Family K→ℂ} (h: Scopes K A.Broad T)
--local notation "β'"=> linearMap -- remove
omit e in
noncomputable def transit : Φ →ₗ[ℂ] ℂ where
  toFun x:= T x.val
  map_add' x y:= h.plus_v x.val y.val (blush x).widen (blush y).widen
  map_smul' x y:= h.scale y.val (blush y).widen x
local notation "φ"=> transit A K h
include h
lemma freight : 1-T (Uπ).val= ∑ i∈range A.vowP, β i • ∑ s∈jetAccount A i,T (U s).val:=by unfold solitude Stencil.ballet; change (1:ℂ) -φ (1-∑ i∈ _,_) = ∑ i∈range A.vowP,β i • ∑ s∈ _,φ (U s); rw [map_sub]; simp only [map_sum,map_smul]; rw [show φ 1=1 from h.unit]; abel_nf; rfl -- tune ring_nf unknown issue, abel
lemma earn_honey (v:‖T (Uπ).val‖< 1/2): ∃ (r:ℕ) (T':Finset A.Lot), r< A.vowP ∧ T'.card=load r∧ honey A < ‖T (U T').val‖:=by
 have xv:(1/2:ℝ)< ‖(1:ℂ)-T (Uπ).val‖:= lt_of_lt_of_le (show (1/2:ℝ) < ‖(1:ℂ)‖ - ‖T (Uπ).val‖ by rw [norm_one]; linarith only [v]) (norm_sub_norm_le ..)
 rw [freight A K e F h] at xv
 by_contra! p; let g:= honey A; let t:=∑ i∈range A.vowP, ‖β i‖*((jetAccount A i).card:ℝ); have ht:hazardS A=1+t:=by unfold hazardS t; rw [card_univ]
 have he(i:ℕ)(q:i∈ range A.vowP): ‖β i • ∑ s∈ jetAccount A i,T (U s).val‖ ≤ (‖β i‖ *((jetAccount A i).card:ℝ))* g:=by rw [norm_smul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); refine (norm_sum_le ..).trans ((sum_le_sum (fun j u=>(show ‖T (U j).val‖ ≤ g from p i j (mem_range.mp q) ((mem_powersetCard.mp (show j ∈ jetAccount A i from u)).2)))).trans_eq ?_); rw [sum_const, nsmul_eq_mul]
 have hg:= xv.trans_le ((norm_sum_le ..).trans (sum_le_sum (s:=range A.vowP) (f:=fun i=> ‖β i • ∑ s∈ jetAccount A i,T (U s).val‖) he)); rw [←Finset.sum_mul] at hg; have h':0 < hazardS A:= by have hV:0≤t:= sum_nonneg (fun i _=> by positivity); rw [ht]; linarith only [hV]
 have hx:hazardS A*g=(1/2:ℝ):= by unfold g honey; rw [mul_comm]; exact div_mul_cancel₀ _ h'.ne'
 have p':0<g:=honey_fee A; change _< t*g at hg; rw [ht,add_mul,one_mul] at hx; linarith only [hg,p',show _=_ from hx] -- lin not linear after addition; ring_nf or nlinarith
lemma signal (v:‖T (Uπ).val‖< 1/2): ∃ (r:ℕ)(s:Finset A.Lot), r< A.vowP ∧ s.card=load r ∧
    honey A< ‖T (U s).val‖ ∧ ¬ Challenged K W A.Zumba (A.coast_b true) (A.coast_b false) A.Broad (10*s.card) (10*s.card) s.card T:=by
 obtain ⟨r,s,h',p,x⟩:= earn_honey A K e F h v; refine ⟨r,s,h',p,x,fun q=> norm_pos_iff.mp ((honey_fee A).trans x) (promises h (by unfold cameo; simp) (by rw [p]; unfold Stencil.load; omega) (knot_s A K e F s) q)⟩ -- placeholder
end Sermon
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Sermon
#print axioms arm_spin
#print axioms knot_s
#print axioms signal
