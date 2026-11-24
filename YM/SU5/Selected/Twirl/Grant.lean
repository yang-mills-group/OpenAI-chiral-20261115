import YM.SU5.Selected.Cor.Pent
import YM.SU5.Selected.Twirl.Pearl
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
namespace Grant
open Sermon Tower.SlabMark
variable {d:ℕ}(A:Mezz)(K:Calibration){W:Window.Family} (F F': Sermon A K W) (e:A.Legate) (r:ℕ) 
local notation "Nu"=> A.G.val*A.q.val
local notation "P₀" z:max=> A.coast_b z
local notation "S₀" => A.Broad
variable {t:Buffered.Family K → ℂ}

-- mixed families chronology. pay no size cap comparisons on these variants; Eχ available; telescope costs. at later d remains F, replacement at <$x$ width. sign negative stripped on true.
noncomputable def strip (i:Bool) (a:ℂ) (f:Buffered.Family K):= if i then a • f else f
def scaleS (a:Bool→ℂ)(F:Sermon A K W): Sermon A K W where
 lamp b i:= a b • F.lamp b i
 neutral := fun b i => holdsC _ (F.neutral b i)
 tone:= fun b i=> Submodule.smul_mem _ _ (F.tone b i)
 admire:= fun b i=>by rw [Tower.mirror_scale,Tower.mirror_scale,star_star,F.admire,smul_neg]
abbrev tint:= scaleS A K (fun b:Bool=> if b then (-1:ℂ) else 1) F'
noncomputable def stage_at (k:ℕ) : Sermon A K W := by
 let g(i:A.Lot) := if i.1.val < k then tint A K F' else F
 exact ⟨fun b i=> match b with | true => (g i).lamp true i|false=> F.lamp false i,
    fun b i=> (by cases b; exact F.tone false i; exact (g i).tone true i),fun b i=> (by cases b; exact F.neutral false i; exact (g i).neutral true i),fun b i=>(by cases b; exact F.admire false i; exact (g i).admire true i)⟩
local notation "Θ" k:max=> stage_at A K F F' k
variable (i:A.Lot)(k:ℕ)
lemma unscale_false(i:A.Lot) : (tint A K F').lamp false i= F'.lamp false i:=one_smul _ _
lemma unscale_true(i:A.Lot): (tint A K F').lamp true i= -(F'.lamp true i) := neg_one_smul _ _
lemma stateN (i:A.Lot) : (Θ k).lamp false i=F.lamp false i:=rfl
lemma stateY (i:A.Lot) : (Θ k).lamp true i=if i.1.val<k then -F'.lamp true i else F.lamp true i:= by unfold stage_at; dsimp only; split <;> simp_all [unscale_true]
lemma offDay (d:A.BlockDay)(e:i.1≠d): (Θ d.val).lamp true i=(Θ (d.val+1)).lamp true i:=by rw [stateY,stateY]; have h:i.1.val≠d.val:=fun p=> e (Fin.ext p); split_ifs <;> first|rfl|omega
variable (a: Duet K A d F F')
include a
lemma lifted_at : (Θ (i.1.val+1)).lamp true i= relocate K 3 d ((Θ i.1.val).lamp true i):=by rw [stateY, stateY]; rw [if_neg (Nat.lt_irrefl i.1.val), if_pos (by omega),a.late,neg_neg]
omit a
variable (s: Finset A.Lot)
local notation "ρ" u:max b:max=> Liturgy A K e u s b
local notation "Ω" u:max=> embrace A K e u s
include e
lemma enroll {b:Bool}(h:∀ i∈s,F.lamp b i= F'.lamp b i): ρ F b=ρ F' b:= prod_congr rfl (fun i u=>Subtype.ext (h i u))
lemma ancient_seed: Ω (Θ 0)= Ω F:=by rw [merge,merge]; exact congrArg₂ (· * ·) (enroll A K _ _ e s (by simp [stateY])) (enroll A K _ _ e s (fun i v=> stateN ..))
include a
lemma ancient_equ (v:Odd s.card): Ω (Θ Nu)= -Ω F':=by
 have h:false=false:=rfl; have p:(ρ (Θ Nu) false)=ρ F' false:= enroll _ _ _ _ e s (fun i h=>(a.dawn i).symm);
 have hu:(ρ (Θ Nu) true)= -(ρ F' true):=by
    unfold Liturgy; rw [show (fun i=> arm A true i K e (Θ Nu))=(fun i=> -arm A true i K e F') from ?_,prod_neg,v.neg_one_pow]; simp
    ext1 i; apply Subtype.ext; change (Θ Nu).lamp true i= -F'.lamp true i; rw [stateY,if_pos]; exact i.1.isLt
 rw [merge, merge,p,hu,neg_mul]


-- numerical ledger: room margins δ insensitive to volume/cut growth. fixed s positive λ lower to stage difference.

noncomputable def portion(A:Mezz):ℝ:= honey A/ (A.G.val*A.q.val:ℕ) -- watch implicit eta
omit a e in
lemma fortune : 0< portion A:= by unfold portion; have h:0< A.G.val*A.q.val:= Nat.mul_pos A.G.property A.q.property; exact div_pos (honey_fee ..) (by exact_mod_cast h)
omit a e in
private lemma spinoff {n:ℕ}(f:ℕ→ℂ)(B:ℝ)(v:0<n)(k:B< ‖f 0 - f n‖) : ∃ i:Fin n,B/(n:ℝ)< ‖f i.val-f (i.val+1)‖:=by
 by_contra! h; have hn:0<(n:ℝ):=by exact_mod_cast v
 let C:=B/(n:ℝ); have hp (i:ℕ)(v:i≤n): ‖f 0 - f i‖ ≤ (i:ℝ)*C:=by
    induction i with
    | zero=> simp
    | succ i ih=>rw [show f 0-f (i+1)= (f 0-f i)+(f i-f (i+1)) from by abel]; push_cast; apply (norm_add_le ..).trans; specialize ih (by omega); have l:C≥ ‖f i-f (i+1)‖:= h ⟨i,v⟩; linarith only [ih,l]
 exact k.not_ge ((hp n le_rfl).trans_eq (mul_div_cancel₀ _ hn.ne'))
omit a e in
private lemma total_l (x y:ℂ)(hx: ‖x‖ <1/2)(hy: ‖y‖ <1/2) : (1/2:ℝ)< ‖1-x+(1-y)‖:= by
 rw [show 1-x+(1-y)= 2-(x+y) by ring]; apply lt_of_lt_of_le _ (norm_sub_norm_le ..); rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]; linarith [norm_add_le x y]
variable (T:Buffered.Family K→ℂ)(P:Scopes K A.Broad T)
local notation "μ"=> transit A K P
local notation "L₀" s:max=> T (Sermon.solitude A K e s).val
local notation "β" => Stencil.label (Finset.univ:Finset A.Lot).card A.vowP
include P
lemma prize_day (t:‖L₀ F‖<1/2)(p:‖L₀ F'‖<1/2):∃ (v:ℕ) (s:Finset A.Lot)(i:A.BlockDay), v<A.vowP ∧ s.card=Stencil.load v∧ portion A< ‖T (embrace A K e (Θ i.val) s).val - T (embrace A K e (Θ (i.val+1)) s).val‖:=by
 obtain ⟨g,s,h,e',q⟩: ∃ (g:ℕ) (s:Finset A.Lot), g<A.vowP ∧ s.card=Stencil.load g ∧ honey A< ‖T (embrace A K e F s).val+T (embrace A K e F' s).val‖ :=by
    let f(s:Finset A.Lot) := T (embrace A K e F s).val+T (embrace A K e F' s).val; have he:(1/2:ℝ)< ‖∑ i∈range A.vowP,β i • ∑ s∈jetAccount A i,f s‖:=by
        unfold f; simp_rw [sum_add_distrib,smul_add,sum_add_distrib]; rw [←freight A K e F P,←freight A K e F' P]; exact total_l _ _ t p -- `.. t p` invalid
    by_contra! p; let g:= honey A; let t:=∑ i∈range A.vowP, ‖β i‖*((jetAccount A i).card:ℝ); have ht:hazardS A=1+t:=by unfold hazardS t; rw [card_univ]
    have he₀(i:ℕ)(q:i∈ range A.vowP): ‖β i • ∑ s∈ jetAccount A i,f s‖ ≤ (‖β i‖ *((jetAccount A i).card:ℝ))* g:=by rw [norm_smul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); refine (norm_sum_le ..).trans ((sum_le_sum (fun j u=>(show ‖f j‖ ≤ g from p i j (mem_range.mp q) ((mem_powersetCard.mp (show j ∈ jetAccount A i from u)).2)))).trans_eq ?_); rw [sum_const, nsmul_eq_mul]
    have hg:= he.trans_le ((norm_sum_le ..).trans (sum_le_sum (s:=range A.vowP) (f:=fun i=> ‖β i • ∑ s∈ jetAccount A i,f s‖) he₀)); rw [←Finset.sum_mul] at hg; have h':0 < hazardS A:= by have hV:0≤t:= sum_nonneg (fun i _=> by positivity); rw [ht]; linarith only [hV]
    have hx:hazardS A*g=(1/2:ℝ):= by unfold g honey; rw [mul_comm]; exact div_mul_cancel₀ _ h'.ne'
    have p':0<g:=honey_fee A; change _< t*g at hg; rw [ht,add_mul,one_mul] at hx; linarith only [hg,p',show _=_ from hx]
 have hσ: Odd s.card:=⟨5*g,by rw [e']; unfold Stencil.load; omega⟩
 let f(x:ℕ):= μ (embrace A K e (Θ x) s); have h':honey A< ‖f 0-f Nu‖:= by unfold f; rw [ancient_seed,ancient_equ (a:=a) _ _ _ _ _ s hσ,map_neg,sub_neg_eq_add]; exact q
 obtain ⟨i,u⟩:= spinoff f (honey A) (Nat.mul_pos A.G.property A.q.property) h'; exact ⟨g,s,i,h,e',u⟩
end Grant
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Grant
#print axioms prize_day
#print axioms ancient_seed
#print axioms offDay
#print axioms lifted_at
#print axioms fortune
#print fortune
