import YM.SU5.Selected.Twirl.Grant
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
-- times seams at both sides of day d; true = include Xu in early segment; false= exclude Xu. W prepares. Need provenance for straddling excitation. Actually can show strict in PRIMARY rank-3 H and uncompressed phase E, not strengthen semantics of rotations. All-six pivot.
variable (A:Mezz)(K:Calibration){W:Window.Family} (F F': Sermon A K W) (e:A.Legate) (r:ℕ) (s:Finset A.Lot)(d:A.BlockDay)(b:Bool)
def wanted (v:A.BlockDay) := ((if b then v ≤ d else v<d):Prop)
instance (v:A.BlockDay) : Decidable (wanted A d b v) := by unfold wanted; infer_instance
noncomputable def pointV := s.filter fun i=> wanted A d b i.1
noncomputable def backV := s.filter fun i=> ¬wanted A d b i.1
noncomputable def fillD := s.filter fun i=> i.1=d
local notation "P" b:max=> pointV A s d b
local notation "R" b:max=> backV A s d b
local notation "Ω"=> fillD A s d
local notation "ξ" F:max u:max v:max=> Liturgy A K e F u v
local notation "η" F:max=> embrace A K e F s
local notation "V" F:max=> ξ F (Ω) true
noncomputable def pool := (ξ F (P b) true)*(ξ F (P true) false)
noncomputable def drain := (ξ F (R b) true)*(ξ F (R true) false)
local notation "Y" F:max b:max => pool A K F e s d b
local notation "N" F:max b:max => drain A K F e s d b
include e
lemma rejoin : η F = Y F b*N F b:=by rw [merge,pool,drain,mul_mul_mul_comm]; unfold Liturgy; exact congrArg₂ (·*·) (prod_filter_mul_prod_filter_not s (fun i=>wanted A d b i.1) _).symm (prod_filter_mul_prod_filter_not s (fun i=>wanted A d true i.1) _).symm -- Args tune
lemma graduatedD : Y F true= Y F false * V F:=by
 unfold pool; rw [mul_assoc (ξ F (P false) true),mul_comm (ξ F (P true) false) (ξ F (Ω) true)] -- assoc maybe need direction. fix
 rw [←mul_assoc]; congr 1; unfold Liturgy; rw [show P true=P false∪ Ω from ?_,prod_union]; · exact disjoint_left.mpr fun x t p=> ne_of_lt (show x.1<d from (mem_filter.mp t).2) ((mem_filter.mp p).2)
 ext i; simp only [pointV,fillD,mem_filter,mem_union,wanted,ite_true,Bool.false_eq_true,ite_false]; grind
lemma graduatedU : N F false= V F*N F true:=by
 unfold drain; rw [←mul_assoc]; congr 1; unfold Liturgy; rw [show R false= Ω ∪ R true from ?_,prod_union];
 · refine disjoint_left.mpr (fun x t p=> (mem_filter.mp p).2 ?_); exact show x.1≤d from ((mem_filter.mp t).2).le
 ext i; simp only [backV,wanted,fillD,mem_filter,mem_union,ite_true,Bool.false_eq_true,ite_false]; grind
local notation "A₀"=> stage_at A K F F' d.val
local notation "A₁"=> stage_at A K F F' (d.val+1)
-- V day Y(off seam F & F' variants); matched transport across shifts after accounting for charges on passed X day.
lemma pool_match : Y A₀ false=Y A₁ false:=by
 unfold pool; rw [enroll A K (A₀) (A₁) e (P false) (b:=true), enroll A K (A₀) (A₁) e (P true) (b:=false)];
 · exact fun i h=> rfl
 exact fun i h=> offDay A K F F' i d (ne_of_lt (show i.1<d from (mem_filter.mp h).2))
lemma drain_match : N A₀ true= N A₁ true:=by
 unfold drain; rw [enroll A K A₀ A₁ e (R true) (b:=true), enroll A K A₀ A₁ e (R true) (b:=false)];
 · exact fun i h=> rfl
 exact fun i h=> offDay A K F F' i d (ne_of_gt (lt_of_not_ge (show ¬ i.1≤ d from (mem_filter.mp h).2)))
variable {w:ℕ}(t: Duet K A w F F')
include t
private lemma L_match (S':Finset A.Lot)(p:∀ i∈ S',i.1=d) : relocate K 3 w ((ξ A₀ S' true).val)= (ξ A₁ S' true).val:=by
 induction S' using Finset.induction_on with
 | empty=> unfold Liturgy; rw [prod_empty,prod_empty]; exact Tower.chime_unit _ _ _
 | insert i s v h=> unfold Liturgy; specialize h (fun i vi=> p i (mem_insert_of_mem vi)); have g':= h; unfold Liturgy at h; rw [prod_insert v,prod_insert v, Subalgebra.coe_mul, Subalgebra.coe_mul, relocate_mul,h]; change relocate _ _ _ ((A₀).lamp true i)* _= (A₁).lamp true i * _; have hi:=p i (mem_insert_self i s); refine congrArg (· * (Liturgy _ _ _ _ s _).val) ?_; rw [←hi]; exact (lifted_at A K F F' i t).symm -- pattern
-- As itinerary: Headline A and B linked through one intermediate BOTH realized by moving suffix further! hence both CM+, footprints differ but *exist precisely*. intermediate may not satisfy `Marble` on the SAME coverage stencil. Not asserting. Need bound real moves. 
noncomputable def tripty (w:ℕ) := (Y F b).val * relocate K 3 w (N F b).val
local notation "Δ" F:max b:max=> tripty A K F e s d b w
lemma rounds : Δ A₀ false= Δ A₁ true:=by
 have h₁:relocate K 3 w ((V A₀).val)=(V A₁).val:= L_match A K F F' e d t _ (fun i h=>(mem_filter.mp h).2)
 unfold tripty; rw [graduatedU, graduatedD A K (A₁), pool_match,drain_match, Subalgebra.coe_mul,Subalgebra.coe_mul, relocate_mul,h₁,mul_assoc] -- specify
omit t e
-- seam geometry generous: `boundary` & `endcap` independent of s. h1= old declination. new seam after X if needed even after last day: only need integer ruler, at r≥. Δ witness both.
local notation "l₀"=> (10:ℤ)*A.ℓ.val
local notation "R₀"=> ruler K.B
noncomputable def boundaryT : ℤ:= if b then (A.rightP d true+l₀)/(R₀)+1 else Sermon.declination A K d
local notation "Y'₀" b:max=> boundaryT A K d b
local notation "dM" b:max=> R₀*boundaryT A K d b
variable (f:addgap K≤ A.ℓ.val)
include e f
lemma boundary_p : dM false+l₀≤ A.leftP d true ∧ A.rightP d false+l₀≤ dM false:= (Sermon.schedule A K e d f).symm -- tuning And.symm
lemma boundary_t : A.rightP d true+l₀≤ dM true ∧ dM true≤ A.rightP d true+l₀+ R₀:=by
 let u:= A.rightP d true + l₀; have he:= ruler_gene K.B; have hp:= Int.emod_add_mul_ediv u (R₀); have hw:= Int.emod_lt_of_pos u he; have hv:= Int.emod_nonneg u he.ne'; change u ≤ R₀*(u/R₀+1) ∧ R₀*(u/R₀+1)≤ u+R₀; rw [mul_add,mul_one]; omega
noncomputable def quarry := A.Broad.filter fun x=> x 3+l₀ ≤ dM b
noncomputable def quay := A.Broad.filter fun x=> dM b+l₀ ≤ x 3
local notation "Q₀" b:max=> quarry A K d b
local notation "Q₁" b:max=> quay A K d b
lemma withinL (v:A.BlockDay)(t:Bool)(p:wanted A d (if t then b else true) v): A.yard v t ⊆ Q₀ b:=by
 intro x h; refine mem_filter.mpr ⟨A.Core_subset ((A.yard_core v t e) h),?_⟩; have hf:= ((A.yard_test ..).1 h).2.1
 cases b
 · have hu: x∈ Sermon.toyL A K d:= stall_left A K e d f t (by cases t<;> exact p) h; exact (mem_filter.mp hu).2
 have ht:= boundary_t A K e d f; have hq:v ≤ d:= by cases t<;> exact p
 obtain rfl|g:= eq_or_ne v d
 · cases t; · have hx:= A.horizon v e; have hv:= A.slope_mid v true; omega
   omega
 have hx:= A.yards_progress e (lt_of_le_of_ne hq g) t true; have hv:=A.slope_mid d true; omega
lemma withinR (v:A.BlockDay)(t:Bool)(p:¬ wanted A d (if t then b else true) v): A.yard v t ⊆ Q₁ b:=by
 intro x h; refine mem_filter.mpr ⟨A.Core_subset ((A.yard_core v t e) h),?_⟩; have hf:= ((A.yard_test ..).1 h).1; cases b; · have hu:x∈ toyR A K d:= stall_right A K e d f t (by cases t<;> exact p) h; exact (mem_filter.mp hu).2
 have ht:= boundary_t A K e d f; have hv: d<v:= lt_of_not_ge (by cases t<;> exact p); have hv:= A.yards_progress e hv true t; have hu: R₀≤ l₀:=by unfold addgap stepgap at f; unfold ruler; omega -- tune
 omega
-- product signs eligibility, size. algebra already. Narrow. neutrality. Support money
private lemma arm_ok(W₀:Finset A.Lot)(X:Finset Cover)(pr:∀ i∈W₀,A.yard i.1 b⊆X): InTest K false X false ((ξ F W₀ b).val):=by
 induction W₀ using Finset.induction_on with
 | empty=> unfold Liturgy; rw [prod_empty]; exact InTest.one
 | insert i s h t=> unfold Liturgy; rw [prod_insert h,Subalgebra.coe_mul]; exact InTest.mul ((F.serves A b i K).mono (pr i (mem_insert_self ..))) (t (fun i p=> pr i (mem_insert_of_mem p)))
lemma quarry_x : InTest K false (Q₀ b) false (Y F b).val:= InTest.mul (arm_ok A K F e true f _ _ (fun i h=> withinL A K e d b f _ true ((mem_filter.mp h).2))) (arm_ok A K F e false f _ _ (fun i h=> withinL A K e d b f _ false ((mem_filter.mp h).2))) -- f auto include although unreferenced
lemma quay_x : InTest K false (Q₁ b) false (N F b).val:= InTest.mul (arm_ok A K F e true f _ _ (fun i h=> withinR A K e d b f _ true ((mem_filter.mp h).2))) (arm_ok A K F e false f _ _ (fun i h=> withinR A K e d b f _ false ((mem_filter.mp h).2)))
end Grant
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Grant
#print axioms rounds
#print axioms boundary_t
#print axioms quarry_x
#print axioms withinL
#print axioms withinR
