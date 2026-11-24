import YM.SU5.Reconstruction.AllGrades.Odds
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
/-! Discount shape on previous state/witnesses ONLY. zero-price at unauthorized gates. -/
lemma distributed {b:Bool}(S:Finset Cover)(n:ℕ){F G:Family (tent Y H)}(h:Tivoli S ((tent Y H).c (momentm Y n s)))(p:InTest K true S b F)(x:InTest K true S b G)(q:distribute Y H s n F=distribute Y H s n G):F=G:=by
 refine native_determines S (tent Y H) h p x (charge_id _ q)
where charge_id{c₀ d₀:Side}(h:c₀=d₀){a b:Mark c₀}(z:ship h a=ship h b):a=b:=by subst c₀; exact z
noncomputable def torchBlock (n q:ℕ)(S:Finset Cover)(F:Family (tent Y H)):Family (tent Y H):=
 if legalAt Y s n q∧ InTest K true S true F ∧ Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y n (s+1))) then Garret.pick Y H s n q true S F else 0
variable (κ n:ℕ)
local notation "W" => wingspan Λ l
local notation "M" s:max=>((K).c (momentm Y κ s))
local notation "tK"=> torchBlock Y H s κ n
lemma tBook (S:Finset Cover)(F:Family (tent Y H)): InTest K true (W S) true (tK S F):=by
 unfold torchBlock; split
 next h=> exact (lamp_jump Y H s κ n h.1 h.2.1 h.2.2).1
 next h=> exact InTest.zero
variable (p:legalAt Y s κ n)
include p
lemma tReserve (S:Finset Cover){F:Family (tent Y H)}(h:InTest K true S true F)(e:Tivoli (W S) (M (s+1))) : distribute Y H (s+1) κ (tK S F)=aboveD Y H s κ n F:=by
 rw [torchBlock,if_pos ⟨p,h,e⟩]; exact (lamp_jump Y H s κ n p h e).2
local notation "T" F:max=> aboveD Y H s κ n F
lemma parts_odd {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(y:InTest K true S true G):T (F+G)= (T F)+(T G):=by
 let t:= (fullness Y κ n p.1).cap_grant
 obtain ⟨b⟩:=t.grant s p.2
 unfold aboveD; rw [(distribute_arith Y H s κ F G 0).1]; unfold nextMark
 exact liner_plus _ _ _ (aliasLaw Λ) _ _ Λ.R.odd_side _ _ _ _ ((Y.voyage κ).ownership s).paid.bill (Journey.legal Λ) (t.branch s p.2) b.legal.1 b.legal.2 (Garret.locates Y H s κ x).env (Garret.locates Y H s κ y).env
lemma torchBlock_parts {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(y:InTest K true S true G): torchBlock Y H s κ n S (F+G)=torchBlock Y H s κ n S F+ torchBlock Y H s κ n S G:=by
 by_cases h:Tivoli (W S) ((K).c (momentm Y κ (s+1))); swap; · simp only [torchBlock,h, and_false,false_and,ite_false,add_zero]
 let P:=torchBlock Y H s κ n S
 apply distributed Y H (s+1) (W S) κ h (tBook Y H s κ n S _) ((tBook Y H s κ n S F).add (tBook Y H s κ n S G))
 rw [(distribute_arith Y H (s+1) κ (P F) (P G) 0).1,tReserve Y H s _ _ p _ x h,tReserve Y H s _ _ p _ y h,tReserve Y H s _ _ p _ (x.add y) h,parts_odd Y H s κ n p x y]
lemma torchBlock_scale {F:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(z:ℂ): torchBlock Y H s κ n S (z • F)=z • torchBlock Y H s κ n S F:=by
 by_cases h:Tivoli (W S) ((K).c (momentm Y κ (s+1))); swap; · simp only [torchBlock,h, and_false,false_and,ite_false,smul_zero]
 apply distributed Y H (s+1) (W S) κ h (tBook Y H s κ n S _) (.smul _ (tBook Y H s κ n S F))
 rw [(distribute_arith Y H (s+1) κ (torchBlock Y H s κ n S F) 0 z).2.2.1] -- uses F not G
 rw [tReserve Y H s _ _ p _ x h,tReserve Y H s _ _ p _ (InTest.smul z x) h,above_scale]
omit p
lemma add_planGr {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(y:InTest K true S true G): torchBlock Y H s κ n S (F+G)=torchBlock Y H s κ n S F+ torchBlock Y H s κ n S G:=by
 by_cases p:legalAt Y s κ n; exact torchBlock_parts Y H s κ n p x y; simp [torchBlock,p]
lemma scale_planGr {F:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(z:ℂ): torchBlock Y H s κ n S (z•F)=z • torchBlock Y H s κ n S F:=by
 by_cases p:legalAt Y s κ n; exact torchBlock_scale Y H s κ n p x z; simp [torchBlock,p]
lemma sub_planGr {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S true F)(y:InTest K true S true G):torchBlock Y H s κ n S (F-G)=torchBlock Y H s κ n S F-torchBlock Y H s κ n S G:=by
 rw [sub_eq_add_neg,←neg_one_smul ℂ G,add_planGr Y H s κ n x (.smul _ y),scale_planGr Y H s κ n y,neg_one_smul,←sub_eq_add_neg]
lemma sum_planGr {X:Type*}{S:Finset Cover}(D:Finset X)(F:X→Family (tent Y H))(x:∀ i∈D,InTest K true S true (F i)): torchBlock Y H s κ n S (∑ i∈D,F i)=∑ i∈D,torchBlock Y H s κ n S (F i):=by
 induction D using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; simpa only [zero_smul] using scale_planGr Y H s κ n (S:=S) InTest.zero (0:ℂ)
 | insert i D hp ih=> have hw(j)(h:j∈D):=x j (mem_insert_of_mem h); rw [sum_insert hp,sum_insert hp, add_planGr Y H s κ n (x i (mem_insert_self ..)) (InTest.sum _ _ hw),ih hw]
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.sum_planGr
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.tReserve
