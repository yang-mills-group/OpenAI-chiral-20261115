import YM.SU5.FiniteGaugeData.Tower.Diagram
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
# Finite-level transfer: arithmetic and separation. Put into identity form
at a host above, check via native at the true period, and `stationary_ext`
back to common supported local system. These identities, by themselves, give
no equality on different PERIODS of the charts (incl AP indices differ). Need
a price for moving transfer operators, not merely the local dual-norm bound.
See also why overlap has to track the whole input: in general no product
push property across *non-separated* boxes, even for scalars; the objects to
cohere are the linear reads. Enlarge and pass through the whole product on
the same construction there.
-/
open Fock Tree
open Next.SectorChange
section oneStep
-- linear arithmetic before casting to the tent, on arbitrary (admissible when
-- needed) step data. Singular matrices normalized via actual Kernel; no
-- arbitrary nonvanishing hypothesis needed for unital enactment but use
-- Branches and odd step.
variable {m n:Side} (G:Ratio m n)(A: StepData (More m) (More n))(j D:ℕ)(Q:Op SU.Slot)(M:Male)(o:Odd G.count.val)(q:Chi)(d β:ℝ)(l:Loom m)
local notation "σ₀"=>gathered G j Q M o q d
local notation "σ₁"=>assembled G j Q M o q d l
local notation "τ"=>pushMark G A j Q M o q d β l
lemma frozen_scale (F:Mark m)(z:ℂ)(X:Fields n)(Y:Fields m): σ₀ (z • F) X Y=z • σ₀ F X Y:=by
 unfold gathered avgF Advance.before; simp_rw [Pi.smul_apply,map_smul]; rw [← Finset.smul_sum]; exact smul_comm ..
lemma assembled_scale (F:Mark m)(z:ℂ)(X:Fields n)(V:Pane m):σ₁ (z•F) X V=z • σ₁ F X V:=by unfold assembled; simp_rw [frozen_scale,integral_smul]
lemma frozen_add (F H:Mark m)(X:Fields n)(Y:Fields m):σ₀ (F+H) X Y=σ₀ F X Y+σ₀ H X Y:=by unfold gathered avgF Advance.before; simp_rw [Pi.add_apply,map_add]; rw [sum_add_distrib,smul_add]
lemma frozen_unit (X:Fields n)(Y:Fields m):σ₀ 1 X Y=1:=by
 let v:= ratio G; haveI :Nonempty (Forest (ratio G)):= select v o
 unfold gathered Advance.before avgF; simp_rw [Pi.one_apply,sub_one]; rw [sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity)]
lemma liner_scale (F:Mark m)(z:ℂ):τ (z•F)= z • τ F:=by
 funext X; unfold pushMark linkLaw; simp_rw [assembled_scale,smul_comm _ z]; rw [integral_smul]; rfl
variable {F H:Mark m} (e: Measurable l)(a:Stencil.LaurentRadius j G.count D)(c:A.patch.Branches A.kernel SU.group)(p:0<d)(p':2*d<firstRadius SU.group)
include p p' e a
lemma assembled_plus (hf:Envelope F)(hh:Envelope H)(X:Fields n)(V:Pane m): σ₁ (F+H) X V=σ₁ F X V+σ₁ H X V:=by
 unfold assembled; simp_rw [frozen_add]
 apply integral_add
 · exact Env.integrableX (Env.along (g:=fun t:Ids m=>(X,drawn l (V,t))) (env_gathered G j Q M o q d a p p' _ hf) (measurable_const.prodMk ((drawn_m l e).comp (measurable_const.prodMk measurable_id)))) (depot m)
 · exact Env.integrableX (Env.along (g:=fun t:Ids m=>(X,drawn l (V,t))) (env_gathered G j Q M o q d a p p' _ hh) (measurable_const.prodMk ((drawn_m l e).comp (measurable_const.prodMk measurable_id)))) (depot m)
include c
lemma liner_plus (hf:Envelope F)(hh:Envelope H): τ (F+H)=τ F+τ H:=by
 funext X; unfold pushMark linkLaw; simp_rw [assembled_plus G j D Q M o q d l e a p p' hf hh,smul_add]; rw [Pi.add_apply]
 apply integral_add
 · exact Env.integrableX (Env.scale (slice_env A β c X.1) (env_fixed G j Q M o q d l a e p p' F hf X)) _
 exact Env.integrableX (Env.scale (slice_env A β c X.1) (env_fixed G j Q M o q d l a e p p' H hh X)) _
omit e p p' a
lemma liner_unit:τ (1:Mark m)=1:=by
 funext X; unfold pushMark linkLaw assembled; simp_rw [frozen_unit]; simp_rw [integral_const,probReal_univ,one_smul,integral_smul_const,(A.isKernel c β).total,one_smul]; rfl
end oneStep
section payment
variable (κ n:ℕ)
variable (p:legalAt Y s κ n)
local notation "ω" F:max=> distribute Y H s κ F
local notation "T" F:max=> aboveD Y H s κ n F
lemma above_scale (F:Family (tent Y H))(z:ℂ): T (z • F)=z • (T F):=by
 unfold aboveD; rw [(distribute_arith Y H s κ F F z).2.2.1]; exact liner_scale .. -- .. overextends
include p
lemma above_parts {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(y:InTest K true S false G):T (F+G)= (T F)+(T G):=by
 let t:= (fullness Y κ n p.1).cap_grant
 obtain ⟨b⟩:=t.grant s p.2
 unfold aboveD; rw [(distribute_arith Y H s κ F G 0).1]; unfold nextMark
 exact liner_plus _ _ _ (aliasLaw Λ) _ _ Λ.R.odd_side _ _ _ _ ((Y.voyage κ).ownership s).paid.bill (Journey.legal Λ) (t.branch s p.2) b.legal.1 b.legal.2 (stationed Y H s S κ x).env (stationed Y H s S κ y).env
lemma above_unit:T 1=1:=by
 unfold aboveD; rw [(distribute_arith Y H s κ 1 1 0).2.2.2.1]; unfold nextMark; exact liner_unit _ _ _ _ _ _ _ _ _ _ ((fullness Y κ n p.1).cap_grant.branch s p.2)
lemma above_sum {X:Type*}(D:Finset X)(F:X→Family (tent Y H)){S:Finset Cover}(x:∀ i∈D,InTest K true S false (F i)): T (∑ i∈D,F i)=∑ i∈D,T (F i):=by
 induction D using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty]; simpa only [zero_smul] using above_scale Y H s κ n 1 (0:ℂ)
 | insert i D hp ih=> have hw(j)(h:j∈D):=x j (mem_insert_of_mem h); rw [sum_insert hp,sum_insert hp, above_parts Y H s κ n p (x i (mem_insert_self ..)) (InTest.sum _ _ hw), ih hw]
local notation "W" S:max=> wingspan Λ l S
-- Congruences at same support host; no case split on Tivoli in consumers.
lemma block_parts {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(y:InTest K true S false G): block Y H s κ n S (F+G)=block Y H s κ n S F+ block Y H s κ n S G:=by
 by_cases h:Tivoli (W S) ((K).c (momentm Y κ (s+1))); swap; · simp only [block,distribute_back,h, dite_false,ite_self,add_zero]
 let P:=block Y H s κ n S
 apply stationary_ext Y H (s+1) (W S) κ h.hosp (booked Y H s κ n S _) ((booked Y H s κ n S F).add (booked Y H s κ n S G))
 rw [(distribute_arith Y H (s+1) κ (P F) (P G) 0).1,reserved Y H s _ _ _ p x h,reserved Y H s _ _ _ p y h,reserved Y H s _ _ _ p (x.add y) h,above_parts Y H s κ n p x y]
lemma block_scale {F:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(z:ℂ): block Y H s κ n S (z • F)=z • block Y H s κ n S F:=by
 by_cases h:Tivoli (W S) ((K).c (momentm Y κ (s+1))); swap; · simp only [block,distribute_back,h, dite_false,ite_self,smul_zero]
 apply stationary_ext Y H (s+1) (W S) κ h.hosp (booked Y H s κ n S _) (.smul _ (booked Y H s κ n S F))
 rw [(distribute_arith Y H (s+1) κ (block Y H s κ n S F) 0 z).2.2.1] -- uses F not G
 rw [reserved Y H s _ _ _ p x h,reserved Y H s _ _ _ p (InTest.smul z x) h,above_scale]
lemma block_unit {S:Finset Cover}(v:Tivoli (W S) ((K).c (momentm Y κ (s+1)))): block Y H s κ n S 1=1:=by
 exact stationary_ext Y H (s+1) (W S) κ (v.hosp) (booked Y H s κ n S _) .one (by rw [reserved Y H s S _ _ p InTest.one v,(distribute_arith Y H (s+1) κ 0 0 0).2.2.2.1,above_unit Y H s κ n p])
omit p
lemma add_scheme {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(y:InTest K true S false G): block Y H s κ n S (F+G)=block Y H s κ n S F+ block Y H s κ n S G:=by
 by_cases p:legalAt Y s κ n; exact block_parts Y H s κ n p x y; simp [block,p]
lemma scale_scheme {F:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(z:ℂ): block Y H s κ n S (z•F)=z • block Y H s κ n S F:=by
 by_cases p:legalAt Y s κ n; exact block_scale Y H s κ n p x z; simp [block,p]
lemma sub_scheme {F G:Family (tent Y H)}{S:Finset Cover}(x:InTest K true S false F)(y:InTest K true S false G):block Y H s κ n S (F-G)=block Y H s κ n S F-block Y H s κ n S G:=by
 rw [sub_eq_add_neg,←neg_one_smul ℂ G,add_scheme Y H s κ n x (.smul _ y),scale_scheme Y H s κ n y,neg_one_smul,←sub_eq_add_neg]
lemma sum_scheme {X:Type*}{S:Finset Cover}(D:Finset X)(F:X→Family (tent Y H))(x:∀ i∈D,InTest K true S false (F i)): block Y H s κ n S (∑ i∈D,F i)=∑ i∈D,block Y H s κ n S (F i):=by
 induction D using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; simpa only [zero_smul] using scale_scheme Y H s κ n (S:=S) InTest.one (0:ℂ)
 | insert i D hp ih=> have hw(j)(h:j∈D):=x j (mem_insert_of_mem h); rw [sum_insert hp,sum_insert hp, add_scheme Y H s κ n (x i (mem_insert_self ..)) (InTest.sum _ _ hw),ih hw]
end payment
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.sum_scheme
#print axioms YM.CF.Buffered.Afterglow.Tower.block_unit
