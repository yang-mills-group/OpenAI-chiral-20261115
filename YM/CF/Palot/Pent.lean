import YM.CF.Palot.Sparkle
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
variable {A I E:Type*}[Fintype A][DecidableEq A][Fintype I][DecidableEq I][CommSemiring E]
variable {n:Side}
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Trees
local notation "bay"=>Stilo.bay
variable {J:Type*}[Fintype J][DecidableEq J]
def invoiceB(B:ℕ)(a:ℝ)(y: Site n)(X:Track (Crowd (Site n)) ℝ):= ∑ i:leaf (Site n), if y∈ i.val then X (beamH i.val)*currency B a i.val else 0
lemma turn_q (X:I→ Support n)(w:I→ℝ)(h:∀ i,0≤w i)(B:ℕ)(a:ℝ)(z:Site n)(P:Finset I):0 ≤ touches X B w a z P:=by
 unfold touches; split
 ·  exact prod_nonneg fun i _=> mul_nonneg (h i) (Real.exp_pos _).le
 ·  exact le_rfl
lemma crownM (h:J→I)(X:J→ Support n)(v:∀ i,(X i).Nonempty)(F:J→ℝ)(w:∀ i,0≤F i)(P: Finset I)(z:Site n)(B:ℕ)(a:ℝ)(p:0≤a): invoiceB B a z (turnY h P X F) ≤ ∑ i∈ ticketSet h P,touches X B F a z i:=by
 unfold invoiceB turnY; rw [show (∑ i:leaf (Site n),_) = ∑ i:leaf (Site n) with z∈ i.val,(∑ j∈ticketSet h P, (Pi.single (rhythm X j) (∏ l∈ j,F l):Track (Crowd (Site n)) ℝ) (beamH i.val)*currency B a i.val) from ?_]; swap; · simp [sum_filter,Finset.sum_apply,sum_mul]
 rw [sum_comm]; apply sum_le_sum; intro i t; by_cases hp: ∃ j:leaf (Site n),z∈j.val∧ rhythm X i=beamH j.val
 · obtain ⟨m,g,f⟩:=hp; obtain ⟨u,l⟩:=break_h X v m i f; rw [sum_eq_single m, f,Pi.single_eq_same,touches,if_pos ⟨u,l.symm ▸ g⟩,prod_mul_distrib]
   · unfold Trees.currency; rw [←Real.exp_sum, ←Finset.mul_sum, ←l]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ p)) (prod_nonneg fun i _=>w i); exact_mod_cast Ac.cover X B u
   · intro k _ y; rw [f,Pi.single_eq_of_ne ?_,zero_mul]; exact fun a=>y (Subtype.ext ((bay_beam _).symm.trans ((congrArg Stilo.bay a).trans (bay_beam _))))
   simp [g]
 rw [sum_eq_zero]; exact turn_q _ _ w B a z i
 intro j p; rw [Pi.single_eq_of_ne (fun f=>hp ⟨j,(mem_filter.mp p).2,f.symm⟩),zero_mul]
def outC (c:ℕ)(P:Finset I):Prop:= c≤P.card-1
lemma promote (h:J→I)(X:J→ Support n)(F:J→ℝ)(H:Finset J→ℝ)(g:∀ i,0≤H i)(c:ℕ):∑ i:Finset I with outC c i,∑ j∈ ticketSet h i,H j≤∑ j:Finset J,if outC c j then H j else 0:=by
 let V(i):Finset I:= Finset.image h i; let N:= fun j:Finset J=> if outC c j then H j else 0; have he i:0 ≤ N i:=by unfold N; split; exact g _; exact le_rfl
 rw [←sum_fiberwise _ V]; apply (sum_le_sum (f:=fun i=>∑ j ∈ ticketSet h i,H j) (g:=fun i=> ∑ j:Finset J with V j=i,N j) (s:= univ.filter (outC c)) ?_).trans; swap
 · intro i g; rw [sum_congr rfl (fun j (p:j∈ticketSet h i)=> show H j=N j from (if_pos (show outC c j from (by unfold outC; rw [turn_card h i j p]; exact (mem_filter.mp g).2))).symm)]; exact sum_le_sum_of_subset_of_nonneg (fun k p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.2⟩) fun i _ _=> he _
 exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun i _ _=> sum_nonneg fun i _=> he i
lemma awaken (h:J→I)(X:J→ Support n)(F:J→ℝ)(v:∀ i,(X i).Nonempty)(B:ℕ)(a γ δ q:ℝ)(p:0≤a)(H:Ready X B F a γ δ q)(m:ℕ)(z:Site n):∑ i:Finset I with outC m i, invoiceB B a z (turnY h i X F)≤ γ*q^m*(1-q)⁻¹:=by
 have he := touch_tail X B H z m; have hp:= H.2.2.2.2.1
 exact le_trans ((sum_le_sum fun i _=> crownM h X v F hp _ z B a p).trans (promote h X F (touches X B F a z) (turn_q _ _ hp B a z) m)) (by apply le_trans ?_ (budget_sum he univ); apply sum_le_sum; intro i _; split_ifs with f p p; exact le_rfl; exact False.elim (p f); exact False.elim (f p); exact le_rfl)
-- attachable majorant representation: no decorations beyond distinct choices after ℓ convolution
lemma erupt(h:J→I)(X:J→Finset A)(F:J→ℝ)(W:List I)(v:W.Nodup): payH (tea h X F) W=turnY h W.toFinset X F:=by
 induction W with| nil=> rw [List.toFinset_nil, turn_empty]; rfl| cons i W ih=> rw [List.toFinset_cons,turn_next h i X F W.toFinset (by simpa using (List.nodup_cons.mp v).1),← ih (List.nodup_cons.mp v).2]; rfl
end YM.CF.Palot
