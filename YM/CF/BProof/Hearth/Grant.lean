import YM.CF.BProof.Hearth.Pivot
/-! Costs of near and far comparisons with model fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{d c a b l r ρ:ℝ} {P:Ready j a b l r}{F:Core j a b l r N}(h:Age P F d)
variable {S:Support N} {U: Streak N} (A:IsStarProjection (F.θ U 1))
include A
lemma empty_board (hc:0<c)(e:c≤1) : BoardH F U ∅ c:=by
 have ht(u:Bool) : bandCut (∅:Support N) u=0:=by unfold bandCut bandSites cutM; simp
 unfold BoardH; rw [ht,ht]; refine ⟨A,IsStarProjection.zero ..,IsStarProjection.zero ..,by simp,by simp,by simp,hc,e⟩ -- tune
lemma onEmpty(u:ℝ): PitH F U ∅ u=F.θ U 1:= by
 have ht(u:Bool) : bandCut (∅:Support N) u=0:=by unfold bandCut bandSites cutM; simp
 unfold PitH; rw [ht,ht]; let S:=F.θ U 1; have he:house S 0 0 u=S:=by simp [house,wedgeP,wedgeQ,land,space]; -- tune
 rw [floorH,he,land,send,entered, A.isSelfAdjoint,A.isIdempotentElem,add_sub_cancel,inv_one,one_mul,A.isIdempotentElem] -- tune
lemma plaza (Q: Quilt N)(p: ‖F.θ U 1* pair Q-pair Q*cc (F.θ U 1)‖≤ρ) (u:ℝ): ‖gapE F U ∅ Q u‖≤ρ:=by
 rw [gapE,onEmpty A]; let V:=F.θ U 1; let B:=pair Q; change ‖(1-V)*B*cc V‖≤_; rw [show (1-V)*B* cc V=(1-V)*( B*cc V-V*B) from (by rw [mul_sub,←mul_assoc (1-V) V,qrComplement A,zero_mul,sub_zero,mul_assoc (1-V)])]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (A.one_sub.norm_le _)).trans ((norm_sub_rev ..).trans_le p))

omit A
abbrev Scope (F:Core j a b l r N)(d c: ℝ):= InRoad F d c × HScope N 3
def funding (a:ℝ)(k:ℕ) :ℝ:=16*((k:ℝ)+1)^4*(4/|a|+1)
lemma funding_pos(a:ℝ)(k:ℕ):0<funding a k:=by unfold funding; positivity
abbrev bille (F:Core j a b l r N){d c:ℝ} (u:ℝ)(x:Scope F d c):=gapE F x.1.val.1.val x.1.val.2 x.2.val u
def shop(h:Age P F d)(c:ℝ):= HScope.palette (h.beam c) 3
lemma fees (x y:Scope F d c)(o:Site (More N)){w k:ℕ}{ε:ℝ}(q:0≤ε)
    (e:∀ i∈bay (terr (More N)) o (w+k), i∈spot x.1.val.2 ↔ i∈spot y.1.val.2) (u:∀ i∈leaks (bay (terr (More N)) o (w+k)), scenery (x.1.val.1.val i) (y.1.val.1.val i) ≤ ε)
    (f:∀ i∈ bay (terr (More N)) o (w+k), ‖x.2.val i-y.2.val i‖≤ε) (i:Site (More N))(p:i∈bay (terr (More N)) o w):let b:= (shop h c).st; b.eval (bay b.F i k) x y≤ funding P.hT k * ε :=by
 let S:= bay (terr (More N)) i k; have ht:= coverBay (r:=k) p; let X:= (x.1.val.1).val; let Y:= (y.1.val.1).val; intro b; change ((fa X Y S)/ |P.hT|+ (∑ j∈ S,dots j x.1.val.2 y.1.val.2))+(∑ j∈S, ‖x.2.val j-y.2.val j‖) ≤ _; rw [sum_eq_zero (fun j hx=> show dots .. =0 from if_pos (e j (ht hx))),add_zero]
 apply (add_le_add (div_le_div_of_nonneg_right (fa_bay q (fun i hi=> u i (leaks_up ht hi))) (abs_nonneg _)) ((sum_le_sum (fun z (hz:z∈S)=> f z (ht hz))).trans ?_)).trans_eq (show (16*((k:ℝ)+1)^4*4*ε)/ |P.hT|+(16*((k:ℝ)+1)^4)*ε=_ from (by unfold funding; ring)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Tenant.reach ..) q
end YM.CF.BProof.Hearth
