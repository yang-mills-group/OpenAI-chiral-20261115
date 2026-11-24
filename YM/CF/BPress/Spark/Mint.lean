import YM.CF.BPress.Spark.Foliage
import YM.CF.BPress.Vesper.Forges
/-! actual Press/Dark family sup simultaneously at all **non-lifted** fields. meas/local including flags conventions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger Pine MeasureTheory Pastry Tulip Skye Girt Scree Cube Lat Fock Vesper
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff Real ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{e a h q v:ℝ}{F:Scree.GramM N}{g:ℂ}
def post0 (i: LocB N):= i.2.val.1
def post1(i:Force N):= i.val.1.val.1
lemma post0_ok(i:LocB N):post0 i ∈ earth i:=i.2.property
lemma post1_ok(i:Force N):post1 i∈ Vesper.harbor i:=i.val.1.property
abbrev Token (I:Type)(N:Side) := I → Finset (Dwell N)→ℝ
variable (u:Pane N)(W:Orbit N)
lemma vig_reg {P:BudgetPoint}{K:Hub N}{A:InkD N}(H:PressB P K A h v)(w:Finset (Dwell N)): ‖crumb (numbE P.threshold (kin K) A u).val w‖≤ H.worth.choose w:=by
 obtain ⟨X,f,T⟩:= H.worth.choose_spec; unfold numbE; by_cases s:pingS P.threshold (kin K) u
 · rw [Set.indicator_of_mem (show u ∈ _ from s)]; have he:= (f _ s w).token 0 (by omega) 0 (fun i=> i.elim0); simpa only [iteratedFDeriv_zero_apply, show increment u 0=u from by simp] using he
 rw [Set.indicator_of_notMem (show u ∉ _ from s),show crumb _ _=0 from rfl,norm_zero]; exact X w
lemma vig_fuel {P:BudgetPoint}{K:Force N}{A:Copy N}(H:ForceB P K A h v)(w:Finset (Dwell N)): ‖crumb (Scree.clamp P K A W).val w‖≤ H.costP.choose w:=by
 obtain ⟨X,f,T⟩:=H.costP.choose_spec; unfold Scree.clamp; split; next k=> have he:= (f _ k w).token 0 (by omega) 0 (fun i=> i.elim0); simpa only [iteratedFDeriv_zero_apply,Girt.openG_zero,show increment W.1 0=W.1 from by simp] using he
 rw [show crumb _ _=0 from rfl,norm_zero]; exact X w
lemma cost_token {o:Skye.Seat N}{A:Finset (Dwell N)→ℝ}{P:BudgetPoint}(g:0≤ a)(v':a≤h)(k:∀ i,0≤ A i)(v:∑ i, tariff P o h i*A i≤ e): (∑ i,A i*a^i.card) ≤ e:=by
 apply le_trans (sum_le_sum (fun i l=>?_)) v; rw [mul_comm]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ g v' _).trans (YM.CF.Graph.talp (g.trans v') i o P)) (k _)
abbrev raw_bill {I: Type}(w:Token I N)(a:ℝ)(i:I):=∑ m,w i m * a^ (Finset.card m)
variable {I:Type}[Fintype I]
structure Payer (z:I→ Site (More N))(X:I→ Support (More N))(R:Token I N)(a ε:ℝ)(B:ℕ): Prop where
 bill:∀ i j,0≤ R i j
 stake: stakeC X z (raw_bill R a) B ε
 cruise:0≤ ε
 care:∀ i,z i∈ X i
 hold:1≤ a
structure RegTag (F:GramM N)(v:Token (LocB N) N):Prop where
 price : ∀ u i m, ‖crumb (u_budget F u i).val m‖≤ v i m
 r : ∀ i, Measurable (fun u:Pane N=>u_budget F u i)
 p:∀ i:LocB N, ∃w, PressB F.p i.2 (βReg F i.1 i.2) h w -- meta!
structure FTag (F:GramM N)(v: Token (Force N) N):Prop where
 price : ∀ u i m, ‖crumb (f_budget F u i).val m‖ ≤ v i m
 r: ∀ i,Measurable (fun u:Orbit N=>f_budget F u i)
 p:∀ i, ∃w, ForceB F.p i (F.K i) h w
-- choose witnesses
variable {b r:ℝ}(Wf:YM.CF.Graph.Ledger h q q b r F)
variable (G:F.p.supportExponent=1)
include G
lemma grav {A:Support (More N)}{w:ℝ}:F.p.mass A w= Real.exp (coverNumber F.p.B A)*w:=by rw [BudgetPoint.mass,G,one_mul]
include Wf G
lemma treasure (u:1≤a)(p:0≤q)(t:a≤ h): ∃ v,Payer post0 earth v a (2*q) F.p.B∧ RegTag F v (h:=h):=by
 have he(i:Bool) : IncX (fun _=>False) (βReg F i) F.p h q:=by cases i; exact Wf.reg; exact Wf.slip
 let N0(i:LocB N):= ((he i.1).weight.choose_spec.1 i.2); let S(i:LocB N):= (he i.1).weight.choose i.2; let D(i:LocB N):= (N0 i).worth.choose
 refine ⟨D,⟨fun i=>(N0 i).worth.choose_spec.1,?_ ,by positivity, post0_ok,u⟩,fun u i=>vig_reg u (N0 i),fun i=> (Girt.flow _ _ _ (N0 i)).1,fun i=>⟨S i,N0 i⟩⟩; intro o; rw [sum_filter,Fintype.sum_prod_type]; have ht(i:Bool): (∑ j:Hub N,if post0 (i,j)=o then Real.exp (coverNumber F.p.B (earth (i,j)))*raw_bill D a (i,j) else 0)≤ q:=by
    apply le_trans (sum_le_sum (fun j h'=>?_ )) ((he i).weight.choose_spec.2 o); by_cases v:j.val.1=o; rw [if_pos v.symm,if_pos (show post0 (i,j)=o from v),grav G]; exact mul_le_mul_of_nonneg_left (cost_token (zero_le_one.trans u) t ((N0 (i,j)).worth.choose_spec.1) ((N0 (i,j)).worth.choose_spec.2.2)) (Real.exp_pos _).le; rw [if_neg (show post0 (i,j)≠o from v),if_neg (Ne.symm v)]
 rw [Fintype.sum_bool]; exact (add_le_add (ht true) (ht false)).trans_eq (two_mul q).symm -- tune choose `.meas`
lemma gems (u:1≤a)(p:0≤q)(t:a≤h): ∃v,Payer post1 harbor v a q F.p.B ∧ FTag F v (h:=h):=by
 let H:= Wf.force; let K:= H.weight.choose; let M:= H.weight.choose_spec; let P:= M.1; let S(i):= (P i).costP.choose; have ht(i: Force N): raw_bill S a i≤K i:= cost_token (zero_le_one.trans u) t ((P ..).costP.choose_spec.1) ((P ..).costP.choose_spec.2.2)
 have he(i:Force N) :0≤ raw_bill S a i:=sum_nonneg fun m _=> mul_nonneg ((P i).costP.choose_spec.1 _) (pow_nonneg (zero_le_one.trans u) _)
 refine ⟨S,⟨fun i=>(P i).costP.choose_spec.1, ?_,p,post1_ok, u⟩,fun v i=>vig_fuel v (P i),fun i=>(tokM _ _ _ (P i)).1, fun i=>⟨_,P i⟩⟩; intro i; rw [sum_filter]; apply le_trans (sum_le_sum (fun j _=>?_)) (M.2 i); split; next l=> rw [← l, if_pos (post1_ok j),grav G]; exact mul_le_mul_of_nonneg_left (ht j) (Real.exp_pos _).le
 next l=> split; exact (he j).trans ((ht j).trans (F.p.loMass _ _ ((he j).trans (ht j)))); exact le_rfl
end YM.CF.BPress.Spark
