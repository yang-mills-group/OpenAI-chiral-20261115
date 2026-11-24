import YM.CF.BPress.Honey.Bakery
/-! valuation table. direct estimates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Honey.Recipe
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
variable (H:Crew A){V:GramM N} (F: Recipe (A:=A) V)(ζ a k C' D τ:ℝ)
abbrev ΩJ := H.P.jrate H.y/2
abbrev jac := H.P.jq H.y B.D
def errorCost:= |Wealth.tin F.M V.funds H.y D ζ F.C|
def leftCost := lPay B.D H.P C' H.y+rMaxV B.D (Wander (H.P.reach H.y) (6*F.M)) H.y
def columnCost(x:Seal A.Hcols):= flareJ (H.P.heightClose H.y) F.bill x
abbrev potH(S:Support (More N)):= fullWeak V.path V.p V.beta F.M S
abbrev weakBill(S:Support (More N)):= if weakFar A S then potH F S else 0
variable {H ζ k C' a D τ F}
namespace Budgeting
variable (Q:Budgeting H F τ k D ζ a C')(x:H.castP)
include Q in
lemma Jac : Ledger.Cash id (columnCost H F) (ΩJ H) (Recipe.jac H):= Q.jac.bill_long (H.P.heightClose H.y) (half_pos (H.P.gg _)).le
include Q in
lemma Jac_turf (S:Seal A.Hcols)(h:columnCost H F S≠0): Turf A S:=Q.jac.long_turf _ _ h
include Q
lemma tail : ∀ i:Seal A.Hcols, |tailY H F x.val i|≤ columnCost H F i:= fun i=> Q.jac.tail_pay (H.P.heightClose H.y) _ _
lemma fromT : Connect A (fromSea H F) (6*F.M):= ⟨fun i=> hessian_reach _ _ _ _ _ _ F.work _ Q.high, hessian_plan _ _ _ _ _ _ F.work Q.high⟩ -- tune
lemma left : ∀ i:A.Hcols, |leftY H F x.val i|≤leftCost H F C':=fun i=>(abs_add_le ..).trans (add_le_add (soft_price Q.summer Q.y_pos Q.hope Q.stride _ _ i x.property.1.2) (rMax_paid H.y Q.fromT Q.summer.seen _ (Q.poly _).tile _ i x.property.1.2)) -- tune
omit Q
lemma trips : Mission A H.y (H.skyio x.val) x.val.2.2.1 (H.port x.val):= marches ..
lemma chooser : x.val.1.1= chosen A H.κ H.y (H.skyio x.val):= (H.reserves x.val x.property).eye.symm -- tune
include Q
lemma billT : ∀ i:Root (More N), |tinW H F x.val i|≤ errorCost H F ζ D:=by -- tune
 intro i; unfold tinW; split; next b=> refine (reg_error _ _ _ F.work Q.err Q.chef Q.rung Q.cost (trips x) x.property.1.1 i ((chooser x) ▸ ?_)).trans (le_abs_self _); exact b -- eq rewriting issue
 next b=> rw [abs_zero]; exact abs_nonneg _
lemma upper_cold (i:A.Hcols)(h:i∈ x.val.1.1): cold H F x.val i ≤ -(Port.reward B.D H.κ H.y V.funds):=by
 rw [cold,if_pos h]; exact Sbill2 H.J H.P _ Q.jRoot F.M V.path V.p V.beta F.work Q.err Q.chef Q.rung Q.cost Q.reward H.F x.val.1.1 F.l F.bill x.val.2.1 x.property.2.1 Q.jac (trips x) x.property.1.1 _ h -- tune D argument
lemma rewardB : 0<Port.reward B.D H.κ H.y V.funds:=by unfold Port.reward; have he:= drift_pos H.y; positivity [Port.sever_pos H.κ Q.err.kap V.funds B.D B.D_pos]
lemma frozen(i:A.Hcols):cold H F x.val i≤0:=by by_cases u:i∈ x.val.1.1; exact (Q.upper_cold x i u).trans (neg_nonpos.mpr Q.rewardB.le); rw [cold,if_neg u]
lemma world : Thinner (s:=More N) (weakRest A V.path V.funds V.p V.beta F.M) (weakBill (A:=A) F) τ k:=by
 constructor; · intro S p; unfold weakBill; split; exact Q.toll.zero _ p; rfl
 · intro i; unfold weakRest weakBill; split; exact Q.toll.unit _; exact GEM.vac _ -- tune
 exact Q.toll.cash.subs (fun i=>ite_nonneg (Q.toll.cash.pos i) le_rfl) (fun i=>by unfold weakBill; split; rfl; exact Q.toll.cash.pos i)
lemma lucid(S) : |weak H F x.val S| ≤ weakBill (A:=A) F S := (Q.world.unit S).2 _ -- GEM.2? tune
omit Q
variable (H τ C' D ζ F)
def upperB := (Fintype.card A.Hcols:ℝ)*leftCost H F C'+(∑ i:Seal A.Hcols,columnCost H F i)+ (Fintype.card (Root (More N)):ℝ)*errorCost H F ζ D+∑ i:Support (More N),weakBill F i -- tune implicit
include Q
variable {H τ C' D ζ F}
lemma pops : Wage H F x.val ≤ upperB H F ζ C' D :=by
 have v_ (x y:ℝ)(g:-x ≤ y):-y ≤ x:= by linarith
 let T:=∑ i:A.Hcols,cold H F x.val i; have he:T≤0:=Finset.sum_nonpos fun _ _=>Q.frozen x _
 unfold Wage wage upperB; rw [sub_eq_add_neg,sub_eq_add_neg,←sum_neg_distrib,← sum_neg_distrib]; apply add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
 · refine le_trans (b:= 0 + (Fintype.card A.Hcols:ℝ)*leftCost H F C') (add_le_add he ?_) (zero_add _).le; exact (sum_le_sum (fun i _=> (le_abs_self (leftY H F x.val i)).trans (Q.left x i))).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ])
 · exact sum_le_sum fun i _=> (le_abs_self (tailY H F x.val i)).trans (Q.tail x i)
 · exact (sum_le_sum (fun i _=> (v_ _ _ ((abs_le.mp (Q.billT x i)).1)))).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ]) -- tune neg_right
 · exact sum_le_sum fun i _=> v_ _ _ (abs_le.mp (Q.lucid x i)).1
end Budgeting
end YM.CF.BPress.Honey.Recipe
