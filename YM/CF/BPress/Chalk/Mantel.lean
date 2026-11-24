import YM.CF.BPress.Chalk.Throne
/-! eq:B-Madd, optional J relation later. Direct compressed pair exterior, not most-likely center payoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Chalk
open Function Filter Finset NormedSpace Fock SU SU.Pair Lattice Cube Lat Spin Spin.Paint Spin.Stride Spin.Hole Pf Dial Nacre Tulip Branch Bias Skye Fixed Net Meadow
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}(H:Paint (More N))(x:Site N)
abbrev liftPack:PanelA N:=⟨fun i=> pureUp i (H (node i)),fun _=>pure_sect ..⟩
def shroud (U:Support N) : FC (Single N):=star (tomes U (liftPack H))
/-- Insert the M-add on sites K. H can be any completion on total lattice (choose reference on other sites). Need Mark itself to use *only* H on that band of course. -/
lemma liftHere (P K:Support N)(t:K⊆ P)(p:MatPlan H) : let v:= woven H P; let u:=woven H (P\K); acts (star (shroud H K)) (acts (tomes univ v) (vacuum _))= acts (tomes univ u) (vacuum _):=by
 intro v u; let T:=pal K (liftPack H); have ht : tomes K (liftPack H)= tomes univ T := by unfold T; rw [rent]; simp
 rw [shroud,star_star,← act_mul,ht,←merge_prod]; refine Chalk.reading _ _ _ ?_; intro i _; unfold merge; simp only [Pi.mul_apply]; by_cases h:i∈K; swap
 · have ht: u.val i=v.val i:=by change (if i∈P\K then _ else (1:FC _))* (sail H).val i=(if i∈P then _ else 1)* _; by_cases p:i∈P <;> split_ifs <;> grind [Finset.mem_sdiff]
   rw [ht, show T.val i=1 from if_neg h,one_mul]
 have hx:i∉ P\K:=fun g=> (mem_sdiff.mp g).2 h
 change acts (T.val i*((pal P helm).val i*(sail H).val i)) _=acts ((pal (P\K) helm).val i*(sail H).val i) _; rw [show T.val i=_ from (show T.val i=pureUp i (H (node i)) from if_pos h), show (pal P helm).val i=proud i from if_pos (t h), show (pal (P\K) helm).val i=1 from if_neg hx,one_mul, act_mul, show (sail H).val i=summitOp i (H (node i)) from rfl,markHere i (p _),triumphant i (p _)]
lemma candle (P K: Support N)(t:K⊆ P)(p:MatPlan H) (u:Wave (Single N)) : inner ℂ (braC (Locks P true) (Locks P false) (coupling H)) (acts (shroud H K) u)=inner ℂ (braC (Locks (P\K) true) (Locks (P\K) false) (coupling H)) u := by rw [woven_unit,woven_unit,←act_inner,liftHere H P K t p]
lemma aligns(v:Mach (More N)): twist (tradew N v) (shelf x) = shelf x:=by
 rw [twist_C]; apply neComm; rintro ⟨⟨i,b⟩,p⟩ ⟨⟨j,a⟩,t⟩ h; have hp:i=j:=by contrapose! h; simp [tradew,h,jump_apply]
 simp only [den,mem_filter,mem_univ,true_and,penX,hp]
lemma shunt_proud (v:Mach (More N)) : twist (quantU (tradew N v)) (proud x)= proud x ∧ twist (quantU (tradew N v)) (Dock x)=Dock x:=by
 let A:=tradew N v; have he(i:Bool): Commute A.val (cutM (Locks {x} i)):=((twist_C A).1 (terra_l (S:={x}) i v)|>.symm); constructor <;> rw [twist_C]
 exact (Arrival.coexist (outage ({x}:Support N)) (he true) (he false)).symm
 exact (Arrival.coexist (S:=∅) disjoint_bot_left (by rw [show cutM (∅:Finset (Single N))=(0:Op (Single N)) by unfold cutM; simp]; exact Commute.zero_right _) ((twist_C A).mp (aligns x v)).symm).symm
lemma shunt_stage (v:Mach (More N)): twist (quantU (tradew N v)) ((liftPack H).val x)= (liftPack (rotateC v H)).val x:=by
 let A:=tradew N v; let B:=regent H x; let C:=regent (rotateC v H) x; let S:=shelf x
 have he : C=congrC A B:=by
    unfold B C; rw [←placed,←placed,coupe_gauge]; have hx:= board_twist A S (coupling H); have ht: twist A S=S:= aligns x v; rw [ht,Fock.body,Fock.body, show cc S=S from cut_real _] at hx; exact hx
 have ht : twist (quantU A) (summitOp x (H (node x)))=exp (coupl C):=by
    have hp:= coupl_cov A.val (regent H x); let U:=quantU A; change U.val*_=_*U.val at hp; rw [summitOp, breeze_exp, twist_formula]; change exp (U.val *coupl B*star U.val)=_; rw [show U.val *coupl B=coupl (congrC A B)*U.val from hp]; rw [mul_assoc,U.property.2,mul_one,he]; -- tune
 change twist (quantU A) (pureUp x _)=pureUp x _; unfold pureUp; dsimp only; rw [map_mul,map_mul,map_mul,map_star,ht,(shunt_proud x v).1,(shunt_proud x v).2]; -- tune
lemma staysH(U:Support N)(v:Mach (More N)): twist (quantU (tradew N v)) (shroud H U)= shroud (rotateC v H) U:=by
 set_option synthInstance.maxSize 20000 in
 unfold shroud; rw [map_star]; apply congrArg; induction U using Finset.induction_on with | empty=> rw [brick_0,brick_0,twist_formula,mul_one,(quantU _).property.2]| @insert i U h ih=> rw [brick _ _ _ h,brick _ _ _ h, map_mul, shunt_stage,ih]
lemma room_eq (U:Support N)(Z:Paint (More N))(t:∀ i∈U,H (node i)=Z (node i)): shroud H U=shroud Z U:=by apply congrArg star; apply congrA; intro i p; unfold liftPack; dsimp only; rw [t _ p]
-- state shell S and cap
lemma norm_hand(i:Single N):‖put i‖≤1:=by
 have he:= CStarRing.norm_self_mul_star (x:=put i); have hx: ‖put i*star (put i)‖ ≤1:=by rw [show star (put i)=_ from (rfl:star (put i)=takeF i),own_op]; exact IsStarProjection.norm_le _ (cutM_idp _)
 nlinarith [norm_nonneg (put i)]
lemma exp_cost (K : FC (Single N)): ‖exp K‖ ≤ Real.exp ‖K‖ :=by
 rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂:=ℝ) K)).trans ?_; exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) K) (by apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖K‖) (fun n=> by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity)) -- Graph.Coif reuse
abbrev ν :ℝ:= Fintype.card Page
private lemma bears (x:Site N) : ((den x).card:ℝ)=ν:=by
 have ht: (den x).card=Fintype.card Page:=by
    let f(a:Page):Single N:=((x,a.1),a.2); have hu:den x=univ.image f:=by ext i; simp only [den,mem_filter,mem_univ,true_and,mem_image]; constructor; intro g; exact ⟨(i.1.2,i.2),by unfold f; rw [← g]⟩; rintro ⟨a,rfl⟩; rfl
    rw [hu,card_image_of_injective,card_univ]; intro i j h; exact Prod.ext (Prod.mk.inj (Prod.mk.inj h).1).2 (Prod.mk.inj h).2
 rw [ht] 
lemma bear_cost (x:Site N)(A:Op Slot)(p:Spin.Sym A): ‖summitOp x A‖≤ Real.exp (ν^2):=by
 let Y:=Yore x A; let F(i j):= Y i j • (put i*put j); have hx(i j:Single N):‖F i j‖ ≤ if i∈den x ∧ j∈den x then (1:ℝ) else 0:=by
    unfold F; rw [norm_smul]; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans (mul_le_one₀ (norm_hand _) (norm_nonneg _) (norm_hand _))))
    unfold Y; rw [yore_at]; simp only [den,mem_filter,mem_univ,true_and]; split; exact (norm_entry (nodeC A) _ _).trans (CStarRing.norm_of_mem_unitary (node_unit _ p.gate)).le; rw [norm_zero]
 apply (exp_cost (coupl Y)).trans; apply Real.exp_monotone; let Z:= ∑ i,∑ j,F i j; change ‖(2:ℂ)⁻¹ • Z‖≤_; rw [norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(2:ℂ)⁻¹‖≤1)); unfold Z; apply (norm_sum_le univ (fun i:Single N=> ∑ j,F i j)).trans; refine (sum_le_sum (s:=univ) (fun i _=> (norm_sum_le univ (F i)).trans (sum_le_sum (fun j _=> hx i j)))).trans ?_; simp_rw [ite_and]
 have ht(i:Single N):(∑ j:Single N, (if i∈den x then if j∈den x then (1:ℝ) else 0 else 0))= if i∈den x then ν else 0 :=by by_cases h:i∈den x; simp_rw [if_pos h, ←sum_filter]; simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,bears,mul_one]; simp only [if_neg h,sum_const_zero]
 simp_rw [ht,←sum_filter]; simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,bears,pow_two,le_refl]
lemma bears_κ(x:Site N)(A:Op Slot)(p:Spin.Sym A):‖pureUp x A‖ ≤ (Real.exp (ν^2))^2:=by
 let M:= summitOp x A; have he: ‖M‖≤ Real.exp (ν^2):= bear_cost x A p
 have ht(X:Finset (Finset (Single N))) : ‖cutM X‖≤1:= IsStarProjection.norm_le _ (cutM_idp X)
 apply ((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (ht _))).trans; apply (norm_mul_le ..).trans; rw [pow_two,norm_star]; exact mul_le_mul ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (ht _)).trans he)) he (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.BPress.Chalk
