import YM.CF.BPress.Chalk.Nest
/-! product toolkit for sitewise CAR operations. Global Koszul signs by Sector rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Chalk
open Function Filter Finset NormedSpace Fock SU SU.Pair Lattice Cube Lat Spin Spin.Paint Spin.Stride Spin.Hole Pf Dial Nacre Tulip Branch Bias Skye Fixed
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N: Side}(x:Site N)
section T
variable {I : Type}[Fintype I][LinearOrder I]{S W V:Finset I}{A B C:FC I}{P:Op I}{b u:Bool}
lemma zoom (h:Sector S b A)(p:S⊆W):Sector W b A:=by
 induction h with| zero=>apply Sector.zero| one=>exact Sector.one| up _ v=> exact .up _ (p v)| down _ v=> exact .down _ (p v)| add _ _ h v=> exact h.add v| mul _ _ h v=>exact h.mul v| scale _ b v=>exact v.scale _
lemma neatN(h:Sector S false A)(p:Sector W u B)(g:Disjoint S W):Commute A B:=by unfold Commute SemiconjBy; simpa [Sector.grainB] using Sector.apart h p g
lemma neatC(h:Sector S false (coupl P)):Sector S false (exp (coupl P)):=by
 have hp(n:ℕ): Sector S false (coupl P^n):=by induction n with|zero=>rw [pow_zero]; exact Sector.one|succ n ih=>rw [pow_succ]; exact ih.mul h
 rw [exp_eq_tsum ℂ]; dsimp only; rw [tsum_eq_sum (s:=range (Fintype.card I+1))]; apply Sector.sumS; intro i _; exact (hp i).scale _; intro i hi; rw [coupl_nil P i (by rw [mem_range] at hi; omega),smul_zero]
lemma neatV (p:P=cutM S*P*cutM S) : Sector S false (coupl P):=by
 unfold coupl; apply Sector.scale; unfold squareP; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _; by_cases g:i∈S∧j∈S; · exact ((Sector.up _ g.1).mul (Sector.up _ g.2)).scale _
 rw [show P i j=0 by nth_rw 1 [p]; rw [slabR,slabL]; split_ifs <;> tauto, zero_smul]; exact .zero _
lemma occupy_κ (V D S W:Finset I): occupy (V∪D) (S∪W)=occupy V S * occupy D W:=by
 ext i j; rw [occupy,slabL]; simp only [light,mem_filter,mem_univ,true_and, union_subset_iff, disjoint_union_right]; by_cases h:i=j; swap; · simp [occupy,cutM,h];
 subst j; simp only [occupy,cutM, Matrix.diagonal_apply_eq, light,mem_filter,mem_univ,true_and, union_subset_iff, disjoint_union_right]; grind
lemma occupy_0 : occupy (∅:Finset I) ∅=1:=by unfold occupy light cutM; simp
lemma own_op (i:I): put i*takeF i=occupy {i} ∅:=by apply op_columns; intro v; rw [occ_act, cut_basis]; simp [light]
lemma end_op(i : I): takeF i*put i=occupy ∅ {i}:=by
 rw [eq_sub_of_add_eq (show takeF i*put i+_=1 from (mixed i i).trans (if_pos rfl)),own_op]; apply op_columns; intro v; rw [act_sub,act_one,cut_basis,cut_basis]; by_cases h:i∈ v <;> simp [h,light]
lemma neat_occupy (p:V⊆S)(q:W⊆S) : Sector S false (occupy V W):=by
 have hu : Sector S false (occupy V ∅):=by
    induction V using Finset.induction_on with | empty=> rw [occupy_0]; exact Sector.one| @insert i v h ih=> rw [←singleton_union,← show ∅∪∅=(∅:Finset I) from rfl, occupy_κ, ←own_op]; have he:i∈S:=p (mem_insert_self ..); exact (((Sector.up _ he).mul (Sector.down _ he)).mul (ih ((subset_insert ..).trans p))) -- syntax
 suffices h: Sector S false (occupy ∅ W) by rw [show occupy V W= occupy V ∅* occupy ∅ W by rw [←occupy_κ,union_empty,empty_union]]; exact hu.mul h
 induction W using Finset.induction_on with
 | empty=>rw [occupy_0]; exact Sector.one
 | @insert i v h ih=> rw [←singleton_union,← show ∅∪∅=(∅:Finset I) from rfl, occupy_κ,←end_op]; have he:i∈S:=q (mem_insert_self ..); exact (((Sector.down _ he).mul (Sector.up _ he)).mul (ih ((subset_insert ..).trans q))) -- tune rfl
end T
abbrev PanelA(N:Side):= {g : Site N→ FC (Single N)// ∀ i, Sector (den i) false (g i)}
def merge (A B:PanelA N): PanelA N:=⟨A.val*B.val,fun i=> (A.property i).mul (B.property i)⟩
def tomes (U:Support N)(A:PanelA N):= U.noncommProd A.val (fun i _ j _ h=> neatN (A.property _) (A.property _) (disj_zone h))
variable (A B:PanelA N) (U: Support N)
lemma brick(i:Site N)(h:i∉U):tomes (insert i U) A=A.val i*tomes U A:= noncommProd_insert_of_notMem _ _ _ _ h -- tune binder order
@[simp] lemma brick_0 : tomes ∅ A=1:=by unfold tomes; simp
lemma congrA (h: Set.EqOn A.val B.val U): tomes U A=tomes U B:=noncommProd_congr rfl (fun i t=> h t) (fun i _ j _ h=>neatN (A.property _) (A.property _) (disj_zone h))
lemma tomes_even : Sector (U.biUnion den) false (tomes U A):=by
 induction U using Finset.induction_on with|empty=> simp; exact Sector.one|@insert i s h ih=> rw [brick _ _ i h,biUnion_insert]; exact (zoom (A.property _) subset_union_left).mul (zoom ih subset_union_right)
lemma comm_tomes(i:Site N)(V:FC (Single N))(p:i ∉ U)(s:Sector (den i) false V): Commute V (tomes U A):=by
 induction U using Finset.induction_on with| empty=>rw [brick_0];exact Commute.one_right _|@insert j s' h ih=> rw [brick _ _ j h]; rw [mem_insert,not_or] at p; exact (neatN s (A.property j) (disj_zone p.1)).mul_right (ih p.2)
lemma merge_prod : tomes U (merge A B)=tomes U A*tomes U B:=by
 induction U using Finset.induction_on with | empty=> simp| @insert i s h ih=> rw [brick _ _ i h,brick _ _ i h,brick _ _ i h,ih]; change A.val i* B.val i * _ = _; simp only [mul_assoc]; rw [← mul_assoc (B.val i),(comm_tomes A s i _ h (B.property i)).eq, mul_assoc]
lemma reading (h:∀ x∈U, acts (A.val x) (vacuum _)= acts (B.val x) (vacuum _)) : acts (tomes U A) (vacuum _)=acts (tomes U B) (vacuum _):=by
 induction U using Finset.induction_on with
 | empty=>simp
 | @insert i u p ih=> rw [brick _ _ i p,brick _ _ i p,act_mul,ih (fun x a=> h x (mem_insert_of_mem a)),←act_mul,(comm_tomes B u _ _ p (A.property i)).eq,(comm_tomes B u _ _ p (B.property i)).eq]; rw [act_mul, h i (mem_insert_self ..), act_mul] -- tune
lemma star_b (S: Support N) : star (tomes S A)=tomes S (⟨fun i=>star (A.val i), fun i=>(A.property i).contr⟩):=by
 induction S using Finset.induction_on with| empty=>simp| @insert i S h ih=> let B:PanelA N:=⟨fun i=>star (A.val i),fun i=>(A.property i).contr⟩; rw [brick _ _ _ h,star_mul,ih,brick _ _ i h]; exact (comm_tomes B S _ _ h (B.property _)).eq.symm
lemma tomes_flour {Z:Type*}[MeasurableSpace Z](A:Z→PanelA N)(h:∀ i∈U,Measurable (fun x:Z=>(A x).val i)): Measurable fun x:Z=> tomes U (A x):=by
 induction U using Finset.induction_on with|empty=> simp_rw [brick_0]; exact measurable_const| @insert i U t ih=> simp_rw [brick _ _ i t]; exact (h i (mem_insert_self ..)).mul (ih (fun i a=> h i (mem_insert_of_mem a)))
lemma tomes_cost(K:ℝ)(h:∀ i∈U, ‖A.val i‖ ≤ K): ‖tomes U A‖ ≤ K^U.card:=by
 induction U using Finset.induction_on with | empty => simp| @insert i U t ih =>
    have hi:=h _ (mem_insert_self ..); rw [brick _ _ i t, card_insert_of_notMem t, pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul hi (ih (fun j r=> h j (mem_insert_of_mem r))) (norm_nonneg _) ((norm_nonneg _).trans hi))
lemma tomes_union (S V:Support N)(h:Disjoint S V): tomes S A*tomes V A=tomes (S∪V) A:=by
 induction S using Finset.induction_on with
 | empty=>simp
 | @insert i U t ih=> simp only [disjoint_insert_left] at h; rw [brick _ _ _ t,mul_assoc,ih h.2,insert_union,brick _ _ i (by simp [t,h.1])]
def pal (S:Support N) (A:PanelA N):PanelA N:=⟨fun i=>if i∈S then A.val i else 1,fun i=>by dsimp only; split; exact A.property _; exact Sector.one⟩
lemma rent (S:Support N) : tomes U (pal S A)= tomes (U∩S) A:=by
 induction U using Finset.induction_on with
 | empty=> simp
 | @insert i U t ih=>
    rw [brick _ _ _ t,ih]; by_cases h:i∈ S
    · rw [insert_inter_of_mem h, brick _ _ i (fun e=>t (mem_inter.mp e).1), pal]; simp [h]
    rw [insert_inter_of_notMem h, pal]; simp [h]
end YM.CF.BPress.Chalk
