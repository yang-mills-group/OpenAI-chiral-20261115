import YM.CF.BPress.Pine.Bud
/- Eq:B-PfC sum over decorated labels. Group with Palmer, fits contour-free theorem part. Pairing *sign* and zero of non-matches/repeats implemented through genuine Pfaffian tested on exterior strings, only geometry projection for power. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
namespace Story
variable {D:EdgeD I B Y F}(S:Story J D)(p:S.Drone)
open Push.AbsoluteSums.Gas
lemma fort_union :fort S p= S.base p.1∪ univ.biUnion fun i:Permits (S.word p.1)=> lit D (i: I) (p.2 i):=rfl
lemma frag(i: EdgeD.Permits (S.word p.1)) {a:D.Prec i.val}(v:p.2 i= some a): ((look D a.val) ∩ S.base p.1).Nonempty:=by
 have he : i.val∈ S.word p.1:= List.mem_toFinset.mp (mem_coe.mp i.property); have ht : i.val = D.src a.val:= (mem_filter.mp a.property).2; exact ⟨D.anchor i.val,mem_inter.mpr ⟨Eq.mp (congrArg (· ∈ D.look a.val) (congrArg D.anchor ht).symm) (D.back _), S.paid _ _ he⟩⟩
lemma base_sub:S.base p.1 ⊆ fort S p:=subset_union_left
lemma lit_sub (i: Permits (S.word p.1)): D.lit i.val (p.2 i)⊆ fort S p:= (subset_biUnion_of_mem (fun i:Permits (S.word p.1)=> lit D _ (p.2 i)) (mem_univ i)).trans subset_union_right
lemma foot_fold (P: Seal S.Drone): (P.image S.fetch).biUnion S.base⊆ P.biUnion S.fort:=by intro i h; obtain ⟨k,h,g⟩:= mem_biUnion.mp h; obtain ⟨a,v,rfl⟩:= mem_image.mp h; exact mem_biUnion.mpr ⟨a,v, S.base_sub a g⟩
lemma locationG : Grove F (S.fort p):=by
 let B:=S.base p.1; let f:=fun i: Permits (S.word p.1)=> lit D i.val (p.2 i); let h:= fun T:Finset (Permits (S.word p.1))=> B∪ T.biUnion f; suffices u:∀ T,Grove F (h T) from u univ
 intro T; induction T using Finset.induction_on with|empty=> simp only [h,biUnion_empty,union_empty]; exact S.landed _|@insert i A t ih=>
    rw [show h (insert i A) =f i ∪ h A by simp [h,union_comm, union_assoc, union_left_comm]]; unfold f lit; cases R:(p.2 i); simp only [Option.elim_none,empty_union]; exact ih; rename_i b; obtain ⟨x,T,O⟩:= Finset.not_disjoint_iff.mp (show ¬Disjoint (D.look b.val) B from (by rw [Finset.disjoint_iff_inter_eq_empty]; exact Finset.Nonempty.ne_empty (S.frag p i R)))
    exact Grove.unite (D.paints b.val) ih T (subset_union_left O) -- f unfolds mismatch

abbrev key (D:EdgeD I B Y F)(S:Seal Y):Finset I:= univ.filter (fun i=>D.anchor i∈S)
variable (K:B→ℂ)(b:J→ℂ)
lemma sphereG: Sector (key D (S.fort p)) false (firm S p).val:= by apply Chalk.zoom ((lifted _ (S.e p.1)).2); intro i a; exact mem_filter.mpr ⟨mem_univ _,S.base_sub p (S.paid _ _ (List.mem_toFinset.mp a))⟩
lemma warm {α:Type}[DecidableEq α](P:Finset α)(S:Finset I)(g:α→ Dough I)(p:∀ i∈P,Sector S false (g i).val): Sector S false ((∏ i∈P,g i).val):=by
 induction P using Finset.induction_on with|empty=> rw [prod_empty]; exact Sector.one|@insert i P t ih => rw [prod_insert t]; exact (p i (mem_insert_self ..)).mul (ih (fun i v=>p i (mem_insert_of_mem v)))
lemma growG: Sector (key D (fort S p)) false (cairn S K p).val:=by
 apply warm; intro i u; have ht:= lit_sub S p i; unfold green; cases w:p.2 i; exact Sector.one; rename_i a; let Q:=a.val; rw [w] at ht; have he: D.look a.val ⊆ _:= ht; exact ((Sector.up (D.src Q) (mem_filter.mpr ⟨mem_univ _,he (D.back _)⟩)).mul (Sector.up (D.dst Q) (mem_filter.mpr ⟨mem_univ _,he (D.front _)⟩))).scale _
lemma key_le {P Q:Seal Y}(p:P⊆Q) : key D P⊆key D Q:=fun i l=> mem_filter.mpr ⟨mem_univ _,p (mem_filter.mp l|>.2)⟩
lemma funds (T:Seal (S.Drone)):Sector (key D (T.biUnion S.fort)) false (S.allStem T).val∧ Sector (key D (T.biUnion S.fort)) false (S.allFresh K T).val := by
 have ht(p)(v:p∈T): key D (S.fort p)⊆ key D (T.biUnion S.fort):= key_le (fun i h=> mem_biUnion.mpr ⟨p,v,h⟩); exact ⟨warm T _ _ (fun i v=>Chalk.zoom (S.sphereG i) (ht _ v)), warm T _ _ (fun i v=>Chalk.zoom (S.growG i K) (ht _ v))⟩
lemma dispersed (U Q:Finset I)(v:Disjoint U Q)(A B C D:Dough I)(h:Sector U false A.val)(p:Sector U false B.val)(q:Sector Q false C.val)(u:Sector Q false D.val) : grap (A*C) (B*D)=grap A B * grap C D:=by
 let Ω:= vacuum I; let W:= (star A.val*B.val); let Z:= (star C.val*D.val); have he(X Y:Dough I):grap X Y=(star X.val*Y.val) ∅ ∅:=by unfold grap; nth_rw 1 [← star_star X.val]; rw [act_inner,←act_mul,vacuum,basis_inner,basis_act]
 rw [he,he,he]; have ht:star ((A*C).val)*(B*D).val=W*Z:=by
    change star (A.val*C.val)*(B.val*D.val)= _; rw [star_mul]; rw [←mul_assoc (star C.val * _), mul_assoc (star C.val) (star A.val), show star C.val*(star A.val*B.val)= W *star C.val from (Chalk.neatN (h.contr.mul p) (q.contr) v).symm.eq,mul_assoc W]; -- tune
 rw [ht]; exact (h.contr.mul p).sliced (q.contr.mul u) v ∅

lemma class_union {P Q: Finset S.Drone}(h:Disjoint (P.biUnion S.fort) (Q.biUnion S.fort)): S.Class (P∪Q)↔ S.Class P∧S.Class Q:=by
 let R(P:Finset S.Drone):=P.image S.fetch; have he: Disjoint ((R P).biUnion S.base) ((R Q).biUnion S.base):=h.mono (foot_fold S P) (foot_fold S Q); have hp(i)(q:i∈R P): S.base i⊆(R P).biUnion S.base:=subset_biUnion_of_mem _ q; have hr(i)(p:i∈R Q): S.base i⊆(R Q).biUnion S.base:=subset_biUnion_of_mem _ p; have hv(i j)(a:i∈R P)(e:j∈ R Q):Disjoint (S.base i) (S.base j):= he.mono (hp _ a) (hr _ e); have hd:Disjoint (R P) (R Q):=by
    refine disjoint_left.mpr fun i q p=>?_ ; obtain ⟨x,v⟩:=Grid.inhabited_grove (S.landed i); exact disjoint_left.mp (hv i i q p) v v
 unfold Class separated; rw [image_union, coe_union]; simp only [mem_union]; constructor; · rintro ⟨t,k⟩; exact ⟨⟨t.mono Set.subset_union_left, fun i x j u=> k i (Or.inl x) j (Or.inl u)⟩,⟨t.mono Set.subset_union_right, fun i x j u=> k i (Or.inr x) j (Or.inr u)⟩ ⟩
 rintro ⟨⟨T,U⟩,Y,V⟩; have he(a b)(t:a∈P)(p:b∈Q) : S.fetch a≠ S.fetch b:= fun h=> disjoint_left.mp hd (h ▸ mem_image_of_mem S.fetch t) (mem_image_of_mem S.fetch p)
 refine ⟨?_,?_⟩; · rintro x (p|p) y (r|r) f; exact T p r f; exact (he _ _ p r f).elim; exact (he _ _ r p f.symm).elim; exact Y p r f
 rintro i (l|l) j (q|q) f; exact U _ l _ q f; exact fun p=> S.focus i j p (hv i j l q); exact fun p=> S.focus i j p ((hv j i q l).symm); exact V _ l _ q f
lemma total_cohort : Grows S.fort (totalW S K b):=by
 refine ⟨?_,?_⟩; · rw [totalW]; simp only [Class,coe_empty,Set.injOn_empty,image_empty, separated,notMem_empty,IsEmpty.forall_iff,true_and,ite_true,prod_empty,allStem,allFresh,one_mul,grap,Subalgebra.coe_one,act_one]; rw [inner_self_eq_norm_sq_to_K]; simp [vacuum,basisKet] -- tune
 intro V U p t; unfold totalW; have he:= class_union S p; split; next k=>
    rw [if_pos (he.mp k).1,if_pos (he.mp k).2]; unfold allStem allFresh; rw [prod_union t,prod_union t,prod_union t]; have hx:Disjoint (key D (V.biUnion S.fort)) (key D (U.biUnion S.fort)):=by refine disjoint_left.mpr fun x h l=> disjoint_left.mp p ((mem_filter.mp h).2) ((mem_filter.mp l).2)
    rw [dispersed _ _ hx _ _ _ _ (S.funds K V).1 (S.funds K V).2 (S.funds K U).1 (S.funds K U).2]; ring
 next k=> split_ifs <;> first| tauto| simp
end Story
end YM.CF.BPress.Pine
