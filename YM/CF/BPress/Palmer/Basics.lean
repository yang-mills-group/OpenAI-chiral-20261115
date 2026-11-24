import YM.CF.Gas.Shop
import YM.CF.BPress.Grid.Thin
import YM.CF.BPress.Palmer.Graph
import YM.CF.BPress.Ledger
/-! Variant root-K in VolumeB-poly. Our proofs invoke the library's tree hypothesis (for literal Mayer graph decomposition & weights with fixed slack). Variants from `a/8` condition for histories, retains strong conclusion once threshold purchased. Use projection "Sole" for paying root hierarchy only in uniform Arena geometry -- every micro or block shape maps into a Site with bounded multiplicity & preserve of connections. Never define ACTUAL confusability on that projected graph. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Palmer
open Function Filter NormedSpace MeasureTheory Finset Lattice Grid Branch Ledger Push.AbsoluteSums Ursell Trees Animals RG
open scoped Topology BigOperators InnerProductSpace Classical
variable {s:Side}{Y I:Type}[Fintype I][Fintype Y][DecidableEq Y] (F:Branch.Field Y) (X:I→ Seal Y)
structure Sole (F:Branch.Field Y)(m:Side):Prop where
 toy : ∃(s:Side)(f:Y→Site s),(∀x y, F.span x y ≤1→ separation (f x) (f y)≤1) ∧ ∀ x:Site s,(univ.filter (fun y:Y=> f y=x)).card ≤ m.val
abbrev Below {α:Type*} (A:Finset α) [DecidableEq α] (B:Finset α):Prop:= A⊆B
-- cash uses `rent` from Stage.
lemma unit_rent (m:Seal Y)(a:ℝ)(h:0≤a):1≤ rent a m:= Ledger.exp_one m a h
lemma FoldUnit (s: Side) : Sole (field 4 s) 1:=by refine ⟨s,id,fun i j t=> t,fun x=> ?_⟩; have ht: ∀ i:Site s,id i=i:=fun i=>rfl; simp [filter_eq'] -- tune
lemma reports {m:Side}(f:Sole F m): ∃(s:Side)(π:Y→ Site s),(∀x:Seal Y, Grove F x→coverNumber 0 (x.image π)≤x.card) ∧ ∀ x: Site s, (univ.filter (fun i:Y=>π i=x)).card ≤ m.val:=by
 obtain ⟨s,π,f,g⟩:=f.toy; refine ⟨s,π,fun A p=>?_ , g⟩; suffices p:Grove (Tenant.terr s) (A.image π) by rw [Gas.zeroΩ _ p]; exact card_image_le
 induction p with|single v=> rw [image_singleton]; exact .single _| @join A x y g h f' ih=> rw [image_insert]; exact .join ih (mem_image_of_mem π h) (f x y f')
variable {c a γ δ :ℝ} (w:I→ℝ)
abbrev evenT (F:Branch.Field Y) (X:I→ Seal Y): Prop:= ∀ i:I,Grove F (X i)
abbrev fareX (X:I→ Seal Y)(a:ℝ)(w:I→ℝ)(i:I) := rent a (X i)*w i
lemma fare_le (h:∀ i,0≤ w i)(p:0≤a)(i:I): w i≤fareX X a w i:= le_mul_of_one_le_left (h i) (unit_rent _ _ p)
structure Stakes (m:Side)(a γ:ℝ):Prop where
 he : 0<a
 hp:0<γ
 stand: (m.val:ℝ)*γ * 8≤ a
variable {F X w} {m:Side}
lemma fare_p (F:Branch.Field Y)(π:Y→Site s)(u:Stakes m a γ)(e: evenT F X)(v:∀ i,coverNumber 0 ((X i).image π)≤ (X i).card)(t:∀ x:Site s,(univ.filter (fun i:Y=>π i=x)).card ≤ m.val)(K:Cash X w (a+a) γ) : let V(i:I) := (X i).image π; Ready V 0 (fareX X a w) 0 (m.val*γ) a (1/2):=by
 intro V; let g:=(m.val:ℝ)*γ; let W:= fareX X a w; have he:=u.hp; have hu:=u.he; have hp:degreePrice 0 g a≤1/2:=by
    unfold degreePrice stretch Animals.ballCost g; norm_num; rw [←mul_div_assoc,div_le_div_iff₀ hu (by norm_num : (0:ℝ)<2)]; nlinarith only [u.stand]
 have hW(i):0≤W i:= mul_nonneg (Real.exp_pos _).le (K.pos i); refine ⟨by positivity,u.he,hp,by norm_num,hW,?_⟩; intro x0
 let T:= univ.filter (fun i:Y=>π i=x0); have hm:= budget_over T (fun x=> Ledger.score X w (a+a) x) (fun _=>γ) (fun i _=> K.hits i); rw [sum_const,nsmul_eq_mul] at hm; refine budget_loosen (budget_mono hm (fun i=> ?_) (fun i=> ?_)) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (t _)) he.le); · split; exact mul_nonneg (hW _) (Real.exp_pos _).le; exact le_rfl
 split; next h=>
    obtain ⟨x,q,x'⟩:= mem_image.mp h; apply le_trans _ (single_le_sum (f:=fun x=>score X w (a+a) x i) (fun x _=> (K.hits x).1 i) (mem_filter.mpr ⟨mem_univ _, x'⟩)); rw [score,if_pos q]; change W i * Real.exp ((0+a)*(coverNumber 0 (V i):ℕ))≤ _; rw [zero_add]; refine (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (v i)) hu.le)) (hW i)).trans ?_; unfold W fareX rent; rw [add_mul,Real.exp_add]; exact Eq.le (by ring)
 next h=> exact hm.1 i

-- root product of costs and support inflation
lemma sums_foot (ha:0≤ a)(b:Seal I) (t: ∀ i,0≤ w i): rent a (b.biUnion X)*(∏ i∈b,w i) ≤ ∏ i∈b,fareX X a w i:=by
 unfold fareX rent; rw [prod_mul_distrib,←Real.exp_sum,←mul_sum, ←Nat.cast_sum]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr card_biUnion_le) ha)) (prod_nonneg (fun i _=>t i)) -- tune
lemma union_g{g:Seal I}(p:Spark X g)(h:∀ i∈g,Grove F (X i)): Grove F (g.biUnion X):=by
 obtain ⟨i,l⟩:=p.1; obtain ⟨x,u⟩:= Grid.inhabited_grove (h i l); refine trunk (mem_biUnion.mpr ⟨i,l,u⟩) ?_; intro y k; obtain ⟨j,t,v⟩:= mem_biUnion.mp k; have he(i)(t:i∈g):X i⊆g.biUnion X:= subset_biUnion_of_mem X t; have ht(j:I)(Q:chain X g i j): ∀ y∈X j,Origin F (g.biUnion X) x y:=by
    induction Q with| refl=> exact fun y ht=>orig_sub (rooted (h i l) x u y ht) (he i l)|tail a b ih=> obtain ⟨h₁,h₂,x,h₃,h₄⟩:= b; exact fun y hy=>(ih x h₃).trans (orig_sub (rooted (h _ h₂) x h₄ y hy) (he _ h₂))
 exact ht _ (p.2 i l j t) _ v
end YM.CF.BPress.Palmer
