import YM.CF.BPress.Palmer.Basics
/-! lem:B-rootK parts 1 and 2 variants with quantitative thresholds (pure constants * γ/spare; reduce rate if needed and epower). Uses manuscript graph coefficients and trees. All applications here on **finite labels**; log an actual sum over all ordered tuple multiplicities. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Palmer
open Function Relation Filter NormedSpace MeasureTheory Finset Lattice RG Grid Branch Ledger Push.AbsoluteSums Ursell Trees Animals Graph
open scoped Topology BigOperators InnerProductSpace Classical
variable {s:Side}{Y I Ω:Type}[Fintype I][Fintype Y][DecidableEq Y] {F:Branch.Field Y}{X:I→Seal Y}{c a γ δ:ℝ}{w:I→ℝ}{m: Side}
-- pay Part2 at larger factor 2*m & rate half
abbrev till_cost (m:Side)(γ:ℝ):=2*((m.val:ℝ)*γ)
private lemma spark_morph (π:Y→Site s){P:Finset I}(p:Spark X P): Ac.Spark (fun i=> (X i).image π) P:=by
 refine ⟨p.1,?_⟩; intro i h j u; refine Relation.ReflTransGen.mono ?_ _ _ (p.2 i h j u); rintro x y ⟨x',y',v,h,t⟩; exact ⟨x',y',_,mem_image_of_mem π h,mem_image_of_mem π t⟩
lemma spark_pay (p: evenT F X)(T:Sole F m)(D:Stakes m a γ) (H:Cash X w (a+a) γ): Cash (Finset.biUnion · X) (fun P:Finset I=> if Spark X P then ∏ i∈ P,w i else 0) a (till_cost m γ):=by
 obtain ⟨s,π,e,h⟩:= reports F T; have hu:= fare_p F π D p (fun i=> e _ (p i)) h H; let W:=fareX X a w; let V(i:I):=(X i).image π; let q(P:Finset I):=if Spark X P then ∏ i∈ P,w i else 0; have ht(S: Finset I): 0≤q S:= ite_nonneg (prod_nonneg (fun i _=> H.pos i)) le_rfl
 refine ⟨ht,?_ ⟩; intro x
 have he:=touch_tail V 0 hu (π x) 0; have k f: 0 ≤ score (Finset.biUnion · X) q a x f:=by unfold score; split; exact mul_nonneg (Real.exp_pos _).le (ht _); exact le_rfl
 apply budget_mono (budget_loosen he ?_) k; swap; · unfold till_cost; norm_num; exact le_of_eq (by ring)
 intro i; rw [if_pos (Nat.zero_le _)]; unfold score; split; next h₁=>
    dsimp only at h₁; unfold q; split; next h₂=>
       have ht:π x ∈ i.biUnion V:=by obtain ⟨i,h,t⟩:= mem_biUnion.mp h₁; exact mem_biUnion.mpr ⟨i,h,mem_image_of_mem π t⟩
       change Real.exp _*_≤ touches V 0 (fareX X a w) 0 (π x) i; rw [touches,if_pos (show _ from ⟨spark_morph π h₂,ht⟩)]
                       -- indentation redo
       simpa only [currency,zero_mul, Real.exp_zero,mul_one,rent] using (sums_foot D.he.le i H.pos)
    next _h=> rw [mul_zero]; simpa only [Nat.zero_le, ite_true] using he.1 i -- coerc tune rhs if elimin
 next h₁=> simpa only [Nat.zero_le, ite_true] using he.1 i

-- payments for literal Ursell coefficients. already use connected support union
variable (X)
def relate (i j:I): Prop:= ¬Disjoint (X i) (X j)
def carrier (z: Clusters I) : Seal Y:= univ.biUnion (fun i=> X (z.2 i))
abbrev tax (z:Clusters I)(w:I→ℝ):= clusters (relate X) w z.2
lemma carries(z:Clusters I){w:I→ℝ}(v:tax X z w≠0)(g:evenT F X) : Grove F (carrier X z):=by
 have he:coefficient (relate X) z.2≠0:=by intro h; apply v; unfold tax clusters; simp only [h,abs_zero,zero_mul,zero_div]; -- tune
 obtain ⟨W,q,w⟩:= exists_ne_zero_of_sum_ne_zero (show ∑ i∈ connectedGroups (pot (relate X) z.2), Push.AbsoluteSums.Graph.alternating i ≠0 from he); refine union_g ⟨⟨none,mem_univ _⟩,fun i _ j _=> Relation.ReflTransGen.mono ?_ _ _ ((belongs.mp q).2 i j)⟩ (fun i _=>g (z.2 i)); refine fun x y h=> ⟨mem_univ _,mem_univ _,?_⟩; exact Finset.not_disjoint_iff.mp (allow (relate X) z.2 (show link (pot (relate X) z.2) x y from ⟨h.1, (belongs.mp q).1 h.2⟩)) -- tune Graph.link syntax
lemma brute (V:I→ Support s) (H:∀ i j, relate X i j→¬Disjoint (V i) (V j)): Tests (relate X) V:=fun i j v=> Finset.not_disjoint_iff.mp (H _ _ v)
private lemma cluster_man (D:Stakes m a γ)(h:∀ i,0≤ w i)(z:Clusters I): rent a (carrier X z)*tax X z w ≤ clusters (relate X) (fareX X a w) z.2:=by
 let u:= z.2; let b:= |coefficient (relate X) u|; let v:=carrier X z; unfold tax clusters; rw [← mul_div_assoc, mul_left_comm (rent _ _)]; apply div_le_div_of_nonneg_right _ (by positivity); exact mul_le_mul_of_nonneg_left (sums_foot (X:=fun i:Option (Fin z.1)=> X (z.2 i)) D.he.le (w:=fun i=> w (z.2 i)) univ (fun i=>h _)) (abs_nonneg _)
theorem cluster_pay (p: evenT F X)(T:Sole F m)(D:Stakes m a γ) (H:Cash X w (a+a) γ):Cash (carrier X) (fun z=>tax X z w) a (till_cost m γ):=by
 obtain ⟨s,π,e,h⟩:= reports F T; have hu:= fare_p F π D p (fun i=> e _ (p i)) h H; let V(i:I):=(X i).image π; let R:=relate X; have hx: Tests R V:=by apply brute; intro i j t; apply Finset.not_disjoint_iff.mpr; obtain ⟨x,u,v⟩:=Finset.not_disjoint_iff.mp t; exact ⟨_,mem_image_of_mem π u,mem_image_of_mem π v⟩
 have hf(z:Clusters I): 0≤tax X z w:=clusters_nonneg _ H.pos _; refine ⟨hf,?_⟩; intro x; have he : (m.val*γ:ℝ)*(1/2:ℝ)^0*(1-(1/2:ℝ))⁻¹ ≤ till_cost m γ:=by unfold till_cost; norm_num; exact le_of_eq (by ring)
 have hT:= budget_loosen (log_hit_tail R V 0 hx hu le_rfl 0 (π x)) he -- tune argument
 apply budget_mono hT; intro z; unfold score; split; exact mul_nonneg (Real.exp_pos _).le (hf _); exact le_rfl
 intro z; unfold score; split; next b=> obtain ⟨i,e,f⟩:= mem_biUnion.mp b; rw [if_pos (show _ from ⟨Nat.zero_le _,mem_biUnion.mpr ⟨_,mem_univ i,mem_image_of_mem π f⟩⟩)]; simpa only [currency,zero_mul, Real.exp_zero,mul_one,rent,R] using cluster_man X D H.pos z -- tune implicit multiplication
 next h=> exact hT.1 z
end YM.CF.BPress.Palmer
