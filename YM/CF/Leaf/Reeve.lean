import YM.CF.Leaf.Reign
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[CommRing B][Algebra ℝ B]
section M
-- one and two interaction constructor.Evolve PS recur. Render holder at endpoints plus low corrections.
abbrev vertexL (F:leaf A→ PowerSeries B)(H: leaf A→leaf A→B→B)(X:leaf A):PowerSeries B:= PowerSeries.mk fun i=>Ktw (fun X Y=> H X Y (coeff i (F Y))) X
abbrev vertexD (F:leaf A→ PowerSeries B)(H: leaf A→leaf A→leaf A→B→B→ B)(X:leaf A):PowerSeries B:= PowerSeries.mk fun i=>Kth (fun X Y Z=>∑ k∈ antidiagonal i,H X Y Z (coeff k.1 (F Y)) (coeff k.2 (F Z))) X
abbrev coneU(K:leaf A→ leaf A→ B→B)(Q:leaf A→leaf A→leaf A→ B→B→ B)(D:leaf A→B)(V:leaf A→ PowerSeries B)(X:leaf A) : PowerSeries B:=C (D X)+vertexL V K X + vertexD V Q X
variable(K:leaf A→ leaf A→ B→B)(Q:leaf A→leaf A→leaf A→ B→B→ B)(F D:leaf A→ B)
abbrev mark_A (W:ℕ→leaf A→ B)(X:leaf A):PowerSeries B:= PowerSeries.mk fun i=> W i X
def drum_K(K:leaf A→ leaf A→ B→B)(Q:leaf A→leaf A→leaf A→ B→B→ B)(F D:leaf A→ B):ℕ→ leaf A→ B
 | 0=> F
 | n+1=> fun X =>let V:= mark_A (fun i=>if t:i ≤ n then drum_K K Q F D i else fun _=>0); ((n:ℝ)+1)⁻¹ • coeff n (coneU K Q D V X)
termination_by i=>i
abbrev ξFront:= mark_A (drum_K K Q F D)
lemma credit_T (X:leaf A)(i:ℕ)(U V:leaf A→PowerSeries B)(p:∀ j ≤ i,∀ X,coeff j (U X)=coeff j (V X)):coeff i (coneU K Q D U X)=coeff i (coneU K Q D V X):=by
 unfold coneU vertexL vertexD; rw [map_add,map_add,map_add,map_add,coeff_mk,coeff_mk,coeff_mk,coeff_mk]; simp_rw [p i le_rfl]; congr 2; funext X Y Z; refine sum_congr rfl fun j w=>?_ ; have e:= mem_antidiagonal.mp w; rw [p _ (by omega),p _ (by omega)] -- tune
lemma bud_L(X:leaf A): ξFront K Q F D X= ham (coneU K Q D (ξFront K Q F D) X) (F X):=by
 ext n; cases n; · rw [tick_r,ξFront,mark_A, coeff_mk,drum_K]
 rename_i i; rw [sprig]; nth_rw 1 [ξFront, mark_A, coeff_mk]; rw [drum_K]; apply congrArg; apply credit_T; intro j p U; unfold ξFront mark_A; simp only [coeff_mk,dif_pos p]
-- ℝ major scalar PS collapsed.PP
variable(P G H:leaf A→ℝ)
abbrev Gv(Y T:leaf A)(t:ℝ):= P Y*t
abbrev Gk (Y X W: leaf A)(a b:ℝ):= P Y * a * b
abbrev V_S:=ξFront (Leaf.Gv P) (Leaf.Gk P) G P
lemma Θ_s(V:leaf A→ PS)(X:leaf A) : coneU (Gv P) (Gk P) P V X= PowerSeries.C (P X)+ΦD V P X:=by
 unfold coneU ΦD; rw [add_assoc]; refine congrArg (_ + ·) (congrArg₂ (·+·) ?_ ?_)
 · ext i; rw [vertexL,coeff_mk,αD,show coeff i (Ktw _ X)=_ from KtwP (coeff i|>.toAddMonoidHom) (fun X Y=>P X • V Y) X]; congr 1
 ext i; rw [vertexD,coeff_mk,βD, show coeff i (Kth _ X)=_ from KthP (coeff i|>.toAddMonoidHom) (fun X Y Z=>P X • (V Y*V Z)) X]; congr 1; funext X Y Z; change _=coeff _ (P X • _); rw [coeff_smul,smul_eq_mul,coeff_mul,mul_sum]; exact sum_congr rfl fun j _=>(mul_assoc ..)
lemma stand_V (X:leaf A)(V:leaf A→ PS)(i:ℕ)(p:0≤P)(h:∀ j ≤ i,∀ X,0≤ coeff j (V X)):0 ≤ coeff i (coneU (Gv P) (Gk P) P V X):=by
 unfold coneU; rw [map_add,map_add]; have he: 0 ≤ coeff i (C (P X)):=by rw [coeff_C]; split; exact p _; rfl
 refine add_nonneg (add_nonneg he ?_) ?_
 · unfold vertexL; rw [coeff_mk]; refine sum_nonneg fun X _=>sum_nonneg fun Y _=>?_ ; split; exact mul_nonneg (p _) (h i le_rfl _); rfl
 unfold vertexD; rw [coeff_mk]; refine sum_nonneg fun X _=>sum_nonneg fun Y _=>sum_nonneg fun Z _=>?_ ; split; swap; rfl
 apply sum_nonneg; intro j p'; have he:=mem_antidiagonal.mp p'; exact mul_nonneg (mul_nonneg (p _) (h _ (by omega) _)) (h _ (by omega) _)
lemma crown_K(X:leaf A)(x:0≤ G)(p:0 ≤ P): cent (V_S P G X):=by
 intro i; induction i using Nat.strong_induction_on generalizing X with
 |h i ih=> cases i; · rw [V_S,bud_L,tick_r]; exact x _
           rename_i j; unfold V_S; rw [bud_L,sprig]; exact mul_nonneg (by positivity) (stand_V P _ _ j p (fun i' q X=>ih _ (by omega) _))
lemma trend_K(X:leaf A):derivative ℝ (V_S P G X)=C (P X)+ΦD (V_S P G) P X:=by unfold V_S; nth_rw 1 [bud_L]; rw [Cadre.tide, Θ_s]
abbrev hue_SK(X:leaf A): PS:=ham (ΦD (V_S P G) P X) 0
lemma crispW(p:0 ≤P)(x:0≤G)(X:leaf A):cent (hue_SK P G X):=by
 intro i; cases i; · rw [hue_SK,tick_r]
 rename_i j; rw [hue_SK,sprig]; apply mul_nonneg; positivity
 unfold ΦD; rw [map_add]; apply add_nonneg
 · unfold αD Ktw; rw [map_sum]; apply sum_nonneg; intro i _; rw [map_sum]; apply sum_nonneg; intro k _; split; rw [coeff_smul]; exact mul_nonneg (p _) (crown_K P _ _ x p _); rw [map_zero]
 unfold βD Kth; rw [map_sum]; apply sum_nonneg; intro i _; rw [map_sum]; apply sum_nonneg; intro k _; rw [map_sum]; apply sum_nonneg; intro b _; split; rw [coeff_smul]; exact mul_nonneg (p _) (cent.sip (crown_K P _ _ x p) (crown_K P _ _ x p) _); rw [map_zero] -- tune
end M
variable {N:Side}{X Y Z:Aura N}{δ:ℕ}(K:Rinse (Seat N) (Copy N)){Γ: Aura N→ℝ}{M:Orbit N→ Aura N→ FC (Dwell N)}{H:ℝ}{P:BudgetPoint} (T:Pitch P H δ K Γ M)
variable{a b c v w:ℝ}(hv:1 ≤ H)
abbrev πU(F: Aura N → Copy N) := ξFront (ζA K) (κA K) F (ξA K)
variable (E:Aura N→ Copy N)(I:Aura N→ℝ)(pE:∀ X,Span_K P H X (E X) (I X))
abbrev σ_H (Γ : Aura N→ℝ):Aura N→ℝ:=fun i=>2*Γ i
include T hv pE
lemma εit{F:Aura N→PowerSeries (Copy N)}{V:Aura N→ PS}(i:ℕ)(p:∀ j ≤ i,∀ X,Span_K P H X (coeff j (F X)) (coeff j (V X)))(X:Aura N):Span_K P H X (coeff i (vertexL F (ζA K) X+ vertexD F (κA K) X)) (coeff i (ΦD V (σ_H Γ) X)):=by
 -- PA
 have he:vertexL V (Leaf.Gv (σ_H Γ)) X+vertexD V (Leaf.Gk (σ_H Γ)) X=ΦD V (σ_H Γ) X:=by apply add_left_cancel (a:=PowerSeries.C (σ_H Γ X)); rw [←add_assoc]; exact Θ_s _ _ _
 rw [← he,map_add,map_add,vertexL,vertexD,vertexL,vertexD]; simp_rw [coeff_mk]; apply Medal.plus
 · unfold Ktw; refine Medal.sumP _ _ _ fun i _=>Medal.sumP _ _ _ fun j _=>?_ ; split_ifs with h; subst X; exact pen_A K T hv _ (p _ le_rfl _) True.intro; exact Medal.zeroT
 unfold Kth; refine Medal.sumP _ _ _ fun X _=> Medal.sumP _ _ _ fun Y _=>Medal.sumP _ _ _ fun Z _=>?_ ; split_ifs with h; swap; exact Medal.zeroT
 -- cast by h
 rw [h]; apply Medal.sumP; intro j u; have hx:=mem_antidiagonal.mp u; exact (hoof_L K T hv (p _ (by omega) Y) (p _ (by omega) Z)).2.2
lemma era_K (i:ℕ)(X:Aura N): Span_K P H X (coeff i (πU K E X)) (coeff i (V_S (σ_H Γ) I X)):=by
 induction i using Nat.strong_induction_on generalizing X with
 |h n ih=> cases n; · rw [πU,V_S,bud_L,bud_L,tick_r,tick_r]; exact pE _
           rename_i i; unfold V_S πU; rw [bud_L,bud_L,sprig,sprig]; unfold coneU; -- tune β rhs.THETA
           let p:=εit K T hv E I pE i (fun j p=>ih j (by omega)) X
           have he: coneU (Leaf.Gv (σ_H Γ)) (Leaf.Gk (σ_H Γ)) (σ_H Γ) (V_S (σ_H Γ) I) X=_:= Θ_s ..
           unfold coneU at he; change Span_K P H X (_ • coeff i (C _+vertexL _ _ X+vertexD _ _ X)) (_ • coeff i (C _+vertexL _ _ X+vertexD _ _ X)); rw [he, add_assoc,map_add,map_add]; let Z:Span_K P H X (coeff i (C (ξA K X))) (coeff i (C (σ_H Γ X))):=by rw [coeff_C, coeff_C]; split; exact palm_S K T hv _; exact Medal.zeroT
           exact ((Z.plus p).rum _).big (le_of_eq (by rw [Real.norm_of_nonneg (by positivity)]; rfl))
abbrev huu_SK(X:Aura N):PowerSeries (Copy N):= ham (vertexL (πU K E) (ζA K) X+vertexD (πU K E) (κA K) X) 0
lemma εlx(X:Aura N)(i:ℕ) : Span_K P H X (coeff i (huu_SK K E X)) (coeff i (hue_SK (σ_H Γ) I X)):=by
 unfold huu_SK hue_SK; cases i; · rw [tick_r,tick_r]; exact Medal.zeroT
 rename_i j; rw [sprig,sprig]; exact ((εit K T hv E I pE j (fun i _ X=> era_K K T hv E I pE i X) X).rum _).big (le_of_eq (by rw [Real.norm_of_nonneg (by positivity)]; rfl))
omit T hv pE
lemma born_p(X:Aura N): πU K E X=C (E X)+ PowerSeries.mk (fun i:ℕ=> if i=1 then ξA K X else 0)+huu_SK K E X:=by
 unfold huu_SK; apply PowerSeries.ext; intro n; cases n; · rw [πU,bud_L,tick_r,map_add,map_add,tick_r]; simp only [coeff_mk,coeff_zero_C]; simp
 rename_i i; rw [map_add,map_add,πU]; nth_rw 1 [bud_L]; rw [sprig,sprig,coneU,add_assoc,map_add,coeff_C,coeff_mk, coeff_C]; by_cases h:i=0; · subst i; simp [πU]
 simp [h, πU]
end YM.CF.Leaf
