import GaugeFieldConstruction.HutM
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5800
set_option maxHeartbeats 260000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Lattice.Corona.Hive
open Function Filter MeasureTheory NormedSpace Finset
open scoped Topology BigOperators Classical
section ink
variable {n:Side} (B:ℕ)(a η:ℝ)(L:List (Site n))(X:Support n){A Y: Support n}
def March :ℝ:= Real.exp (a*heft B X)
def tempI :ℝ:= March B a X * Real.exp (Bonus B η L X)
local notation "Z"=> tempI B a η L
lemma Temp_p:0< Z X:= mul_pos (Real.exp_pos _) (Real.exp_pos _)
lemma Temp_roll (h:0≤η)(p:0≤a)(v:¬ Disjoint A Y):Z (A∪Y)≤ (Z A)*(Z Y):=by
 unfold tempI; rw [mul_mul_mul_comm]
 apply mul_le_mul _ (by rw[← Real.exp_add]; exact Real.exp_monotone (Bonus_adv B η L h)) (Real.exp_pos _).le (by unfold March; positivity)
 unfold March; obtain ⟨x,g,t⟩:=Finset.not_disjoint_iff.mp v; rw [←Real.exp_add,←mul_add]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ p; unfold heft; exact_mod_cast meets_sum g t B
lemma Temp_join (p:0≤a)(h:0≤η){I:Type*}(I':I→Support n)(s:Finset I)(v:∀ i∈s,¬Disjoint X (I' i)): Z (X∪s.biUnion I') ≤ Z X*∏ i∈s,Z (I' i):=by
 induction s using Finset.induction with
 | empty=>simpa
 | insert i s t ih=>
    rw[biUnion_insert,union_comm (I' i),← union_assoc]
    refine (Temp_roll B a η L h p (fun K=> v i (mem_insert_self ..) (disjoint_of_subset_left subset_union_left K))).trans ((mul_le_mul_of_nonneg_right (ih (fun k hk=> v _ (mem_insert_of_mem hk))) (Temp_p ..|>.le)).trans_eq ?_)
    rw [prod_insert t]; ring
lemma Temp_gap (h:0≤η)(o:Site n) : Z X + Z X*(η*cum B o X) ≤ tempI B a η (o::L) X :=by
 unfold tempI; rw [Bonus_more,add_comm (η*_), Real.exp_add, ←mul_assoc]; have he:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (η*cum B o X)) (Temp_p B a η L X|>.le); unfold tempI at he; linarith only [he]
lemma Temp_mono (h:0≤η)(o:Site n):Z X≤tempI B a η (o::L) X:= by apply le_trans _ (Temp_gap B a η L X h o); exact le_add_of_nonneg_right (mul_nonneg (Temp_p ..|>.le) (mul_nonneg h (cum_pos ..)))
abbrev RedB (B:ℕ)(a η:ℝ)(L:List (Site n)):=tempI B (a+6*ζd) η L
abbrev ColdB (B:ℕ)(a η:ℝ)(L:List (Site n)):=tempI B (a+2*ζd) η L
lemma coldB_le : ColdB B a η L X*(ridg B X)^4=RedB B a η L X:=by unfold ColdB RedB tempI March ridg; rw [mul_right_comm,←Real.exp_nat_mul,←Real.exp_add]; push_cast; congr 2; ring
abbrev Summit(B:ℕ)(a:ℝ)(X:Support n):= March B (a+16*ζd) X
structure Scales (B:ℕ)(a η:ℝ)(L:List (Site n)):Prop where
 a0:0≤a
 pos:0<η
 toll(X:Support n): Bonus B η L X≤ζd*heft B X
variable {a B η L}
lemma redB_place (m:Scales B a η L): RedB B a η L X*(ridg B X)^9 ≤ Summit B a X:=by
    unfold RedB tempI Summit ridg March; rw[←Real.exp_add,← Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; push_cast; linarith only [m.toll X]
lemma Scales.drop (x:Site n)(m:Scales B a η (x::L)): Scales B a η L:=by
 refine ⟨m.a0,m.pos,?_⟩; intro X; refine le_trans ?_ (m.toll X); rw[Bonus_more]; exact le_add_of_nonneg_left (mul_nonneg m.pos.le (cum_pos ..))
end ink
section geode
variable {n:Side}{I:Type}[Fintype I](X:I→Support n)(U:I→ℝ)(p:∀ i,0≤U i)(A:Support n)(o y:Site n)
variable (a η:ℝ)(L:List (Site n))(b:ℕ)
abbrev beam(M: Support n→ℝ)(i:I):= U i*M (X i)
-- Beware macros order B ℕ after $a η$ deliberately variable? changes for API.Vessel
noncomputable def postY:= ∑ i:I with y∈X i,U i
noncomputable def postG (M: Support n→ℝ)(y:Site n):= postY X (beam X U M) y
noncomputable def clouds:= univ.filter (fun i=>¬Disjoint A (X i))
noncomputable def culm (b:ℕ)(a η:ℝ)(L:List (Site n))(X:I→Support n)(U:I→ℝ)(o:Site n)(i:I):=beam X U (tempI b a η (o::L)) i-beam X U (tempI b a η L) i
abbrev respite(b:ℕ)(a η:ℝ)(L:List (Site n))(X:I→Support n)(U:I→ℝ)(o:Site n)(y:Site n):= postY X (culm b a η L X U o) y
local notation "v" => tempI b a η L
lemma respite_1 : respite b a η L X U o y=postG X U (tempI b a η (o::L)) y-postG X U (tempI b a η L) y:=by unfold postG respite postY culm; rw [sum_sub_distrib]
include p
lemma post_0:0≤postY X U y:= sum_nonneg fun i _=> p i
lemma culm_0 (h:0≤η)(i:I):0≤culm b a η L X U o i:= sub_nonneg.mpr (mul_le_mul_of_nonneg_left (Temp_mono b a η L _ h o) (p i)) -- arg he
lemma uni_0(i:I):0≤beam X U v i:=mul_nonneg (p _) (Temp_p ..|>.le)
lemma respite_0 (h:0≤η):0≤respite b a η L X U o y:= sum_nonneg fun i _=> culm_0 _ _ p _ _ _ _ _ h _ -- tune
lemma clouds_touch (i:I)(w:i∈clouds X A){b:ℕ}{a η:ℝ}{L:List (Site n)}(h:0<η)(e:o∈A) : beam X U (tempI b a η L) i ≤ (η⁻¹ * ridg b A) * culm b a η L X U o i :=by
 let W:=tempI b a η L; let Δ:=culm b a η L X U o i
 obtain ⟨x,p₁,p₂⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp w).2
 have hv' :=Temp_gap b a η L (X i) h.le o
 have hv:windPulse b o x≤cum b o (X i):=single_le_sum (s:=X i) (f:=windPulse b o) (fun i _=>Real.exp_pos _|>.le) p₂
 have hx:1≤cum b o (X i)*ridg b A:=le_trans (pulse_core b o A e p₁) (mul_le_mul_of_nonneg_right hv (ridg_pos ..|>.le))
 have ht:beam X U W i*(η*cum b o (X i)) ≤ Δ:=by unfold beam Δ culm; nlinarith only [mul_le_mul_of_nonneg_left hv' (p i)]
 have hz:= mul_le_mul_of_nonneg_right ht (ridg_pos b A|>.le)
 apply le_of_mul_le_mul_left (a:=η) _ h; change η*_ ≤ η*(η⁻¹*_* Δ); rw [←mul_assoc η (η⁻¹*_ :ℝ),←mul_assoc η η⁻¹,mul_inv_cancel₀ h.ne',one_mul]
 nlinarith only [hz,mul_le_mul_of_nonneg_right hx (show 0≤η*beam X U W i from mul_nonneg h.le (uni_0 X U p _ _ _ _ _))]
lemma clouds_release (h:0<η)(e:o∈A) : (∑ i∈ clouds X A with y∈X i,beam X U v i) ≤ η⁻¹ * ridg b A * respite b a η L X U o y:=by
    rw[respite,postY,mul_sum]; refine (sum_le_sum (fun i hi=>clouds_touch X U p A o i (mem_filter.mp hi).1 h e)).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (s:=(clouds X A).filter _) (by intro i h; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩) (fun i _ _=> ?_)
    exact mul_nonneg (by have t:=ridg_pos b A; positivity) (culm_0 X U p o a η L b h.le i)
lemma clouds_site(v₀:ℝ)(w:∀ i:Site n,postY X U i ≤ v₀): (∑ i∈clouds X A,U i) ≤ v₀*A.card:=by
    let P(y:Site n)(i:I):= if y∈X i then U i else 0; let p₀(y:Site n)(i:I):= show 0≤ P y i by unfold P; split; exact p i; rfl
    apply (sum_le_sum (g:=fun i=>∑ j∈ A, P j i) (fun i t=>?_)).trans; swap
    · obtain ⟨j,w,o⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp t).2; have h:= single_le_sum (s:=A) (f:=fun j=> P j i) (fun j _=>p₀ j i) w; exact le_trans (le_of_eq (if_pos o).symm) h
    rw [sum_comm]; apply (sum_le_sum (g:=fun _=>v₀) (fun i _=>?_)).trans_eq; swap
    · apply le_trans (b:= ∑ j:I,P i j) (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>p₀ _ _)); unfold P; rw[←sum_filter]; exact w i
    simp [mul_comm]
end geode
end YM.Lattice.Corona.Hive
end
