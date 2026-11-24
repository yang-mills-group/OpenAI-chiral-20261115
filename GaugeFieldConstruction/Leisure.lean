import GaugeFieldConstruction.Minibus
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5800
set_option maxHeartbeats 280000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Lattice.Corona.Hive
open Function Filter MeasureTheory NormedSpace Finset
open scoped Topology BigOperators Classical
section
variable {n:Side}{α:Type}[Fintype α]{Ω η a:ℝ}{b:ℕ}{L:List (Site n)}(B:Support n)(S:α→Support n)(U:α→ℝ)(p:∀ i, 0≤U i)(l:Scales b a η L)(g:0≤Ω)(q:∀ y:Site n,postG S U (RedB b a η L) y ≤ Ω)(t:Cube_M b *Ω ≤ 1)
local notation "C"=> ColdB b a η L
local notation "R"=> RedB b a η L
local notation "c"=> Cube_M b
local notation "θ"=> beam S U R
def LeadQ (d:ℕ) := (univ:Finset (Fin d →α)).filter fun v=>∀ i,v i ∈ clouds S B
def lengthQ {d:ℕ}(v:Fin d→α):= B ∪ univ.biUnion (S∘ v)
abbrev saltQ {d:ℕ}(v:Fin d→α):= (∏ i,U (v i)) * RedB b a η L (lengthQ B S v)
lemma length0 {d:ℕ}(v:Fin d→α): B⊆ lengthQ B S v:= subset_union_left
include l p
lemma salaries {d:ℕ}{v:Fin d→α}(p':v∈ LeadQ B S d): saltQ B S U (a:=a) (η:=η) (b:=b) (L:=L) v ≤ R B * ∏ i, θ (v i):=by
    unfold saltQ lengthQ RedB; apply (mul_le_mul_of_nonneg_left (Temp_join b (a+6*ζd) η L B (by have h:=l.a0; nlinarith [ζdp]) l.pos.le (S ∘ v) univ (fun i _=> (mem_filter.mp ((mem_filter.mp p').2 i)).2)) (prod_nonneg (fun i _=>p _))).trans_eq
    rw[Finset.prod_mul_distrib]; change _ * (_*_) = _*(_*(∏ i, tempI b _ _ L ((S ∘ v) i))); ring
omit l p
private lemma lead_total {d:ℕ}{q:Fin d→ Finset α}(T:α→ℝ) : (∑ v:Fin d→α with ∀ i,v i∈q i,∏ i,T (v i))=∏ i:Fin d,∑ v∈q i,T v:=by
 let f(i:Fin d)(v:α):ℝ:=if v∈ q i then T v else 0
 calc
 _ = ∑ v:Fin d→α,∏ i,f i (v i):=by
    rw[sum_filter]; refine sum_congr rfl fun i p=>?_ ; split; next h=> exact prod_congr rfl fun j a=>(if_pos (h j)).symm
    next h=> push Not at h; obtain ⟨j,p⟩:=h; symm; apply prod_eq_zero (mem_univ j); exact if_neg p
 _ = ∏ i:Fin d,∑ v:α, f i v:= (Fintype.prod_sum f).symm
 _ = _:=by
    apply prod_congr rfl; intro i _; unfold f; rw [←sum_filter]; simp only [filter_mem_eq_inter,univ_inter]
include l p g q t
-- sharper bounds dividing when d≠0
lemma safari {d:ℕ}(v:d≤2) : (∑ x∈ LeadQ B S d,saltQ B S U (a:=a) (η:=η) (b:=b) (L:=L) x) ≤ R B * ridg b B^2 * if d=0 then 1 else (c*Ω) :=by
    have Hp: (∑ i∈clouds S B, θ i) ≤ (c*Ω)*ridg b B:=by
       refine (clouds_site S (θ) (uni_0 S U p (a+6*ζd) η L b) B Ω q).trans ((mul_le_mul_of_nonneg_left (hefty b B) g).trans_eq (by ring))
    apply (sum_le_sum (fun i hi=> salaries B S U p l hi)).trans; unfold LeadQ; rw [←mul_sum,lead_total,Finset.prod_const,card_univ,Fintype.card_fin] -- tune
    rw[mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Temp_p ..|>.le); refine (pow_le_pow_left₀ (sum_nonneg fun j _=>uni_0 _ _ p _ _ _ _ _) Hp d).trans ?_ -- tune
    split
    · next h=> rw[h,pow_zero,mul_one]; exact one_le_pow₀ (ridg_one ..)
    next h=> rw[mul_pow,mul_comm]; refine mul_le_mul (pow_le_pow_right₀ (ridg_one ..) v) ?_ (pow_nonneg (mul_nonneg (cube_M_pos b|>.le) g) _) (by have he:=ridg_pos b B; positivity); exact (pow_le_pow_of_le_one (mul_nonneg (cube_M_pos b|>.le) g) t (show 1 ≤ d from by omega)).trans_eq (pow_one _)
variable (o y: Site n)(u:o∈B)
local notation "Δ"=>respite b (a+6*ζd) η L S U o y

lemma lead_i {d:ℕ}(h:d ≤ 2)(i:Fin d) (u:o∈B) :
 (∑ x∈ (LeadQ B S d).filter (fun x=>y∈ S (x i)), ∏ j:Fin d, θ (x j)) ≤ ridg b B^3 *(η⁻¹*Δ):=by
    let K:=clouds S B; let J:= K.filter (fun x=>y∈ S x); let P(j:Fin d):=if j=i then J else K
    have hx:(LeadQ B S d).filter (fun x=>y∈ S (x i))=univ.filter fun x:Fin d→α=>∀ j,x j∈P j:=by
       ext x; rw [mem_filter,LeadQ,mem_filter,mem_filter]; constructor
       · rintro ⟨a,z⟩; refine ⟨mem_univ x,fun j=>?_⟩; unfold P; split_ifs with hr; · subst j; exact mem_filter.mpr ⟨a.2 _,z⟩
         exact a.2 j
       intro a
       have H : x i∈ J:= by simpa [P] using a.2 i
       refine ⟨⟨mem_univ _,fun j=>?_⟩,(mem_filter.mp H).2⟩; by_cases d:j=i
       · subst i; exact (mem_filter.mp H).1
       simpa only [P,K,if_neg d] using a.2 j
    rw [hx,lead_total]; let F(j):=∑ x∈P j,θ x
    have g0(j):0≤ F j:=sum_nonneg fun i _=>uni_0 _ _ p _ _ _ _ i
    have e: (∑ j∈K, θ j) ≤ ridg b B:=by
       apply (clouds_site S (θ) (uni_0 S U p _ _ _ _) B Ω q).trans
       apply (mul_le_mul_of_nonneg_left (hefty b B) g).trans; rw[← mul_assoc, mul_comm Ω c]; nlinarith only [mul_le_mul_of_nonneg_right t (ridg_pos b B|>.le)]
    have z:F i ≤ ridg b B*(η⁻¹*Δ):=by unfold F P; rw [if_pos rfl]; exact (clouds_release S U p B o y (a+6*ζd) η L b l.pos u).trans_eq (by ring)
    have hk:(∏ j∈ univ.erase i, F j) ≤ ridg b B^2:=by
       refine (prod_le_prod (fun j _=>g0 j) (g:=fun _=>ridg b B) (fun j hj=>?_)).trans ?_
       · exact (show F j ≤ ridg b B from (by unfold F P; rw[if_neg (mem_erase.mp hj).1]; exact e))
       rw[prod_const]; apply pow_le_pow_right₀ (ridg_one ..); rw[card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]; omega
    change _ ≤ _; rw[←Finset.mul_prod_erase univ F (mem_univ i)] -- might not unfold
    exact (mul_le_mul z hk (prod_nonneg fun i _=>g0 i) ((g0 i).trans z)).trans_eq (by ring)
include u
lemma safari_y {d:ℕ}(v:d≤2) : (∑ x∈LeadQ B S d with y∈lengthQ B S x,saltQ B S U (a:=a) (η:=η) (b:=b) (L:=L) x) ≤ R B * ridg b B^3 *
 ( windPulse b o y * (if d=0 then 1 else c*Ω) + 2*η⁻¹ *Δ ) :=by
    let f(x:Fin d→α):=saltQ B S U (a:=a) (η:=η) (b:=b) (L:=L) x; have z(i):0≤ f i:= mul_nonneg (prod_nonneg (fun j _=>p _)) (Temp_p ..|>.le)
    let W:=LeadQ B S d; let V:= W.filter (fun i=>y∈lengthQ B S i)
    let T:=if d=0 then (1:ℝ) else c*Ω
    have hT:0 ≤ T:=by unfold T; split; exact zero_le_one; exact mul_nonneg (cube_M_pos b|>.le) g
    let K:= ridg b B; have kp:0<K:=ridg_pos ..; have F1:= pulse_pos b o y; have F2:0≤ Δ:=respite_0 _ _ p _ _ _ _ _ _ l.pos.le; have rp:=Temp_p b (a+6*ζd) η L B; let R':=R B; change 0 < R' at rp; have ηp:= l.pos
    change ∑ x∈V,f x≤R' * K^3*(windPulse b o y*T+_)
    by_cases h:y∈ B
    · apply (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _=> z i)).trans ((safari B S U p l g q t v).trans ?_)
      have hz:= mul_le_mul_of_nonneg_right (pulse_core b o B u h) (show 0≤R'*K^2*T by positivity); change R'*K^2*T≤_; change _ * _ ≤ windPulse b o y*K * _ at hz
      nlinarith only [hz, mul_nonneg (show 0 ≤ R'*K^3*(2*η⁻¹) by positivity) F2]
    apply le_trans (b:=∑ i∈W,∑ j:Fin d,(if y∈ S (i j) then f i else 0)); swap
    · rw[sum_comm]; simp_rw [←sum_filter]
      have H(j:Fin d): (∑ i∈W with y∈S (i j),f i) ≤ R'*K^3 *(η⁻¹*Δ):=by
         refine (sum_le_sum (fun i hi=> salaries B S U p l (mem_filter.mp hi).1)).trans ?_; rw [←mul_sum]
         exact (mul_le_mul_of_nonneg_left (lead_i B S U p l g q t o y v j u) rp.le).trans_eq (mul_assoc R' _ _).symm
      refine (sum_le_sum (fun i (_:i∈univ)=>H i)).trans ?_; rw[sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
      have e:= mul_le_mul_of_nonneg_right (show (d:ℝ)≤2 by exact_mod_cast v) (show 0≤R'*K^3*(η⁻¹*Δ) by positivity); nlinarith only[e,mul_nonneg (show 0≤R'*K^3*windPulse b o y by positivity) hT]
    have e:V⊆ W:=filter_subset ..; apply le_trans _ (sum_le_sum_of_subset_of_nonneg e (fun i _ _=>sum_nonneg fun j _=>by split; exact z i; exact le_rfl))
    apply sum_le_sum; intro i l; obtain ⟨j,v,t⟩:=mem_biUnion.mp ((mem_union.mp ((mem_filter.mp l).2)).resolve_left h)
    apply le_trans (le_of_eq (Eq.symm (show (if y∈ S (i j) then f i else 0)= f i from if_pos t)))
    exact Finset.single_le_sum (f:=fun j=> if y∈ S (i j) then f i else 0) (fun j _=>by split; exact z i; exact le_rfl) (mem_univ j)
end
end YM.Lattice.Corona.Hive
end
