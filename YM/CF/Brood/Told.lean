import YM.CF.Tar.Epip -- heavy imports basis declarations
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {A B E F X:Type*}[NormedAddCommGroup A][NormedSpace ℂ A][NormedAddCommGroup B][NormedSpace ℂ B][NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F][NormedAddCommGroup X][NormedSpace ℂ X]
variable [FiniteDimensional ℂ A][FiniteDimensional ℂ B][FiniteDimensional ℂ F][FiniteDimensional ℂ E]
variable {J I:Type*}[Fintype J][Fintype I]
variable (W: Basis J ℂ A)
def ρθ (W:Basis J ℂ A):=1+ ∑ j:J,‖LinearMap.toContinuousLinearMap (W.coord j)‖
lemma μp_pos :0 < ρθ W:=add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=>norm_nonneg _)
lemma pagan (i:J)(x:A):‖W.repr x i‖≤ρθ W*‖x‖:=by
 let L:=(W.coord i).toContinuousLinearMap; exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_trans (single_le_sum (fun j _=>norm_nonneg (LinearMap.toContinuousLinearMap (W.coord j))) (mem_univ i)) (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)) -- tune zh
lemma perk_l (T:A→ₗ[ℂ]B)(C:ℝ)(p:0 ≤ C)(h:∀ j,‖T (W j)‖≤ C)(x:A):‖T x‖≤ C*ρθ W *‖x‖:=by
 have he:T x=∑ j:J,W.repr x j • T (W j):= by
    nth_rw 1 [←W.sum_repr x]; rw [map_sum]; simp_rw [map_smul] -- cue
 rw [he]; apply (norm_sum_le ..).trans; calc
    _ ≤ ∑ j:J,‖LinearMap.toContinuousLinearMap (W.coord j)‖* ‖x‖*C:= sum_le_sum fun j _=>by rw [norm_smul]; exact mul_le_mul (((W.coord j).toContinuousLinearMap).le_opNorm _) (h _) (norm_nonneg _) (by positivity)
    _ ≤ _:=by
       rw [← sum_mul,←sum_mul]; let z:=ρθ W; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg x)) p).trans_eq (show ρθ W*‖x‖*C=C*ρθ W*‖x‖ from by ring) -- simplify direction
lemma ε_shear (M α:ℝ)(ha:0<α)(hp:0 ≤ M):∃ q ε:ℝ,0< q∧0<ε ∧∀ x a b c:ℝ,0≤ a → x=max a b → α*a ≤ c+ε*x → α*b ≤ c+ ε*x+M*a → x ≤ q*c:=by
 let k:=α⁻¹; have hk:0 < k:=inv_pos.mpr ha; let K:=k+k*M*k; have hx:k ≤ K:=le_add_of_nonneg_right (by positivity)
 have hz:= lt_of_lt_of_le hk hx; refine ⟨2*K,1/(2*K),by positivity,by positivity,?_⟩
 intro x a b c hvA h xq y -- does require signs.Peek if a negative K*(c+eps*x) cannot dominate CaseA.M. add 0 ≤ a hypothesis
 let V:= c+1/(2*K)*x; have hu:a≤k*V:=(le_inv_mul_iff₀ ha).mpr xq
 have hv : b≤ k*(V+M*a):=(le_inv_mul_iff₀ ha).mpr y
 have hq: b ≤ K*V:=hv.trans ((mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hu hp) _) hk.le).trans_eq (by unfold K; ring)) -- order
 have hψ:0≤ V:=by
    apply le_trans _ (show α*a≤V from xq); positivity
 have hB : x≤ K*V:= h.trans_le (max_le (hu.trans (mul_le_mul_of_nonneg_right hx hψ)) hq)
 unfold V at hB; rw [mul_add,←mul_assoc K _ x,show K*(1/(2*K))=1/2 from (by field_simp)] at hB; linarith
-- B first then (A,C frame). triangular full error bound. Assumed D lower bound using scales. columns.
local notation "O"=> (B × F)
local notation "Jr"=> (Sum J I)
variable (U:Basis I ℂ (B×F))
local notation "Tκ"=> (W.prod U)
local notation "Ψ"=> (A × B× F)
variable (v:A×(B×F)→ₗ[ℂ]A×(B×F))
noncomputable def urn_K (v:A× (B× F)→ₗ[ℂ] A × (B×F)):A×(B×F)→ₗ[ℂ] A:= (LinearMap.fst ..).comp v
def vein_K (v:A× (B×F)→ₗ[ℂ]A×(B×F)):A×(B×F)→ₗ[ℂ](B×F):=(LinearMap.snd ..).comp v
local notation "TS"=> (LinearMap.inl ℂ A O)
local notation "QS"=> (LinearMap.inr ℂ A O)
local notation "Yt"=> (Sum J I)
local notation "ΠZ"=> (fun i:Yt=> (W.prod U) i)
lemma closer_S (T D:Ψ→ₗ[ℂ]Ψ) (C ε α:ℝ)(ht:0 ≤ C)(hu:0 ≤ ε)(h:∀ i, ‖(T (Tκ i)).1 -(D (Tκ i)).1‖ ≤ ε)(hz:∀ i:I,‖(T (0,U i)).2- (D (0,U i)).2‖ ≤ ε)(hk:∀ i:J, ‖(T (W i,0)).2- (D (W i,0)).2‖ ≤ C)(p:∀ x:Ψ, α*‖x.1‖ ≤ ‖(D x).1‖ ∧ α*‖x.2‖≤ ‖(D x).2‖)(x:Ψ): α*‖x.1‖ ≤ ‖T x‖ + (ε*ρθ (Tκ))*‖x‖ ∧ α*‖x.2‖≤ ‖T x‖+(ε* ρθ U)*‖x‖ + (C*ρθ W)*‖x.1‖:=by
 let z:=T-D
 let L:= vein_K z
 have hp:‖(T x).1-(D x).1‖≤ ε*(ρθ Tκ)*‖x‖:=perk_l Tκ (urn_K z) ε hu h x
 have hv:‖(T x).2-(D x).2‖≤ ε*ρθ U*‖x‖ + C*ρθ W*‖x.1‖:=by
    change ‖L x‖≤ _; nth_rw 1 [show x=QS x.2+TS x.1 from (by ext <;> simp)]; rw [map_add]; exact (norm_add_le ..).trans (add_le_add ((perk_l U (L.comp QS) ε hu hz x.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le _) (mul_nonneg hu (μp_pos U).le))) (perk_l W (L.comp TS) C ht hk x.1))
 constructor
 · have hB:= norm_sub_norm_le (D x).1 (T x).1; have hU:‖(D x).1-(T x).1‖= ‖(T x).1-(D x).1‖:= norm_sub_rev ..; rw [hU] at hB; exact (p x).1.trans (by linarith only [hp,hB,norm_fst_le (T x)])
 have hB:= norm_sub_norm_le (D x).2 (T x).2; have hU:= norm_sub_rev (D x).2 (T x).2; rw [hU] at hB; exact (p x).2.trans (by linarith only [hv,hB,norm_snd_le (T x)])
lemma turn_F (C α:ℝ)(h: 0≤ C)(p:0 < α):∃ q ε:ℝ,0< q∧0< ε∧∀ (T D: Ψ→ₗ[ℂ]Ψ),(∀ i:Sum J I,‖(T (Tκ i)).1-(D (Tκ i)).1‖≤ ε)→(∀ i:I,‖(T (0,U i)).2- (D (0,U i)).2‖ ≤ ε)→(∀ i:J, ‖(T (W i,0)).2- (D (W i,0)).2‖ ≤ C)→(∀ x:Ψ, α*‖x.1‖ ≤ ‖(D x).1‖ ∧ α*‖x.2‖ ≤‖(D x).2‖)→∃ G:Ψ ≃ₗ[ℂ] Ψ,G.toLinearMap=T ∧ ∀ x, ‖G.symm x‖ ≤ q*‖x‖:=by
 let C':= C *ρθ W; have h':0 ≤ C':=mul_nonneg h (μp_pos W|>.le)
 obtain ⟨q,ε,hq,v,Θ⟩:=ε_shear C' α p h'; let r:=ρθ Tκ; let t:=ρθ U; have ht:0<t:=μp_pos U; have hz:0<r:=μp_pos Tκ
 let z:= ε /(r+t); have hh:0<z:=div_pos v (add_pos hz ht); refine ⟨q,z,hq,hh,fun T D hb hT pB hc=>?_⟩
 have hf(x):‖x‖≤q*‖T x‖:=by
    obtain ⟨a,b⟩:= closer_S W U T D C z α h hh.le hb hT pB hc x
    have he: z*(r+t)= ε:= div_mul_cancel₀ _ (ne_of_gt (add_pos hz ht)); apply Θ ‖x‖ ‖x.1‖ ‖x.2‖ ‖T x‖ (norm_nonneg _) (Prod.norm_def _)
    · exact a.trans (add_le_add_right (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le) hh.le).trans_eq he) (norm_nonneg _)) _)
    exact b.trans (add_le_add_left (add_le_add_right (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hz.le) hh.le).trans_eq he) (norm_nonneg _)) _) _)
 have hg:Injective T:= by intro x y p; have he:=hf (x-y); rw [map_sub,p,sub_self,norm_zero,mul_zero] at he; exact sub_eq_zero.mp (norm_le_zero_iff.mp he)
 let G:=LinearEquiv.ofBijective T ⟨hg,T.surjective_of_injective hg⟩; refine ⟨G,rfl,fun x=>?_⟩; have ht:=hf (G.symm x); change ‖G.symm x‖≤q*‖G (G.symm x)‖ at ht; rwa [G.apply_symm_apply] at ht
end YM.CF.Py
