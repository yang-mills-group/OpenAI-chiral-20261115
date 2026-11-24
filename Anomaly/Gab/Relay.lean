import YM.CF.Brood.Told
/-! adapted two-component turn for global unit row & deg-three -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {A B E F X:Type*}[NormedAddCommGroup A][NormedSpace ℂ A][NormedAddCommGroup B][NormedSpace ℂ B][NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F][NormedAddCommGroup X][NormedSpace ℂ X]
variable [FiniteDimensional ℂ A][FiniteDimensional ℂ B]
variable {J I:Type*}[Fintype J][Fintype I]
variable (W: Basis J ℂ A)
-- B first then (A,C frame). triangular full error bound. Assumed D lower bound using scales. columns.
local notation "O"=> B
local notation "Jr"=> (Sum J I)
variable (U:Basis I ℂ B)
local notation "Tκ"=> (W.prod U)
local notation "Ψ"=> (A × B)
variable (v: A × B→ₗ[ℂ]A×B)
noncomputable def urn_T_D (v:A × B→ₗ[ℂ] A × B): A × B→ₗ[ℂ] A:= (LinearMap.fst ..).comp v
def vein_Z_D (v:A × B→ₗ[ℂ]A×B): A × B→ₗ[ℂ]B:=(LinearMap.snd ..).comp v
local notation "TS"=> (LinearMap.inl ℂ A O)
local notation "QS"=> (LinearMap.inr ℂ A O)
local notation "Yt"=> (Sum J I)
local notation "ΠZ"=> (fun i:Yt=> (W.prod U) i)
lemma closer_C_D (T D:Ψ→ₗ[ℂ]Ψ) (C ε α:ℝ)(ht:0 ≤ C)(hu:0 ≤ ε)(h:∀ i, ‖(T (Tκ i)).1 -(D (Tκ i)).1‖ ≤ ε)(hz:∀ i:I,‖(T (0,U i)).2- (D (0,U i)).2‖ ≤ ε)(hk:∀ i:J, ‖(T (W i,0)).2- (D (W i,0)).2‖ ≤ C)(p:∀ x:Ψ, α*‖x.1‖ ≤ ‖(D x).1‖ ∧ α*‖x.2‖≤ ‖(D x).2‖)(x:Ψ): α*‖x.1‖ ≤ ‖T x‖ + (ε*ρθ (Tκ))*‖x‖ ∧ α*‖x.2‖≤ ‖T x‖+(ε* ρθ U)*‖x‖ + (C*ρθ W)*‖x.1‖:=by
 let z:=T-D
 let L:= vein_Z_D z
 have hp:‖(T x).1-(D x).1‖≤ ε*(ρθ Tκ)*‖x‖:=perk_l Tκ (urn_T_D z) ε hu h x
 have hv:‖(T x).2-(D x).2‖≤ ε*ρθ U*‖x‖ + C*ρθ W*‖x.1‖:=by
    change ‖L x‖≤ _; nth_rw 1 [show x=QS x.2+TS x.1 from (by ext <;> simp)]; rw [map_add]; exact (norm_add_le ..).trans (add_le_add ((perk_l U (L.comp QS) ε hu hz x.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le _) (mul_nonneg hu (μp_pos U).le))) (perk_l W (L.comp TS) C ht hk x.1))
 constructor
 · have hB:= norm_sub_norm_le (D x).1 (T x).1; have hU:‖(D x).1-(T x).1‖= ‖(T x).1-(D x).1‖:= norm_sub_rev ..; rw [hU] at hB; exact (p x).1.trans (by linarith only [hp,hB,norm_fst_le (T x)])
 have hB:= norm_sub_norm_le (D x).2 (T x).2; have hU:= norm_sub_rev (D x).2 (T x).2; rw [hU] at hB; exact (p x).2.trans (by linarith only [hv,hB,norm_snd_le (T x)])
lemma turn_U_D (C α:ℝ)(h: 0≤ C)(p:0 < α):∃ q ε:ℝ,0< q∧0< ε∧∀ (T D: Ψ→ₗ[ℂ]Ψ),(∀ i:Sum J I,‖(T (Tκ i)).1-(D (Tκ i)).1‖≤ ε)→(∀ i:I,‖(T (0,U i)).2- (D (0,U i)).2‖ ≤ ε)→(∀ i:J, ‖(T (W i,0)).2- (D (W i,0)).2‖ ≤ C)→(∀ x:Ψ, α*‖x.1‖ ≤ ‖(D x).1‖ ∧ α*‖x.2‖ ≤‖(D x).2‖)→∃ G:Ψ ≃ₗ[ℂ] Ψ,G.toLinearMap=T ∧ ∀ x, ‖G.symm x‖ ≤ q*‖x‖:=by
 let C':= C *ρθ W; have h':0 ≤ C':=mul_nonneg h (μp_pos W|>.le)
 obtain ⟨q,ε,hq,v,Θ⟩:=ε_shear C' α p h'; let r:=ρθ Tκ; let t:=ρθ U; have ht:0<t:=μp_pos U; have hz:0<r:=μp_pos Tκ
 let z:= ε /(r+t); have hh:0<z:=div_pos v (add_pos hz ht); refine ⟨q,z,hq,hh,fun T D hb hT pB hc=>?_⟩
 have hf(x):‖x‖≤q*‖T x‖:=by
    obtain ⟨a,b⟩:= closer_C_D W U T D C z α h hh.le hb hT pB hc x
    have he: z*(r+t)= ε:= div_mul_cancel₀ _ (ne_of_gt (add_pos hz ht)); apply Θ ‖x‖ ‖x.1‖ ‖x.2‖ ‖T x‖ (norm_nonneg _) (Prod.norm_def _)
    · exact a.trans (add_le_add_right (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le) hh.le).trans_eq he) (norm_nonneg _)) _)
    exact b.trans (add_le_add_left (add_le_add_right (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hz.le) hh.le).trans_eq he) (norm_nonneg _)) _) _)
 have hg:Injective T:= by intro x y p; have he:=hf (x-y); rw [map_sub,p,sub_self,norm_zero,mul_zero] at he; exact sub_eq_zero.mp (norm_le_zero_iff.mp he)
 let G:=LinearEquiv.ofBijective T ⟨hg,T.surjective_of_injective hg⟩; refine ⟨G,rfl,fun x=>?_⟩; have ht:=hf (G.symm x); change ‖G.symm x‖≤q*‖G (G.symm x)‖ at ht; rwa [G.apply_symm_apply] at ht
end YM.CF.Py
