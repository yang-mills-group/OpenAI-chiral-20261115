import Anomaly.Gab.Rush
import YM.CF.Brood.Rink
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T:ℝ}{z:ℂ} {P:ArmorK}
namespace SketchA
variable {P:ArmorK}
abbrev Φframe (F:I→ ArcΦ)(H Q:ℝ)(L:Side):= B.constr ℂ (fun i:I=> ((↑(chipH L Q (pκ.color i)):ℂ)⁻¹) • pκ.space H (F i))
abbrev Gain₀ (v0 v1 v2 A u q:ℝ)(L:Side):Prop:= ∀ (V Y:BudgetPoint)(z:ℂ)(H Q w K C:ℝ),Melon L V Y z H Q A w →∀ F G:I→ArcΦ,∀ x':I→ℂ,(∀ i,Markup L V Y z H Q A w K C v0 v1 v2 (F i) (G i) 0 (x' i)) → (∀ i,pκ.space H (F i)= (Q:ℂ) • (B i))→ (∃ E':E ≃ₗ[ℂ] E,E'.toLinearMap=pκ.Φframe G H Q L ∧∀ x: E, ‖E'.symm x‖ ≤ q*‖x‖) ∧∀ i,|κprobe mintR L H (A*Q) w z (F i)|≤ u*coin_Z pκ L Q (Sum.inl i)
lemma litFour (t:glen_K P T ε) (h:αsmall L A ≤1)(u:FadeC P.g0 P.g1 P.g2* αsmall L A ≤ ε) : Gain₀ ιBuild4 P.g0 P.g1 P.g2 A (3*MF+1) T L:=by
 intro V Y z H Q w K C p F G x g' u'
 have hG(i:Ξθ):F i=cue_Φ Q H i:= bite_Φ H (zero_lt_one.trans_le p.earn) _ _ (g' i).shape (Swell.sCap ..) ((u' i).trans (ιBuild4.yoga H Q (zero_lt_one.trans_le p.earn) i).symm) -- tune Name.sCap
 have hw:= fun i=> (g' i).shape'
 have he: Frame_C L Q H G hw=ιBuild4.Φframe G H Q L :=congrArg (Gior.constr ℂ) (funext fun i=> (sluice H _ (G i) (hw i)).symm)
 constructor
 · rw [←he]; exact torch V Y L z w Q H A p.seam p.rank p.earn p.grab G hw _ _ _ p.pay (fun i=>by rw [←hG]; exact (g' i).receipt) T ε h u t.punch p.holder p.buckle -- check binder
 intro i; rw [hG]; refine (sold_ζ L z w Q H A p.seam p.rank p.earn p.grab p.pay i).2.2.trans ?_; change _ ≤ (3*MF+1)*chipH L Q i; rw [add_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_right h (chipX _ _ p.rank i).le) _
variable (x y:ArcΦ)(u:Melon L X Y z H Q A w)(a:Iβ) (T₀:Markup L X Y z H Q A w K C v0 v1 v2 x y 0 (0:ℂ)) -- drop T₀
local notation "iA"=> Sum.inl (β:=Iδ) a
local notation "Ω"=> chipH L Q (iA)
local notation "ℓ"=> ((L.val:ℝ)⁻¹)
local notation "ι"=>ιBuild3
variable (r:ℂ)(Yκ:Markup L X Y z H Q A w K C v0 v1 v2 x y 0 r) (Vκ:ιBuild3.space H x=(Q:ℂ) • Bθ a)
include u Yκ Vκ
lemma κtriple(p:|v1| * (far_C A *ℓ)≤ ε) (v:far_C A*ℓ≤1):
 -- normalized violet exactly assessed.Close
 ‖(↑Ω:ℂ)⁻¹ • ρDream H y-z • Bθ a‖ ≤ ε ∧ |κprobe mintR L H (A*Q) w z x| ≤ (MF+2)* Ω:=by
 let c:= cue_Φ Q H iA; have h:=u.rank; have h_:= zero_lt_one.trans_le u.earn; have hc:(x).2.1=c.2.1:= tote_Φ _ h_ _ _ Yκ.shape (Swell.sCap ..) (Vκ.trans (ιBuild3.yoga H Q h_ a |> .symm)) -- tune .. parsing
 have hp:= Yκ.receipt; let V:= H^2; let U:= Vera L X Y z; have he: ζVtap L z x= (tune_Φ Ω H (U (Gior iA))).2.1 :=by
    change _= (tune_Φ Ω H (U _)).2.1
    rw [←dyedΨ,ζVtap,hc]
 let R:= (recolor y H (Ω) Yκ.shape')-U (Gior iA)
 have hx:= chipX L Q u.rank iA; obtain ⟨h0,h1⟩:=between_L L
 obtain ⟨p₁,p₂,p₃,p₄⟩:= Markup.crops u Yκ
 have hv : ‖z‖*‖x.2.1‖*H^2≤ MF*Q :=by
    rw [hc,mul_assoc,show _=Q*‖(Gior iA).1‖ from (norms_t (Gior iA) _ _ h h_).1]; refine (mul_le_mul u.seam (mul_le_mul_of_nonneg_left ((norm_fst_le _).trans (basis_D (iA))) h.le) (mul_nonneg h.le (norm_nonneg _)) (Real.exp_pos _).le).trans_eq ?_; unfold MF; ring
 constructor
 · apply le_of_mul_le_mul_left _ hx
   have ht : R.1= (↑Ω:ℂ)⁻¹ • ρDream H y - z • Bθ a:=by unfold R; rw [←sluice, Bθ_i]; rfl
   rw [←ht,← (show ‖(tune_Φ Ω H R).2.1‖*H^2=_ from (norms_t R Ω H hx h_).1), mul_comm _ ε] -- RHS ε*Ω.
   have hf: tune_Φ Ω H R = y-tune_Φ Ω H (U (Gior iA)) :=by unfold R; rw [map_sub,release_h _ _ _ h_ hx]; --
   rw [hf]; change ‖y.2.1-_‖*H^2 ≤_; rw [←he]; refine hp.violet.trans ((le_abs_self _).trans ?_); rw [abs_mul]; refine (mul_le_mul_of_nonneg_left (Markup.pale_bound u Yκ) (abs_nonneg _)).trans ?_
   apply le_trans ?_ (mul_le_mul_of_nonneg_right p hx.le)
   change |v1| * (far_C A*(Q*ℓ^5))≤ |v1| * (far_C A*ℓ)*(Q*ℓ^3); have hz:=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0.le h1 (show 4≤5 by decide)) (mul_nonneg h.le (mul_nonneg (abs_nonneg v1) (far_ge A)))
   nlinarith only [hz]
 unfold κprobe mintR; apply (abs_add_le ..).trans; rw [abs_of_nonneg (by have hA:=u.grab; positivity : 0≤ ℓ^4*_+ℓ^3*_+ℓ^4*_+ ℓ^5*(A*Q))]
 refine (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left p₁ (pow_nonneg h0.le _)) (mul_le_mul_of_nonneg_left hv (pow_nonneg h0.le _))) (mul_le_mul_of_nonneg_left p₃ (pow_nonneg h0.le _))) le_rfl) u.pay).trans ?_
 have hL:ℓ^5≤ℓ^4:=pow_le_pow_of_le_one h0.le h1 (by norm_num); have hA:=u.grab; have he:=far_ge A
 change _ + ℓ^5*(A*Q)+Q*ℓ^5≤ (MF+2)*(Q*ℓ^3)
 have hz :far_C A * ℓ^4*Q ≤ Q*ℓ^3:= (Eq.le (show _=far_C A*ℓ*(Q*ℓ^3) from by ring)).trans (mul_le_of_le_one_left (by positivity) v)
 have hX: 0 ≤ εKo A:=by have ht:0 ≤ paceY:=zero_le_one.trans paceY_paid; unfold εKo; positivity
 unfold far_C at hz; rw [abs_of_nonneg hA] at hz
 nlinarith only [hz,mul_le_mul_of_nonneg_right hL (mul_nonneg hA h.le),mul_le_mul_of_nonneg_left hL h.le,mul_nonneg (mul_nonneg hX h.le) (pow_nonneg h0.le 4), mul_nonneg h.le (pow_nonneg h0.le 3)]
omit u Yκ Vκ
-- smaller.P θ3 payer
abbrev ρFront:= ↑mind_B
abbrev τCores (δ T:ℝ): Prop:=∀ (F G: ρFront→ₗ[ℂ]ρFront),(∀ i:Iβ,‖F (Bθ i)-G (Bθ i)‖≤δ)→(∀ x,Real.exp (-1)*‖x‖ ≤ ‖G x‖)→∃ M:ρFront ≃ₗ[ℂ]ρFront,M.toLinearMap=F ∧∀ x, ‖M.symm x‖≤ T*‖x‖
lemma turns_T :∃ δ T:ℝ,0<δ∧0<T∧τCores δ T:=by
 let a:=Real.exp (-1); have h:0<a:=Real.exp_pos _; let T:=ρθ Bθ; have ht:0<T:=μp_pos _; let d:=a/(2*T); let K:= a/2; have hp:0<K:=by unfold K; positivity
 refine ⟨d,K⁻¹,div_pos h (by positivity),inv_pos.mpr hp,?_⟩; intro F G p q
 have hz(x): ‖x‖≤ K⁻¹*‖F x‖:=by
    have hP:= q x; have hh:‖F x-G x‖≤ d*T*‖x‖:=perk_l Bθ (F-G) d (by unfold d; positivity) p x
    have he: ‖G x‖- ‖F x‖≤ ‖F x-G x‖:= (norm_sub_norm_le ..).trans_eq (norm_sub_rev ..); have hf:d*T=K:=by unfold d K; field_simp
    rw [hf] at hh; apply (le_inv_mul_iff₀ hp).mpr; change a*‖x‖≤ _ at hP; unfold K at hh ⊢; nlinarith only [hP,hh,he]
 have hb: Injective F:=by
    intro x y p; have hc:=hz (x-y); rw [map_sub,p,sub_self,norm_zero,mul_zero] at hc; exact sub_eq_zero.mp (norm_le_zero_iff.mp hc)
 let A:= LinearEquiv.ofBijective F ⟨hb,F.surjective_of_injective hb⟩; refine ⟨A,rfl,fun x=>?_⟩; have ht:= hz (A.symm x); change ‖A.symm x‖ ≤ K⁻¹*‖A (A.symm x)‖ at ht; rwa [A.apply_symm_apply] at ht
lemma litThree (δ:ℝ)(t:τCores δ T)(p:|v1| * (far_C A *ℓ) ≤ δ)(g:far_C A*ℓ≤1) : Gain₀ ι v0 v1 v2 A (MF+2) T L:=by
 intro X Y z H Q w K C u Fx G tx hx hu
 have he(i:Iβ):= κtriple (Fx i) (G i) u i (tx i) (hx i) (hu i) p g
 refine ⟨t _ (z • LinearMap.id) ?_ ?_,fun i=>(he i).2⟩
 · intro i; rw [Φframe, Basis.constr_basis]; exact (he i).1
 · intro x; change _≤ ‖z • x‖; rw [norm_smul]; exact mul_le_mul_of_nonneg_right u.holder (norm_nonneg _)
end SketchA
end YM.CF.Py
