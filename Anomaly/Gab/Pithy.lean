import Anomaly.Gab.Incept
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
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T:ℝ}{z:ℂ}
namespace SketchA
abbrev βSize(B:Basis I ℂ E):=1+ ∑ i:I, ‖B i‖
variable {P:ArmorK}{u p f:ℝ}
local notation "ι"=> Sum I Unit
local notation "ΣS"=> ρZee B
local notation "Θ" => pκ.coin_Z L Q
local notation "κρ"=> κprobe mintR L H (A*Q) w z
local notation "Lν" => ((L.val:ℝ)⁻¹)
local notation "ΠV"=> E × ℂ
def τFrame (L:Side)(Q H:ℝ)(Z: Sum I Unit→ ArcΦ × ℂ): (E × ℂ) →ₗ[ℂ] (E × ℂ):= (ρZee B).constr ℂ (fun i=> ((↑(pκ.coin_Z L Q i):ℂ)⁻¹) • pκ.winA H (Z i))
abbrev κGain (δ T q f:ℝ):Prop:=∀ (G:E≃ₗ[ℂ]E), (∀ x,‖G.symm x‖≤ T * ‖x‖) →∀ Z:ΠV→ₗ[ℂ]ΠV, (∀ i:Sum I Unit, ‖(Z (ρZee B i)).1-G ((ρZee B i).1)‖ ≤ δ)→ (∀ i: Unit, ‖(Z (ρZee B (Sum.inr i))).2 - (ρZee B (Sum.inr i)).2‖ ≤ δ)→ (∀ i:I, ‖(Z (ρZee B (Sum.inl i))).2‖ ≤ f) →∃ M:ΠV≃ₗ[ℂ] ΠV, M.toLinearMap=Z∧∀ x:ΠV,‖M.symm x‖ ≤ q *‖x‖
lemma κGold(t:T>0)(v:0≤ f):∃ δ q:ℝ,0<δ∧0<q∧ κGain (B:=B) δ T q f:=by
 obtain ⟨p,ε,u',h,P⟩:=turn_U_D B (Basis.singleton Unit ℂ) f (min T⁻¹ 1) v (lt_min (inv_pos.mpr t) zero_lt_one)
 refine ⟨ε,p,h,u',?_⟩; intro G g Z Vx Vy Vz; apply P Z (G.toLinearMap.prodMap (LinearMap.id :ℂ→ₗ[ℂ]ℂ)) (fun i=>Vx i) ?_ ?_ (fun x=>?_)
 · intro i; let H:=Vy i; rw [zee₁] at H; change ‖(Z _).2-_‖≤ε; simp -- tune
   exact H
 · intro i; have ht:=Vz i; rw [zee₀] at ht; change ‖(Z _).2 - 0‖≤ f; rw [sub_zero]; exact ht
 refine ⟨(mul_le_mul_of_nonneg_right (min_le_left ..) (norm_nonneg _)).trans ?_, mul_le_of_le_one_left (norm_nonneg _) (min_le_right ..)⟩
 change T⁻¹ * ‖x.1‖ ≤ ‖G x.1‖; rw [inv_mul_le_iff₀ t]; exact (Eq.le (congrArg norm (G.symm_apply_apply x.1)).symm).trans (g (G x.1))
-- uniform on all such parents.
abbrev Bleak(L:Side)(v0 v1 v2:ℝ)(A:ℝ): Prop := ∀ (P V:BudgetPoint)(z:ℂ)(H Q w K C:ℝ), Melon L P V z H Q A w →∀ (Z U: ArcΦ)(t x:ℂ),(Markup L P V z H Q A w K C v0 v1 v2 Z U t x) → pκ.space H Z=0 → |κprobe mintR L H (A*Q) w z Z| ≤ far_C A * (Q *((L.val:ℝ)⁻¹)^(m+1))
lemma arrester (S: Gain₀ pκ v0 v1 v2 A u T L)(Xξ: Bleak pκ L v0 v1 v2 A)
 (U:Melon L X Y z H Q A w) (v:κGain (B:=B) ε T p (|C| * u)) (hp:0≤ε)
 (pZ:paceY*|K| * (far_C A * Lν) ≤ ε) (pY:|C| * (far_C A * Lν)≤ ε) (p':far_C A* Lν≤u)
 (Z F: Sum I Unit→ArcΦ × ℂ)(h:∀ i,Markup L X Y z H Q A w K C v0 v1 v2 (Z i).1 (F i).1 (Z i).2 (F i).2) (y:∀ i,pκ.winA H (Z i)= (Q:ℂ) • (ρZee B i)) : let G:= τFrame pκ L Q H F; (∃ T:ΠV≃ₗ[ℂ]ΠV,T.toLinearMap=G∧∀ x: ΠV,‖T.symm x‖ ≤ p * ‖x‖) ∧ (∀ i,|κprobe mintR L H (A*Q) w z (Z i).1| ≤ u* pκ.coin_Z L Q i) ∧ (∀ j:Unit, |κprobe mintR L H (A*Q) w z (Z (.inr j)).1| ≤ far_C A * (Lν*Q)):=by
 intro G; let P: I→ Sum I Unit:=Sum.inl
 have hz(i:I): pκ.space H (Z (P i)).1=(Q:ℂ) • B i ∧ (Z (P i)).2=0:=by
    unfold P; let j:= Sum.inl (β:=Unit) i; have hx:=y j; rw [zee₀] at hx; refine ⟨congrArg Prod.fst hx,?_⟩; change (Z j).2 = _; rw [← smul_zero (↑Q:ℂ)]; exact congrArg Prod.snd hx
 let Tf (i):=(F (P i)).1
 obtain ⟨⟨g,q,r⟩,f⟩:= S X Y z H Q w K C U (fun i=>(Z (P i)).1) Tf (fun i=>(F (P i)).2) (fun i=>by simpa only [(hz i).2] using h (P i)) (fun i=> (hz i).1)
 have hm(i:I): G (ρZee B (P i))=(↑(pκ.coin_Z L Q (P i)):ℂ)⁻¹ • pκ.winA H (F (P i)):= Basis.constr_basis ..
 have H₀:= U.rank; let P':Unit→ Sum I Unit:=Sum.inr; obtain ⟨ha,hb⟩:=between_L L
 have he(i:Unit): pκ.space H (Z (P' i)).1=0∧ (Z (P' i)).2=(Q:ℂ):=by
    unfold P'; have ht:= y (.inr i); rw [zee₁] at ht; exact ⟨(congrArg Prod.fst ht).trans (smul_zero _),(congrArg Prod.snd ht).trans (mul_one _)⟩
 have ht(i:Unit): |κprobe mintR L H (A*Q) w z (Z (P' i)).1| ≤ far_C A * (Lν*Q):=by
    refine (Xξ _ _ _ _ _ _ _ _ U _ _ _ _ (h _) (he i).1).trans (mul_le_mul_of_nonneg_left ?_ (far_ge A)); rw [mul_comm Lν]; apply mul_le_mul_of_nonneg_left _ H₀.le; nth_rw 2 [show Lν=Lν^1 from (pow_one _).symm]; exact pow_le_pow_of_le_one ha.le hb (by omega)
 have hr: (Q:ℂ)≠0:= Complex.ofReal_ne_zero.mpr H₀.ne'
 have hD(n:ℝ)(p:n≤ ε): Q⁻¹*(n*Q) ≤ ε:=by rw [mul_comm n,inv_mul_cancel_left₀ H₀.ne']; exact p
 refine ⟨v g r G ?_ ?_ ?_,fun i=>?_,ht⟩
 · rintro (i|j)
   · rw [hm, zee₀]; change ‖((↑(chipH ..):ℂ)⁻¹ • pκ.space H (F (.inl i)).1) - g.toLinearMap (B i)‖≤_; rw [q,Φframe,Basis.constr_basis,sub_self,norm_zero]; exact hp
   let i:= P' j; have hp:=Markup.pay_Y U (h i) (ht j)
   change ‖(G (ρZee B i)).1 -_‖ ≤ _
   rw [show G (ρZee B i)=_ from (show _= (Q:ℂ)⁻¹ • pκ.winA H (F i) from Basis.constr_basis ..),zee₁]; change ‖(Q:ℂ)⁻¹ • pκ.space H (F i).1-g 0‖ ≤ _
   rw [map_zero,sub_zero,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg H₀.le]; exact (mul_le_mul_of_nonneg_left ((pκ.pace ..).trans hp) (inv_nonneg.mpr H₀.le)).trans ((Eq.le (show Q⁻¹*(paceY*(|K| * (far_C A*(Lν*Q))))=Q⁻¹*((paceY*|K| * (far_C A*Lν))*Q) from by ring)).trans (hD _ pZ))
 · intro i; let A':= P' i; have he': G (ρZee B A')=(Q:ℂ)⁻¹ • pκ.winA H (F A'):=Basis.constr_basis ..; rw [he',zee₁]; have hp:= Markup.offset_pay U (h A') (ht i); change ‖(Q:ℂ)⁻¹*(F A').2 -1‖ ≤ ε; rw [show (↑Q:ℂ)⁻¹*_ -_= (↑Q:ℂ)⁻¹*((F A').2-(Z A').2) from (by rw [mul_sub,(he i).2, inv_mul_cancel₀ hr]),norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg H₀.le]; apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr H₀.le)).trans; refine (Eq.le (show _=Q⁻¹*(|C| * (far_C A * Lν)*Q) from by ring)).trans (hD _ pY) -- rw he' match
 · intro i; let j:=P i; have hp:= Markup.offset_pay U (h (P i)) (f i)
   have hv:=pκ.coin_pos L Q H₀ j; let k:= pκ.coin_Z L Q j
   rw [(hz i).2,sub_zero] at hp; rw [hm i]; change ‖(k:ℂ)⁻¹ * _‖≤ _; rw [norm_mul,norm_inv, Complex.norm_real,Real.norm_of_nonneg hv.le]
   exact (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hv.le)).trans_eq (by change k⁻¹*(|C| * (u*k))=_; have hv:k ≠ 0:=hv.ne'; field_simp)
 cases i with
 | inl i=> exact f i
 | inr i=> exact (ht i).trans ((Eq.le (show _=far_C A* Lν*Q by ring)).trans (mul_le_mul_of_nonneg_right p' H₀.le))
end SketchA
end YM.CF.Py
