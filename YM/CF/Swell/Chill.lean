import YM.CF.Swell.Lawn
import YM.CF.Swell.Hush
import YM.CF.Swell.Bark
import YM.CF.Swell.Tap
import YM.CF.Swell.Fist
import YM.CF.Mew.Tube
import YM.CF.Pso.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow Py
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N B m L:Side}
variable {r:ℕ}
variable {I:Type}[Fintype I][LinearOrder I]
variable {P:BudgetPoint}(E':GramM (mid m B))
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Wilson Precision Next.Free Gauge Paige Vault Brace Spire Pressure Jade Oise
variable {A:Teller SU.group}{W:ChartRatio SU.group}{Zp:Patch}(D:Grace A Zp W){d e g x b a t u0 K Kt f l α s':ℝ}
-- Header gifts Aux clock. Need IncX at **boosted** Stamp. applies unconditionally Contact_Q for all such E (mask-reduced Cap). θ boost=11.
abbrev leaseΓ(P:BudgetPoint):ℝ:=P.supportExponent+8
abbrev θG(P:BudgetPoint):ℝ:=P.supportExponent+10
def PoseΓ(P: BudgetPoint): BudgetPoint:={P with supportExponent:=P.supportExponent+12, exponent_pos:=add_pos P.exponent_pos (by norm_num)}
variable (Av:RegBudget N)(p:IncX (fun _=>False) Av (PoseΓ P) a t)(h:0≤a)
abbrev ECost(P:BudgetPoint):= Vow.chi_f P.order * feeU P.B 1
include p h
lemma grow_κ(X:Scree.Hub N)(q:PressB (PoseΓ P) X (Av X) a K):PressB P X (Av X) a K:=by obtain ⟨x,y,z,u,v,h,w,q⟩:=q; exact ⟨x,y,z,u,v,h,fun i j k=>⟨(w i j k).grade,(w i j k).paid,(w i j k).token⟩,q⟩
lemma touch_Γ :IncX (fun _=> False) Av P a t:=by
 obtain ⟨v,x,z⟩:=p.weight; let F:= fun i=> grow_κ Av p h i (x i); refine ⟨⟨v,F,fun i=>?_⟩, fun s h=> h.elim⟩; refine le_trans ?_ (z i); refine sum_le_sum ?_; intro k v; split_ifs; swap; rfl
 exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (Nat.cast_nonneg _))) ((Taxi.eraF _ _ (F k) h _ (ping_f P _)).grade)
lemma head_ψ : ∃ (E:Aura N→ Copy N)(V:Aura N→ℝ),(∀ i:Aura N, Span_K P a i (E i) (V i)) ∧ Bake.Turf E ∧ (∀ i:Seat N,nook (V*loom_v (leaseΓ P) 1 (widthK N P.B) 0) i ≤ ECost P*t) ∧∀ i:Orbit N,Rue.FleetS P.threshold i.1→flags P.threshold i.1=∅→ exponentL P Av i.1=∑ Y:Aura N,E Y i:=by
 obtain ⟨G,g,hx⟩:=p.weight; let F:=fun i=> grow_κ Av p h i (g i); let E(Y:Aura N):=∑ y∈ Ione.web0 Y,oV (Av y); let κ:=chi_f P.order; let T (Y:Aura N):=∑ y∈Ione.web0 Y,κ*G y; have he(k:Scree.Hub N)(i:Aura N)(q:k∈Ione.web0 i): k.val.2=i.val:=congrArg Subtype.val (mem_filter.mp q).2
 have ht(i:Seat N): Λpay P.B (leaseΓ P) i (fun k:Scree.Hub N=>k.val.2) G ≤ feeU P.B 1*t:=by
    have hG(j):0 ≤ G j:=(Taxi.eraF _ _ (F j) h _ (ping_f P _)).grade; let L(k:Scree.Hub N):=k.val.1; have h0:0 ≤ t:= le_trans (sum_nonneg (s:=univ) (fun j _=> by split; exact mul_nonneg (Real.exp_pos _).le (hG j); exact le_rfl)) (hx i)
    refine town_U (P:=P) L _ G h0 hG (fun k=>k.property) _ _ (fun y=>?_)
    refine le_trans ?_ (hx y); unfold χbank; rw [sum_filter]; apply sum_le_sum; intro k _; unfold L; split_ifs with g' u v; apply mul_le_mul_of_nonneg_right _ (hG _); apply Real.exp_monotone; apply mul_le_mul_of_nonneg_right; unfold PoseΓ leaseΓ; dsimp only; linarith; exact Nat.cast_nonneg _; exact False.elim (u g'.symm); exact False.elim (g' v.symm); rfl
 refine ⟨E,T,(fun Y=>Medal.sumP _ _ _ fun k p=>he k Y p ▸ rimR (F _) h),fun i V T=>by unfold E; rw [Finset.sum_apply,Finset.sum_apply],fun i=>?_ ,fun i g v=>?_⟩
 · rw [ECost,mul_assoc]; apply le_trans _ (mul_le_mul_of_nonneg_left (ht i) (Vow.spicy_f ..)); unfold Λpay; rw [←sum_fiberwise_of_maps_to (s:=univ.filter (fun k:Scree.Hub N=>i∈k.val.2)) (t:=Cadre.spark i) (g:=lagE) (fun k u=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp u).2 ⟩),mul_sum]; apply sum_le_sum; intro X u; unfold T; -- inside `(T*...) X`
   rw [Pi.mul_apply,sum_mul,Finset.mul_sum]; refine le_of_eq ?_; refine sum_congr ?_ (fun j p=>?_ )
   · unfold Ione.web0; ext j; simp only [mem_filter,mem_univ,true_and]; refine ⟨fun p=>⟨by change i∈(Bake.lagE j).val; rw [p]; exact (mem_filter.mp u).2,p⟩, And.right⟩
   dsimp only; rw [he j X (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩)]; change κ* _*Real.exp ((leaseΓ P-1*0)*_)=_; unfold κ widthK Trees.currency; rw [mul_zero, sub_zero]; ring
 unfold exponentL E; simp_rw [show ∀ k:Scree.Hub N,numbE P.threshold k.val.2 (Av k) i.1=_ from fun k=> (show _= Av k i.1 from Set.indicator_of_mem (show i.1∈_ from Leaf.lush_K i g v k.val.2) _), Finset.sum_apply]; exact (sum_fiberwise_of_maps_to (s:=univ) (fun i _=>mem_univ _) _).symm -- tune
omit p h
-- Tax economics buys at P active.Stamps. Fee burden local. choose moment thresholds after L/postx. explicit products and budgets.
variable (σ:I→ Seat N)(M:I→ Bag N)(V:I→ Aura N→ℝ) (b d H:ℝ) {k' t':ℕ}(σp:∀ z:Seat N,(univ.filter fun i=>σ i=z).card ≤ t')(pG:∀ i, Blip_o (σ i) (M i) (V i) P k' H b (θG P))
abbrev Cu_μ(P:BudgetPoint)(t':ℕ)(b:ℝ):=2*feeU P.B t'*b
abbrev Ξ₂ (P:BudgetPoint)(i t':ℕ)(b:ℝ) := μReq P.B i*(Cu_μ P t' b)
abbrev Λhop(F:Aura N→ℝ)(n:ℕ):=fun i:Aura N=> (i.val.card:ℝ)^n*F i
variable{w:ℝ}
open Larch
lemma fuse_Q {s:ℝ} (h:0 ≤ s) (F:Aura N→ℝ)(hf:0≤F)(T:ℝ)(p:t+1 ≤ T)(i n): nook (Λhop F n*loom_v t w (widthK N P.B) 0) i ≤ μReq P.B n*nook (F*loom_v T w (widthK N P.B) 0) i:=by -- tune w
 unfold Cadre.nook; rw [mul_sum]; apply sum_le_sum; intro j q; let Q:= widthK N P.B
 have he:= hD_Q (P:=P) t T j p n -- check signature
 change _ ≤ μReq P.B n*(F _*Real.exp ((T-w*0)*_)); change (j.val.card:ℝ)^n*F _*Real.exp ((t-w*0)*_) ≤ _; unfold loom_v at he; simp_rw [mul_zero] at *; exact (Eq.le (show (j.val.card:ℝ)^n*F j*_=F j*(κRoom P.B j^n*Real.exp ((t-0)*Q j)) from (by unfold κRoom; ring))).trans ((mul_le_mul_of_nonneg_left he (hf _)).trans_eq (mul_left_comm ..)) -- T association
include σp pG
structure NeedU(P:BudgetPoint)(b b₁ K:ℝ)(t':ℕ):Prop where
 cost : 0 ≤ b
 cash: ECost P*b₁ < K
 high: 0<K
 debt: Sour.spanV P.B*(Cu_μ P t' b+2*K*Ξ₂ P 1 t' b) ≤ 1
 share: Cu_μ P t' b+Ξ₂ P 1 t' b*K+Ξ₂ P 2 t' b*K*K < (1-Sour.spanV P.B*(Cu_μ P t' b+2*K*Ξ₂ P 1 t' b))*K
lemma eatU (W:Aura N→ Copy N) (Jx:Aura N→ℝ)(hE:∀ i,Span_K P H i (W i) (Jx i))(hr:1 ≤ H)(hp:∀ i:Seat N,nook (Jx*loom_v (leaseΓ P) 1 (widthK N P.B) 0) i ≤ ECost P*f)(TQ:NeedU P b f K t') : Tax_R (V_S (Leaf.σ_H (κsum V)) Jx) (Leaf.σ_H (κsum V)) (widthK N P.B) (Sour.spanV P.B) (leaseΓ P) 1 K (Cu_μ P t' b) (Ξ₂ P 1 t' b) (Ξ₂ P 2 t' b):=by
 let B:=P.B; let A:= leaseΓ P; let Γ:=Leaf.σ_H (κsum V); let T:= V_S Γ Jx
 have hz:0 ≤ Γ:=fun k=> mul_nonneg (by norm_num) (sum_nonneg fun j _=> (pG j).chant.weight _)
 have hT(o:Seat N):nook (Γ*loom_v (A+1) 1 (widthK N P.B) 0) o ≤ Cu_μ P t' b:=by
    have ht':(A+1)+1 ≤θG P:=by unfold A leaseΓ θG; linarith
    have hh:= vΨ σ σp M V pG o (A+1) ht' TQ.cost; rw [show loom_v (A+1) 1 (widthK N P.B) 0=loom_v (A+1) 0 (widthK N P.B) 0 from funext fun i=> by simp [loom_v]]; exact hh
 have hf:0 ≤ Cu_μ P t' b:= by refine le_trans ?_ (hT (0:Seat N)); exact sum_nonneg fun i _=>mul_nonneg (hz i) (show 0≤ loom_v (A+1) 1 (widthK N P.B) 0 i from (Real.exp_pos _).le)
 have hpw(n o): nook (Λhop Γ n*loom_v A 1 (widthK N P.B) 0) o ≤ Ξ₂ P n t' b:= (fuse_Q (t:=A) (s:=0) le_rfl Γ hz _ le_rfl _ n).trans (mul_le_mul_of_nonneg_left (hT o) (show 0 ≤ μReq P.B n from (by unfold μReq Sour.spanV; positivity))) -- w inference
 have hℓ:A ≥ 2:= by unfold A leaseΓ; linarith only [P.exponent_pos];
 refine ⟨(fun X=>crown_K Γ _ _ (fun i=>(hE _).wage (zero_le_one.trans hr)) hz),hz,vigor N B,(by unfold Sour.spanV; positivity),zero_lt_one,by linarith only [hℓ],TQ.high,by unfold Ξ₂; apply mul_nonneg _ hf; unfold μReq Sour.spanV; positivity,hf,fun i=>?_ ,fun X i=>Eq.le ?_,fun i=>?_ , fun i=>?_ ,fun i=>?_ ,TQ.debt,TQ.share⟩
 · rw [show ϕV T 0 0=Jx from ?_]; exact (hp _).trans_lt TQ.cash
   funext i; unfold ϕV T; rw [car_k,V_S,bud_L,tick_r]
 · rw [trend_K]
 · exact (le_trans (sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (Real.exp_monotone (show _* widthK N P.B j ≤ _ * _ from mul_le_mul_of_nonneg_right (by linarith) (by unfold widthK; positivity))) (hz j)) (hT i))
 · apply le_trans _ (hpw 1 i); unfold nook shelfR; apply sum_le_sum; intro j _; apply le_of_eq; simp only [Pi.mul_apply,Λhop,pow_one,κRoom, Leaf.σ_H]; ring
 apply le_trans _ (hpw 2 i); unfold nook Hiκ; apply sum_le_sum; intro j _; apply le_of_eq; simp only [HiΦ,Pi.mul_apply,Λhop, Leaf.σ_H]; ring
end YM.CF.Swell
