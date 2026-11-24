import YM.CF.Swell.Vita
import YM.CF.Brood.Ship
import YM.CF.Swell.Stroke
import YM.CF.Mew.Tube
import YM.CF.Swell.Veil
import YM.CF.Swell.Muse
import YM.CF.Swell.Bark
import YM.CF.Neon.Hick
import YM.CF.Swell.Chill
import YM.CF.Swell.Yard
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
-- exchange ordinary anchor bank to incidence over all sites.Extra fuel.PSR.
variable {N:Side}{P:BudgetPoint} {K:ℕ}{c α Θ:ℝ}
open Py
open Neon
open Larch Oath
variable {B m: Side}{h K v:ℝ}(J:RegBudget (mid m B))
variable {I:Type}[LinearOrder I][Fintype I](O:I→ Site (mid m B))(hp:Injective (Cube.node∘ O))
local notation "ΨL"=> LabelΩ I
variable (s t:ℝ)(hP:1 ≤h)(u:s=t*hc_P)(z:0 < t) (E:Ξθ→ArcΦ) 
variable (X:Key (LabelΩ I)→ RegBudget (mid m B))(F F1:LabelΩ I→RegBudget (mid m B))(T:LabelΩ I→ ArcΦ)(B0:ℕ)(b a r:ℝ)(θp:ℕ)(D:GramM (mid m B))(L:Side)
variable (A': LabelΩ I→ ℂ)(E':Key (LabelΩ I)→RegBudget (mid m B))
open Roots
attribute [-instance] instDecidableEqLex -- same Ψ
variable (S:Stroke_V (P:=P) (h:=h) (K:=K) X (Cube.node ∘ xΞ O) F (xΞ O) b F1 L.val r a (fun j=>cue_Φ s h (tiν j)) θp T A' E')
local notation "Xκ"=> xΞ O
local notation "Ω"=> Cube.node ∘ xΞ O
-- glyph impulses
noncomputable def ζShape(U:I→BadgeΦ≃ₗ[ℂ]BadgeΦ)(s t:ℝ)(i j:LabelΩ I):ℂ:= if tiβ i= tiβ j then ζFare (U (tiβ i)) s t (tiν i) (tiν j) else 0
variable (X0:I→BadgeΦ≃ₗ[ℂ]BadgeΦ)
include hp
lemma born_C (i: LabelΩ I)(v:Key (LabelΩ I)):
 toV_C (Cube.node ∘xΞ O) (ζShape X0 s t) v i=(↑(t/s):ℂ) *Gior.equivFun ((X0 (tiβ i)).symm (Gior.equivFun.symm (fun k=>v (tagΨ (tiβ i) k)))) (tiν i) :=by
 unfold toV_C; rw [ΨM O hp, Finset.sum_map, Gior.equivFun_symm_apply,map_sum,map_sum,Finset.sum_apply,Finset.mul_sum]; apply sum_congr rfl; intro j _; unfold ζShape; rw [if_pos (show tiβ i= tiβ ((eqtag_β (tiβ i)) j) from rfl)]; unfold ζFare; rw [map_smul,map_smul,Pi.smul_apply]; -- tune geometry
 simp only [smul_eq_mul]; rw [mul_assoc,mul_comm (_:ℂ) (v _)]; rfl -- tune
include z u
lemma ζS_eq : Bijective (toV_C (Cube.node∘xΞ O) (ζShape X0 s t)):=by
 let c:ℂ:=↑(t/s); have hs:s>0:=u ▸ mul_pos z hcP_ge; have he:c≠0:=Complex.ofReal_ne_zero.mpr (div_pos z hs).ne'
 constructor
 · intro x y p; funext i; let b:= tiβ i; let X(w:Key ΨL):= Gior.equivFun.symm (fun k:Ξθ=>w (tagΨ b k)); have hx: Gior.equivFun ((X0 b).symm (X x))=Gior.equivFun ((X0 b).symm (X y)):=by
      funext j; have ht:= congrFun p (tagΨ b j); rw [born_C O hp,born_C O hp] at ht; exact mul_left_cancel₀ he ht
   have hv:= congrArg Gior.equivFun ((X0 b).symm.injective (Gior.equivFun.injective hx)); unfold X at hv; simp_rw [Gior.equivFun.apply_symm_apply] at hv; exact congrFun hv (tiν i)
 intro x; let Y(b:I):= fun j=> c⁻¹*x (tagΨ b j); let v(i:LabelΩ I):=Gior.equivFun ((X0 (tiβ i)) (Gior.equivFun.symm (Y (tiβ i)))) (tiν i)
 refine ⟨v,?_⟩; funext i; let b:=tiβ i; rw [born_C O hp]; change c * Gior.equivFun ((X0 b).symm (Gior.equivFun.symm (Gior.equivFun ((X0 b) (Gior.equivFun.symm (Y b)))))) (tiν i)= _; rw [Gior.equivFun.symm_apply_apply, (X0 b).symm_apply_apply,Gior.equivFun.apply_symm_apply]; exact mul_inv_cancel_left₀ he _
omit z u hp
-- compute direct.Rowe.needed.Em.Constraint.Acc.Eq solver maps finite matrices.
lemma optic_U(v w:LabelΩ I):tipI (fun d:Key ΨL=> toV_C Ω (ζShape X0 s t) d v) [w]= if w∈pipe_ζ Ω v then ζShape X0 s t v w else 0:=by
 let Z:=ζShape X0 s t; let F(i:ΨL)(x:Key ΨL):= Z v i*x i; have he(i):River (F i):= River.scale (north_r _) _; unfold toV_C; rw [(tip_bank _ _ (fun i (_:i∈ pipe_ζ Ω v)=> he i)).2 [w]]; let q(i):= tale_R i (s:=[w]) (by simp); have hh(i:ΨL):tipI (F i) [w]=Z v i*(if w=i then 1 else 0):= (tip_C (north_r i) _ _).trans (by simp only [q i,List.toFinset_cons,List.toFinset_nil,insert_empty_eq,singleton_inj]; rfl)
 change (∑ j∈pipe_ζ Ω v, tipI (F j) [w])= _; simp_rw [hh,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq]; first|exact rfl|skip
variable(u0 t0 Aχ:ℝ)(pD: D.p=P)(pK:P_U P b K ≤ ΘS_F s)(hΓ:2*peka_H P.power * P_U P b K ≤ ΘS_F s)
variable (hr:t0*t ≥ r+Τσο P a b K)(hz:u0*t ≥ θp*(r+Τσο P a b K)+(K+pulse_χ P K θp))(hr0: 0 ≤ r+Τσο P a b K)(hu:10 ≤P.B)(hl:1<L.val)(p0:0 ≤ u0)
include S pD pK hΓ hr hz hr0 hu hl u z p0 hP hp
lemma launchQ :∃ C:(LabelΩ I→ LabelΩ I→ℂ), let J:= toV_C (Cube.node∘xΞ O) C; Bijective J∧(∀ z∈hill ΨL,‖J z‖≤1/2)∧ Leaf_R D O (dry_C (E' ∘ J)) 0 h u0 t0 t L:=by -- Leaf_R expects O:I. correct pD
 let q(i:I)(v):= T (tagΨ i v)
 have hs:0<s:=u ▸ mul_pos z hcP_ge
 have he(i v): InΦ (q i v):=infΚ (h:=h) s (q i) (fun j=> claim_T (X:=D) _ _ L hl _ _ (pD ▸ S.bump (tagΨ i j)) (pD ▸ hu) (zero_le_one.trans hP)) v
 choose U t' f using fun i:I=> Δquo s hs hP (q i) (fun j=> ⟨((S.lure (tagΨ i j)).1).trans pK, ((S.lure (tagΨ i j)).2).trans hΓ⟩) (he i)
 let C:=ζShape U s t; let J:=Roots.toV_C (Cube.node∘xΞ O) C
 have hP0(i:ΨL)(l: ΨL)(p:l∈pipe_ζ Ω i): ‖C i l‖ ≤ κc s t:=by
    have hw: ((tiβ l)=tiβ i):= hp (mem_filter.mp p).2; unfold C ζShape; rw [if_pos hw.symm]; exact Φfrost s t hs hP z (q _) (he _) _ (t' _) (f _) u.symm _ _
 have hk(i: ΨL): ∑ j∈pipe_ζ Ω i, κc s t ≤ (1/2:ℝ):=by rw [ΨM O hp,Finset.sum_const,Finset.card_map,Finset.card_univ,nsmul_eq_mul]; let b:= tiβ i; exact duty_L s t hs hP z (q b) (he b) _ (t' b) (f b) u.symm
 have ha(z:Key ΨL)(v:z∈hill ΨL)(i): ‖J z i‖ ≤1/2:=(norm_sum_le ..).trans ((sum_le_sum fun j p=>by rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hill_i.mp v _)).trans (hP0 i j p)).trans (hk _))
 have htZ(z:Key ΨL)(v:z∈hill ΨL):J z∈hill ΨL:=hill_i.mpr (fun i=> (ha z v i).trans (by norm_num)); have ht:J 0=0:= funext fun i=> sum_eq_zero fun _ _=>mul_zero _
 let F'' : Key ΨL→ _:=dry_C (E' ∘ J)
 refine ⟨C,?_,?_⟩ -- let
 · exact ζS_eq O hp s t u z U
 refine ⟨fun z h=> (pi_norm_le_iff_of_nonneg (by positivity)).mpr (ha z h),?_,?_,fun i=>?_,fun i=> ?_,fun i=>?_⟩
 · change F'' 0=0∧_; rw [show F'' 0=E' 0 from (if_pos roots).trans (congrArg E' ht)]; exact ⟨S.at0,rfl⟩
 · intro z'; rw [pD]; have ht:0≤ u0*t:= mul_nonneg p0 z.le; constructor; swap; · exact ⟨⟨0,fun i=>Vale.rinsed ..,fun i=>by simpa [BudgetPoint.mass]⟩,fun _ h=>h.elim⟩
   by_cases p:z'∈hill ΨL
   · change IncX _ (F'' z') _ _ _; rw [show F'' z'=E' (J z') from if_pos p]; obtain ⟨V,v,w⟩:=(S.sold _ (htZ z' p)).weight; exact ⟨⟨_,v,fun i=> (w i).trans hz⟩,fun _ h=> h.elim⟩
   change IncX _ (F'' z') _ _ _; rw [show F'' z'=0 from if_neg p]; exact ⟨⟨0,fun i=>Vale.rinse ..,fun i=>by simpa [BudgetPoint.mass]⟩, fun _ h=> h.elim⟩
 · have he(z:Key ΨL)(u:z∈hill ΨL):F'' z i= E' (J z) i:= congrFun (if_pos u) i
   refine ⟨fun z hz v t h=>?_ ,fun x=> (port_C _ ((S.lit i).2 x) J (coin_R Ω C) (by norm_num: (1/2:ℝ)<1) ha).cong (fun z hz=> congrFun (he z hz) x) ⟩
   change F'' z i=F'' v i; rw [he z hz,he v t]; exact (S.lit i).1 _ (htZ z hz) _ (htZ v t) (fun k hv=> sum_congr rfl fun j p=>by rw [h j (((mem_filter.mp p).2 ▸ hv))])
 · refine ⟨fun _ _ _ _ _=>rfl,fun _=> zeroR _⟩
 · let bv:=tiβ i; let Z(v):= tagΨ bv v
   have hx(v:Ξθ):= S.bump (Z v); let V:ArcΦ:=cue_Φ t h (tiν i); let W(v:Ξθ):= C (Z v) i
   have hh:0 ≤ h:=zero_le_one.trans hP
   have pK : νTip F'' i=∑ j:Ξθ,W j • νTip E' (Z j):=by
      funext q t; let D(z:Key ΨL):= E' z q t
      change tipI (fun z=> F'' z q t) [i]= _; rw [show tipI (fun z=>F'' z q t) [i]=tipI (D ∘ J) [i] from (lace_C _ (show Set.EqOn (fun x=>F'' x q t) (D ∘ J) (hill ΨL) from fun z h=>congrFun (congrFun (if_pos h : F'' z= E' (J z)) q) t) roots),Mew.cane D ((S.lit q).2 t) J (coin_R Ω C) (by norm_num:(1/2:ℝ)<1) ha ht i]
      rw [←sum_subset (subset_univ (pipe_ζ Ω i))]; swap; · intro j _ t; rw [optic_U O _ _ U,if_neg,zero_smul]; exact fun h=>t (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.symm⟩)
      rw [ΨM O hp,Finset.sum_map, Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j p; rw [optic_U O _ _ U, if_pos]; swap; · exact mem_filter.mpr ⟨mem_univ _,rfl⟩
      rfl

   change Axon _ _ D.p (νTip F'' i) _ _ V; rw [pK,pD,show V= ∑ j:Ξθ,W j • (cue_Φ s h j+ q bv j) from ?_]; swap; · refine Eq.trans (Θport s t hs hP z (q bv) (he bv) (U bv) (t' bv) (f bv) u.symm (tiν i)).symm ?_; refine sum_congr rfl fun j _=>?_ ; unfold W C ζShape; rw [if_pos (show tiβ (Z j)= tiβ i from rfl)]; rfl
   refine turf_A L.val (O bv) P _ _ _ _ ?_ (wave_F univ _ _ _ P L.val (O bv) (fun j _=>charge_ν (W j) L.val _ _ _ _ (r+Τσο P a b K) hh (hx j)) hh) -- bv shadow earlier.
   refine le_trans ?_ hr; rw [←sum_mul]; apply mul_le_of_le_one_left hr0; refine le_trans (sum_le_sum (fun j (_:j∈(univ:Finset Ξθ))=> hP0 _ _ ?_)) ?_; exact mem_filter.mpr ⟨mem_univ _,rfl⟩; -- hk
   have ht:=hk i; rw [ΨM O hp,Finset.sum_map] at ht; exact ht.trans (by norm_num)
end YM.CF.Swell
