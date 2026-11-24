import YM.CF.BProof.Charge.Trek

/-! Heavy terms on a Regular patch including Kept terms in the near gaps.
Taylor in NORMALIZED Color currency. NPL bounds uniform with actual magnetic choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
local notation "Cl"=> SU.group.colorScale
variable {s:Side}(K:Chart G){C w P D:ℝ}
variable (y:ℝ)(W:Argument s)(c:Clip)(p:BudgetPoint)(T:PathData SU.group)(M:ℕ)(U:Config G s)
variable (h:Ink K C y)(v:p.threshold=thresh y)(k:ValidR c p M)(ht:T.Bounds c w P D)

abbrev model (a:Tile s): Lie:= mA y • root T M a + linear T M a W
def Tall (a:Tile s) : Prop := Sum.elim (Chromic W y 1 U) (fun a=> Spread W U y (pulley a M)) a
lemma lamp0 (a:Tile s): Tall y (0:Argument s) M (mag y) a:=by
 have he(b:Bond s): Tone (0:Argument s) y b (mag y):=by refine ⟨?_,?_,?_⟩; rw [cd_self]; have h:0<thresh y:=coin_pos ..; positivity; simpa only [Pi.zero_apply,norm_zero] using (show 0≤thresh y from (coin_pos ..).le); simpa only [Pi.zero_apply, Gauge.mat_lieExp_zero,mul_one, cd_self] using (show 0≤xi y from (coin_pos ..).le)
 cases a; exact fun i=>he _; exact fun i _=>he i
include h v
lemma direct_pay (l:Cell s) (H:Tall y W M U (.inl l)) (β:ℝ):
    let u:= SU.group.chord (faceValue U l);
    heavy c p T M β U (.inl l)= unit c β (.inl l)*(u^2/2) ∧ u≤ thresh y∧ |u-‖model y W T M (.inl l)‖|≤ predicted C y:=by
 intro u; have ht : Chromic W y 1 U l:= H; have hu:= chord_price K W y 1 U h l ht; have k:= expense (overall K W y 1 U h l ht); rw [lRead,pull_id] at hu k; rw [cd_one] at k
 refine ⟨?_,hu,k⟩; unfold heavy directQ unit; dsimp only [Sum.elim_inl]; rw [PathData.clipped, if_pos (v.symm ▸ hu)]; unfold u; ring
include ht
abbrev point (C y:ℝ)(M:ℕ):=predicted C y+2*M*Cl*thin C y
private lemma per_slot (a:Lam s)(H:Tall y W M U (.inr a))(j:Slot)(g:j∈Stack.allShort M):
    let x:=j.atSite (lRead a.1 U) (ref a).1 -- a.ref? namespace Lam access fails
    ‖x‖≤thresh y∧ ‖x-(mA y • mark a.1 j.plaq+curlP a.1 (F03.slotFace j (ref a).1) W)‖≤point C y M:=by
    let V:= lRead a.1 U; let v:= (ref a).1; let q:= F03.slotFace j v; let l:= SU.group.curvature (faceValue V q); let t:=thresh y; let e:=mA y • mark a.1 j.plaq+curlP a.1 q W
    let w:= travel V v j.walk; have hq:= spread_walk W U y K h a M H j g; have he:= chrom_slot W U y a M H j g; have hu:‖l‖≤t:= (SU.group.curvature_norm _).trans (chord_price K W y _ U h _ he)
    have hz:‖l-e‖≤ predicted C y:= (overall K W y _ U h _ he).core; have hk: ‖SU.group.adjoint w l-l‖≤2*(M*stepC C y)*(Cl*t):= adj_cost hq hu
    intro x; have he': x=SU.group.adjoint w l:= F03.atSite_path j V v; rw [he', Gauge.norm_adjoint]; refine ⟨hu,?_⟩; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ l _); apply (add_le_add hk hz).trans; unfold point t stepC thin; apply le_of_eq; ring
include k
lemma high_quality (a:Lam s)(H:Tall y W M U (.inr a)) (β:ℝ):
    let u:= ‖Pressure.shorten T M 1 (lRead a.1 U) (ref a)‖;
    heavy c p T M β U (.inr a)= unit c β (.inr a)*(u^2/2)∧ u≤ P *thresh y ∧ |u-‖model y W T M (.inr a)‖| ≤ P*point C y M:=by
    intro u; refine ⟨?_,?_⟩; unfold heavy unit higher; dsimp only [Sum.elim_inr]; rw [Pressure.trunk,if_pos (stays W U y p c a M H v K h k)]
    let r:=(ref a).1; let q(j:Slot):= j.atSite (lRead a.1 U) r; let e(j:Slot):= mA y • mark a.1 j.plaq+curlP a.1 (F03.slotFace j r) W; let J:=Stack.allShort M; let F :=coeff T a.2.1
    have e' (g:Slot→Lie){t:ℝ}(v:0≤t)(p:∀ j∈J,‖g j‖≤t) : ‖∑ j∈J,F j • g j‖≤ P*t:=by
       apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (grouped_cost c T M ht a.2.1) v); rw [sum_mul]; exact sum_le_sum fun j h=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (p j h) (norm_nonneg (F j)))
    have hu:u=‖∑ j∈J,F j • q j‖:=by unfold u; rw [shorten_data c T M _ ht]; rfl
    have hp(j)(z:j∈J):=per_slot K y W c p T M U h v ht a H j z -- tune order
    let D:=model y W T M (.inr a); have he:D=∑ j∈J,F j • e j:=by
       change mA y • glow T M a.1 a.2.1+_=_; change mA y • _+ray T M a W=_; rw [glow,rays]; unfold e; rw [Finset.smul_sum]; simp_rw [smul_add,sum_add_distrib]; congr 1; exact sum_congr rfl fun i _=> smul_comm ..
    rw [hu,show model y W T M (Sum.inr a)=_ from he]; refine ⟨e' q (coin_pos ..).le (fun j v=> (hp j v).1),?_⟩; apply (abs_norm_sub_norm_le ..).trans; rw [← sum_sub_distrib]; simp_rw [← smul_sub]; apply e' (fun j=> q j-e j) _ (fun j h=>(hp j h).2); unfold point predicted fourBill paper thin; have h0:= Cl -- delete
    have hv:= SU.group.colorScale_pos; have hx:=h.up; have hg:0<aA y:=coin_pos ..; have ht:0<thresh y:=coin_pos ..; positivity

abbrev value (a:Tile s):= Sum.elim (fun p:Cell s=> SU.group.chord (faceValue U p)) (fun a:Lam s=> ‖Pressure.shorten T M 1 (lRead a.1 U) (ref a)‖) a
abbrev rough (P y:ℝ):=(P+1)*thresh y
abbrev thinly (P C y:ℝ)(M:ℕ) := (P+1)*point C y M
lemma issue (a:Tile s)(H:Tall y W M U a)(β:ℝ)(hb:0≤β):
    let d:=unit c β a; let u:=value T M U a; 0≤d∧0≤u ∧ heavy c p T M β U a=d*(u^2/2)∧ u≤rough P y∧ |u-‖model y W T M a‖|≤thinly P C y M :=by
    have hC:=h.up; have ht':0 < thresh y:=coin_pos ..; have hu:0≤thin C y:=by unfold thin; have : 0<aA y:=coin_pos ..; positivity
    have hk:=SU.group.colorScale_pos; have hP:0≤P:=Push.AbsoluteSums.budget_nonneg ht.four; have hx:0≤predicted C y:=by unfold predicted fourBill paper; positivity
    have hp:0≤point C y M:=by unfold point; positivity -- tune
    cases a with
    | inl a=> obtain ⟨g,u,p⟩:=direct_pay K y W c p T M U h v a H β; exact ⟨mul_nonneg hb c.quadratic_pos.le, SU.group.chord_nonneg _,g, u.trans (le_mul_of_one_le_left ht'.le (by linarith)), p.trans (le_trans (b:=point C y M) (by unfold point; exact le_add_of_nonneg_right (by positivity)) (le_mul_of_one_le_left hp (by linarith)))⟩ -- tune
    | inr a=> obtain ⟨g,u,p⟩:=high_quality K y W c p T M U h v k ht a H β; refine ⟨mul_nonneg hb share_pos.le,norm_nonneg _,g,u.trans (by unfold rough; gcongr; linarith),p.trans (by unfold thinly; gcongr; linarith)⟩
end YM.CF.BProof.Charge.Form
