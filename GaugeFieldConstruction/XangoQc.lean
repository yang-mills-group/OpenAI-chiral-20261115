import GaugeFieldConstruction.AltaiQc
/-!
# Constant and affine contour operation existence under Bloom. Annihilator and all tests
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S) (Z:∀ v:UV five,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0)
-- permutations first slot. Π
lemma juteHeartQc (q:Equiv.Perm (Fin n)): JuteQc q 0=0:=by simp[JuteQc]
lemma juteRideQc (q:Equiv.Perm (Fin n))(i:Fin n): JuteQc q i.succ=(q i).succ:=by simp[JuteQc]
lemma juteInvQc (q:Equiv.Perm (Fin n)): (JuteQc q).symm=JuteQc q.symm:=rfl -- tune
lemma juteMarkQc (q:Equiv.Perm (Fin n))(x:Fin n→l)(b:l): Fin.cons b x ∘ JuteQc q=Fin.cons b (x ∘ q):= funext fun i=> by refine Fin.cases ?_ ?_ i <;> simp [juteHeartQc,juteRideQc]
lemma juteHeadQc (q:Equiv.Perm (Fin n))(x:Points (n+1)): helm (rearrange (JuteQc q) x)=helm x:=by simp [helm_head,rearrange_at,juteHeartQc]
lemma juteRideQc' (q:Equiv.Perm (Fin n))(x:Points (n+1)): riders (rearrange (JuteQc q) x)=rearrange q (riders x):= by ext1 i; change x (JuteQc q i.succ)=x (q i).succ; rw [juteRideQc]
-- Any uniform kills with J. Need not wait threshold. Proposition true for any measures.
def JetBillQc (K:Bills):Prop:=∀ n (q:Equiv.Perm (Fin n)) (i:Fin n)(a:Axis)(x:Points (n+1)), (K n (q i)).K a (rearrange (JuteQc q.symm) x)= (K n i).K a x
lemma JetPaperQc (i:Axis):JetBillQc (postage i):=fun _ _ _ _ _=>rfl
lemma JetAngleQc (Ω):JetBillQc (rpm Ω):=by
 intro n q i a x; simp_rw [rpm, angle,juteRideQc', rearrange_at]; rw[juteHeartQc,q.symm_apply_apply]
lemma moveDeltaQc (S:City)(K:Bills)(w:JetBillQc K)(q:Equiv.Perm (Fin n)) {b:Bulb}{i:Fin n}{t:Test n}(v:Works b t (q i))(L: Fin n→ UV five)(J:placard (UV five)):
    delta (K _ (q i)) t b v.cared (S.armed J L) = delta (K _ i) (Fathom.perm q.symm t) b (stepWorksQc q t v).cared (S.armed J (L ∘ q)):=by
 unfold delta; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro p _; unfold armed; simp_rw [tagged_cost]; rw [← S.rearr (JuteQc q), juteInvQc]; unfold Fathom.add; rw [juteMarkQc]; congr 1; ext1 x; rw [perm_app,testcut_v,w,juteHeadQc,juteRideQc',testcut_v,perm_app]
lemma reachPayQc (S:City)(K:Bills)(J:placard (UV five))(A B:l)(r : JetBillQc K)(H:∀ T:InkQc, S.tagged T.x B T.f= delta (K _ 0) T.f T.b T.h.cared (S.armed J (Fathom.add A T.x))): Reaches S J K A B:=by
 intro n x k t b v
 cases n with
 | zero=> exact Fin.elim0 k
 | succ i=>
    let s:=Equiv.swap 0 k; have e : s 0=k:= Equiv.swap_apply_left ..; let q:=perm s.symm t
    let L':=x ∘ s; let ρ:= InkQc.mk ⟨i, Fin.tail L', q⟩ b (stepWorksQc s t (i:=0) (e.symm ▸ v)); have p:=H ρ
    generalize hy: v.cared = U; rw [←e]; rw [formHwQc S s, moveDeltaQc S K r s (v:= show Works b t (s 0) from e.symm ▸ v),scale_hwQc]
    have he (z:l): update L' 0 z=Fathom.add z (Fin.tail L'):=by nth_rw 1 [←casedQc L']; exact Fin.update_cons_zero ..
    change S.spot L' 0 B q= delta _ _ _ _ (S.armed J (update L' 0 A)); rw[spot_cost,he,he,←tagged_cost]; exact p
include Z in
lemma uniqueReachQc (w : Bills)(J:placard (UV five))(A B C:l)(r:Reaches S J w A B)(q:Reaches S J w A C): B=C:=by -- include Z
 apply sub_eq_zero.mp; refine Z _ (fun v p=>?_); rw [map_sub, LinearMap.sub_apply,r _ _ _ _ _ p.u,q _ _ _ _ _ p.u,sub_self]
noncomputable def HarvestQc (S:City)(A:l)(J:placard (UV five))(T:Bills)(i:InkQc):ℂ:= delta (T _ 0) i.f i.b i.h.cared (S.armed J (Fathom.add A i.x))
#print axioms moveDeltaQc
end YM.GaugeFieldConstruction.Ember.Hulse
