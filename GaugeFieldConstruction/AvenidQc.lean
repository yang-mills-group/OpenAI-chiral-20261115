import GaugeFieldConstruction.BarnabasQc
/-!
# Cohort. Supplies & Typical turnkey
-/
set_option autoImplicit false
set_option synthInstance.maxSize 9900
set_option maxHeartbeats 270000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
local notation "l5"=> Calibration.lift Floor.five
local notation "l4"=> Calibration.lift Floor.four
local notation "ℓ"=> Calibration.lift
variable {n : ℕ} {S:City} (Y:AreaQc S) (N:NickleQc) (v:UpAngleQc Y) (Z:∀ v:UV five,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0)
variable {w1 w3 w4}(p:CornetQc Y N w1 w4 w3) {P:Axis→Across}(L:Sheds S P)
local notation "τT"=>Tot S P L
lemma PenEarnQc {K:Bills}(x:InkQc)(d:Floor)(F:UV d)(A:l)(r:SymT)(h:Reaches S (prints r) K A (ℓ d F)): PenQc S (ℓ d) F x= JobPqc (S:=S) x K r A:=JetCostQc x K r _ _ h -- tune
include Z p
lemma wroughtQc (i:Axis):∃ Q: τT →ₗ[ℂ] Across,∀ (t:τT)(x:UV four), Reaches S (prints t.val) (postage i) (l4 x) (Q t x):=by
 choose F h using fun (t:τT)(x:UV four)=> VentureQc Y Z N (postage i) (prints t.val) (fun n w=>stand L w t) (JetPaperQc i) 0 (fun j x=>basis i j) (fun n=> ToastQc i) w3 p.m3 l5 (l4 x) (fun a b=> BootTagQc Y l5 _ _ _ _ (p.K1 x (pens t.val a b))) (Calibration.inject five) -- tune order
 have C (x:InkQc)(t:τT)(a:UV four): PenQc S l5 (F t a) x=JobPqc (S:=S) x (postage i) t.val (l4 a):= PenEarnQc x _ _ _ _ (h _ _) -- ...
 have q:= PenSeenQc S Z l5 (Calibration.inject five)
 let Q:τT→ₗ[ℂ] Across:= LinearMap.mk₂ ℂ F (fun a b x=> q (by rw [map_add]; ext1 y; rw[C]; change _= PenQc S l5 _ y+PenQc S l5 _ y; rw[C,C,Submodule.coe_add,map_add,LinearMap.add_apply])) (fun c a x=>q (by rw [map_smul]; ext1 y; rw[C]; change _=c • PenQc S l5 _ y; rw[C,Submodule.coe_smul,map_smul,LinearMap.smul_apply])) (fun t a b=>q (by rw[map_add]; ext1 y; rw[C]; change _= PenQc S l5 _ y+PenQc S l5 _ y; rw[C,C,map_add,map_add])) (fun c t a=>q (by rw[map_smul]; ext1 y; rw[C]; change _=c • PenQc S l5 _ y; rw[C,map_smul,map_smul]))
 exact ⟨Q,fun t x=> (by change Reaches _ _ _ _ (F t x); rw[← IdentQc (F t x)]; exact h t x)⟩ -- rw issue
lemma DangleQc (d:Floor):∃ Q:τT→ₗ[ℂ] (Ortho.Skew→ₗ[ℝ] End ℂ (UV d)),∀ (t:τT)(Ω:Ortho.Skew)(b:UV d), Reaches S (prints t.val) (rpm Ω) (ℓ d b) (ℓ d (Q t Ω b)):=by
 choose F h using fun (t:τT)(Ω:Ortho.Skew)(b:UV d)=> VentureQc Y Z N (rpm Ω) (prints t.val) (fun n w=>stand L w t) (JetAngleQc Ω) 1 (fun i=>TurnyQc Ω i) (fun n=>TackQc Ω) (w4 d) (p.m4 d) (ℓ d) (ℓ d b) (fun i j=>BootTagQc Y _ _ _ _ _ (p.K2 d b (pens t.val i j))) (Calibration.inject d)
 let V:= PenQc S (ℓ d)
 have q:Injective V:=PenSeenQc S Z _ (Calibration.inject d)
 have C (x:InkQc)(t:τT)(Ω:Ortho.Skew)(b:UV d): V (F t Ω b) x=JobPqc (S:=S) x (rpm Ω) t.val (ℓ d b):=PenEarnQc x _ _ _ _ (h _ _ _)
 let R(t:τT)(Ω:Ortho.Skew):End ℂ (UV d):={
    toFun:= F t Ω
    map_add' a b:=q (by rw[map_add]; ext1 y; rw[C]; change _= V _ y+V _ y; rw[C,C,map_add,map_add])
    map_smul' c a:=q (by rw [RingHom.id_apply,map_smul]; ext1 y; rw[C]; change _= c • V _ y; rw[C,map_smul,map_smul]) }
 let T(t: τT): Ortho.Skew→ₗ[ℝ] End ℂ (UV d):={
    toFun:= R t
    map_add' Ω Θ:=LinearMap.ext fun x=> q (by change V (F t (Ω+Θ) x)=V (F t Ω x+F t Θ x); rw[map_add]; ext1 y; rw[C]; change _= V _ y+V _ y; rw[C,C]; exact TickAnglePlusQc ..)
    map_smul' c Ω:= LinearMap.ext fun x=> q (by change V (F t (c • Ω) x)=V (c • F t Ω x); rw [Loft.real_pay,map_smul]; ext1 y; rw[C]; change _=(c:ℂ) • V _ y; rw [C]; exact TickAngleScaleQc ..) }
 let Q:τT→ₗ[ℂ] (Ortho.Skew→ₗ[ℝ] End ℂ (UV d)):={
    toFun:= T
    map_add' x y:= by apply LinearMap.ext; intro i; apply LinearMap.ext; intro z; apply q; change V (F (x+y) i z)= V (F x i z+F y i z); rw[map_add]; ext1 k; rw[C]; change _= V _ k+ V _ k; rw [C,C,Submodule.coe_add,map_add,LinearMap.add_apply]
    map_smul' c x:= by apply LinearMap.ext; intro i; apply LinearMap.ext; intro z; apply q; change V (F (c • x) i z)=V (c • F x i z); rw[map_smul]; ext1 k; rw [C]; change _= c • V _ k; rw [C,Submodule.coe_smul,map_smul,LinearMap.smul_apply] }
 exact ⟨Q,fun t Ω x=>h t Ω x⟩
include v
lemma OutfitQc : Nonempty (Supplies L):=by
 choose X hx using wroughtQc Y N Z p L; choose Q h using DangleQc Y N Z p L; let T:= LinearMap.pi X
 refine ⟨{ theta:=T, Y:=Q, bend:=fun t=>?_, reality:=?_, law:=fun t b i=>hx i t b, decree:=fun d Omega t x=> h d t Omega x }⟩
 · constructor
   · intro s i x; let r:= spinReachQc Y s v t.val _ _ _ (SpotPaperQc s i) _ _ (hx i t x); rw [← Loft.spin_lift] at r; change _= pay _ (X _ _ _); rw[← uniqueReachQc Z _ _ _ _ _ r (hx _ _ _),pay_pay]; rfl
   intro s i x; let a:=DyeReachQc Y s v t.val _ _ _ (hx i t x); rw[←ColorLiftQc] at a; exact uniqueReachQc Z _ _ _ _ _ a (hx _ _ _)
 intro i t b; let a:= GrayPathQc Y v t.val _ _ _ (hx i t b); rw[← shadeLiftQc] at a; exact uniqueReachQc Z _ _ _ _ _ a (hx i (sbar L t) (shade four b)) -- defeq
omit p
lemma sedateQc (C:Supplies L)(d)(Ω)(t:τT): C.Y d t Ω (one d)=0:=by -- no v
 let F:= one d; let Y0:= C.Y d t Ω F
 have E:Reaches S (prints t.val) (rpm Ω) (ℓ d F) (0:l):= reachPayQc S _ _ _ 0 (JetAngleQc Ω) (fun u=>by
    rw [map_zero,LinearMap.zero_apply]; exact (vacantQc Y t.val u.x u.f (rpm Ω (u.n+1) 0) u.b u.h (stand L u.x t)).symm)
 apply Calibration.inject d; rw[map_zero]; exact uniqueReachQc Z _ _ _ _ _ (C.decree d Ω t F) E
lemma typicalQc (C:Supplies L)(t:τT)(c:t=sbar L t):Loft.Typical C t:=by
 refine ⟨fun Ω=>?_,(Loft.packet _).2 (fun s i d x=>?_)⟩
 · constructor
   · intro d; exact sedateQc Y v Z L C d Ω t
   · intro d x; have ht:sbar L t=t:=c.symm; apply Calibration.inject d; rw[shadeLiftQc]; let h:= GrayPathQc Y v t.val (rpm Ω) _ _ (C.decree d Ω t x); rw [← shadeLiftQc, show tbar t.val=t.val from congr_arg Subtype.val c.symm] at h; exact uniqueReachQc Z _ _ _ _ _ (C.decree d Ω t (shade d x)) h
   · intro d x; let H:=C.decree five Ω t (ℓ d x); simp_rw [IdentQc] at H; exact uniqueReachQc Z _ _ _ _ _ H (C.decree _ _ _ _)
   intro s d x; let h:= DyeReachQc Y s v t.val _ _ _ (C.decree d Ω t x); rw [←ColorLiftQc] at h; apply Calibration.inject d; rw[ColorLiftQc]; exact uniqueReachQc Z _ _ _ _ _ (C.decree _ _ _ _) h -- tune
 apply Calibration.inject d; change ℓ d _= ℓ d (spinFrame _ s _); nth_rw 1 [Loft.spin_lift]; let h:= spinReachQc Y s v t.val _ _ _ (AnglePriceQc s i) _ _ (C.decree d i t x); rw [← Loft.spin_lift, pay_false] at h; exact uniqueReachQc Z _ _ _ _ _ (C.decree _ _ _ _) h -- tune
#print axioms typicalQc
#print axioms OutfitQc
end YM.GaugeFieldConstruction.Ember.Hulse
