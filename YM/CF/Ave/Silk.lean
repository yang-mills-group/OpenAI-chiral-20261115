import YM.CF.Ave.Tower
import YM.CF.Pastry.Icing

/-! Staggered transfer interval controlled before averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e H a K : ℝ}
-- station feeds only the necessary sample marks
abbrev stayX (x : Train m B e) := stationP m B (stick 0) (stick 0) none x.1.val (slot m x.2)
lemma visiting (p : Train m B e) (g : Court m B) : stayX (routeT p g)=flipR g (stayX p) := by
  let s := onF g (slot m p.2)
  have he : slot m (partner m B g p.2)=s := rfl
  rw [stayX,show (routeT p g).2=_ from rfl, show slot m ((routeT p g).2)=_ from he] -- tune
  exact touch_g ..
lemma tenant_t (b : Room B e) {x : Train m B e} (g:x∈Breath m B e) : TenantK (stayX x):= dark0 b none (pays g)
def town (f : Post m B→ Ewe m B) (x : Train m B e) := accessK m B (stick 0) (stick 0) none x.1.val (slot m x.2) f
lemma resident (b : Room B e) (f : Post m B→Ewe m B) (g : Continuous f) : ContinuousOn (town (m:=m) (B:=B) (e:=e) f) (Breath m B e) := by
  let A := banner m B e {0}; let F := fun t:FlagU m B=> accessK m B (stick 0) (stick 0) none t.1 t.2 f
  have he : stick (0:Row)∈zone {0} := stick_in _ (mem_singleton_self _)
  have h : ContinuousOn F A := access_cont A _ _ _ f g (fun t p=> drives b p.1 p.2 he he (by rw [sub_self,norm_zero]; positivity) none) (dress _ _ _ he he none b)
  let G := fun p:Train m B e=>(p.1.val,slot m p.2); refine h.comp (f:=G) ((continuous_subtype_val.comp continuous_fst).prodMk ((slot_cont m).comp continuous_snd)).continuousOn (fun p u=>?_)
  exact pays u
abbrev Cloth (m B : Side) := Raw (Post m B) (Elf m B)
abbrev Sens (m B : Side) := Toll (Elf m B)
def silt (t : ℝ) (A Y : Op (Elf m B)) := hang (n:=Elf m B) (Tour.Kcc (decay A t) (reserve (projector A) Y)) (Tour.Kcg (decay A t) (driftB (projector A) Y)) (Tour.Kgg (decay A t) (weldB (projector A) Y))
def retire (m B : Side) (c : Foot m B) (t : ℝ) (v : Train m B e) := silt (m:=m) (B:=B) t (wiel m B c v.1.val) (pair m B v.1.val v.2)
lemma diect (m B : Side) (t) (x : Train m B e) (c) (b : Room B e) : (nursery (n:=Elf m B) (lens m B c x.1.val) (lensP c b x.1.property)).cook (retire m B c t x)=sheet m B c t x.1.val x.2 := stitchP (n:=Elf m B) .. -- tune
lemma wand (b : Room B e) {S : Stamp m B} (p : 1≤H) {A C D : Cloth m B} {W U V : Sens m B} (h : Linen S A C D (sigK (CSide m B)) W U V) : Dedicated (e:=e) p S (town (m:=m) (B:=B) (fun d=>hang (A d) (C d) (D d))) (Linen.coins W U V * H^2) := by
  let F (x : Post m B):= hang (n:=Elf m B) (A x) (C x) (D x)
  have he x (p:x∈Breath m B e) : town (m:=m) (B:=B) F x=F ⟨_,tenant_t b p⟩ := by unfold town; exact entrance (p:=stick 0) (q:=stick 0) (m:=m) (B:=B) (v:=none) (tenant_t b p)
  change Dedicated p S (town (m:=m) (B:=B) (e:=e) F) _
  refine subscribing p (mul_nonneg h.coast (sq_nonneg _)) (fun x g=>?_) (resident b F h.pivotC) (fun x g=>?_) (fun x hx y hy g l=>?_) (fun x g v=>?_)
  · rw [he x g]; exact h.pool_tier _ _ (zero_le_one.trans p)
  · rw [he x g]; exact h.fondant _ (fun i e j=> sign_up S e j) _
  · rw [he x hx,he y hy]; refine h.pivotD _ _ ?_
    exact station_read S none _ _ g trivial (A:=slot m x.2) (X:=slot m y.2) (fun i p=>l i.1 (mem_product.mp p).1)
  let t : Post m B := ⟨_,tenant_t b g⟩
  have hx : routeT x v ∈ Breath m B e := by rw [← breathed (m:=m) p]; change law m B (Lattice.gauge v x.1.val) (partner m B v x.2)≠0; rw [law_g]; exact g
  rw [he x g, he _ hx]; let y : Post m B := ⟨_, tenant_t b hx⟩
  change routeM m B v (F t)=F y; rw [show routeM m B v (F t)=F ((slotK _).drive v t) from h.gift ..]; apply congrArg; exact Subtype.ext (visiting x v).symm
set_option maxHeartbeats 500000 in
lemma minted (b : Room B e) (p : 1≤H) {A C D : Stamp m B→Cloth m B} {W U V : Stamp m B→Sens m B} (h : ∀ S,Linen S (A S) (C S) (D S) (sigK (CSide m B)) (W S) (U S) (V S)) (v : 0<a) (s : Ledger a W K) (g : Ledger a U K) (l : Ledger a V K) (d : ℝ) (Z : 0 < d) (t : d*21^4≤ a/2 *(B.val:ℝ)) : let f S := Linen.coins (W S) (U S) (V S)*H^2;
    (∀ S, f S≠0→Grove (terr _) S) ∧ ∀ i, cellHit m B d f i ≤ Real.exp (d*21^4) * (16*(7*(B.val:ℝ)+1)^4 * ((4 * bulk a quota * K)*H^2)) := by
  intro f; have he (S:Stamp m B) (g:f S≠0) : Grove (terr _) S:= (h S).shore (left_ne_zero_of_mul (show Linen.coins _ _ _*H^2≠0 from g))
  have ht : 0≤quota:= (by linarith [quota_bound]); have hv : 0 ≤ bulk a quota := tsum_nonneg (fun i=>by positivity); have hh := s.posP
  refine ⟨he, hit_transfer Z.le t he (fun S=>mul_nonneg (h S).coast (sq_nonneg _)) ?_ (by positivity)⟩
  intro x
  have hx: hitE (a/2) (fun S=>ledgerV (W S)) x≤bulk a quota*K := tall (fun i=>(h i).low) s v (ample_slots _) ht x
  have hy: hitE (a/2) (fun S=>ledgerV (U S)) x≤bulk a quota*K := tall (fun i=>(h i).middle) g v (ample_slots _) ht x
  have hz: hitE (a/2) (fun S=>ledgerV (V S)) x≤bulk a quota*K := tall (fun i=>(h i).high) l v (ample_slots _) ht x
  unfold hitE f; simp_rw [← mul_assoc, ←sum_mul]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simp_rw [Linen.coins, mul_add, sum_add_distrib]; exact (add_le_add (add_le_add (add_le_add hx hy) hy) hz).trans_eq (by ring)
structure Construct (m B : Side) (H : ℝ) (p:1≤H) (e t : ℝ) (c : Foot m B) (v Y : ℝ) (F : Stamp m B→ Train m B e→ Ewe m B) (K : Stamp m B→ℝ) : Prop where
  serve S : Dedicated p S (F S) (K S)
  bought S : K S≠0→ Grove (terr _) S
  spends x : cellHit m B v K x≤Y
  inventory x (g:x∈Breath m B e) : ∑ S, F S x=retire m B c t x
end YM.CF.Ave
