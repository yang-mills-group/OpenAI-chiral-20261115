import YM.SU5.Reconstruction.Marque.Fab
import YM.SU5.Reconstruction.Marque.Rails
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Metric
open scoped Topology Classical
abbrev Wander (H:Type*) [PseudoEMetricSpace H]:= H≃ᵢ H
variable {H:Type*} [MetricSpace H]
local notation "W"=> Wander H
variable {ι:Type*} {L:Filter ι}
variable {U V:ι→ (H≃ᵢ H)} {u v:H≃ᵢ H}
@[simp] lemma wander_mul (u v:W)(x:H):(u*v) x=u (v x):= rfl
@[simp] lemma wander_inv (u:W)(x:H): u⁻¹ x=u.symm x:=rfl
@[simp] lemma wander_back (u:W)(x:H): u (u⁻¹ x)=x:=u.apply_symm_apply x
@[simp] lemma wander_front (u:W)(x:H): u⁻¹ (u x)=x:=u.symm_apply_apply x
def Spiral (L:Filter ι) (U:ι→W)(u:W):=∀ x:H,Tendsto (fun i=> U i x) L (𝓝 (u x))
variable (p:Spiral L U u)(q:Spiral L V v)
lemma plainLimit (L:Filter ι)(g:W):Spiral L (fun _=>g) g:=fun _=>tendsto_const_nhds
include p
lemma curlLimit {e:ι→H}{b:H}(h:Tendsto e L (𝓝 b)): Tendsto (fun i=> U i (e i)) L (𝓝 (u b)):= by
 apply tendsto_iff_dist_tendsto_zero.mpr -- tune arguments
 refine squeeze_zero' (g:=fun i=>dist (U i b) (u b)+ dist (e i) b) (Eventually.of_forall (fun i=> dist_nonneg)) (Eventually.of_forall (fun i=> le_trans (dist_triangle _ (U i b) _) ?_)) ?_ -- tune
 · exact ((congrArg (·+dist (U i b) (u b)) ((U i).isometry.dist_eq (e i) b)).trans (add_comm ..)).le
 · simpa using! (tendsto_iff_dist_tendsto_zero.mp (p b)).add (tendsto_iff_dist_tendsto_zero.mp h)
lemma backLimit : Spiral L (fun i=> (U i)⁻¹) u⁻¹ := by
 intro x; apply tendsto_iff_dist_tendsto_zero.mpr; have h:=tendsto_iff_dist_tendsto_zero.mp (p (u⁻¹ x))
 apply h.congr; intro i; rw [wander_back, ← (U i).isometry.dist_eq ((U i)⁻¹ x) (u⁻¹ x), wander_back,dist_comm]
include q
lemma stackLimit: Spiral L (fun i=> U i * V i) (u*v):=fun x=>curlLimit p (q x)
omit p q
variable {Y:Type*}[TopologicalSpace Y]
def Continues (U:Y→W):=∀ x:H,Continuous (fun y=>U y x)
lemma spirals {U:Y→W}{e:ι→Y}{b:Y}(h:Tendsto e L (𝓝 b))(p:Continues U): Spiral L (fun i=> U (e i)) (U b):=fun x=>(p x).continuousAt.tendsto.comp h
lemma nowC {U:Y→W}: Continues U↔∀ y:Y,Spiral (𝓝 y) U (U y):= ⟨fun h _ x=>(h x).continuousAt.tendsto,fun h x=>continuous_iff_continuousAt.mpr (fun y=> h y x)⟩
structure Passage (H:Type*) [MetricSpace H] where
 ok : Two→Set (Wander H)
 pass : (1:Wander H) ∈ ok 1
 plus : ∀ {x y} {u v: Wander H}, u∈ok x→ v∈ ok y→ u*v∈ok (x*y)
 opp : ∀ {x}{u:Wander H},u∈ok x→ u⁻¹∈ok x⁻¹
namespace Passage
variable {P:Passage H}
variable {x y:Two}
lemma circles (p:u∈P.ok x)(q:v∈ P.ok y):rehome u v∈P.ok (rehome x y):= P.plus (P.plus p q) (P.opp p)
lemma powerLift (p:u∈P.ok x)(n:ℕ):u^n∈P.ok (x^n):=by induction n with | zero=> simpa only [pow_zero] using P.pass | succ n e=> simpa only [pow_succ] using P.plus e p
-- lift of path
variable {F G :Y→ Two}
variable (P)
def Agree (g:Y→Two):=∃ U,Continues (H:=H) U∧∀i:Y,U i∈P.ok (g i)
def Fell (p:ι→Two) (v:Two)(L:Filter ι):=∃ (U:ι→ Wander H) (u:W),Spiral L U u∧ u∈P.ok v∧∀ᶠ i in L,U i∈P.ok (p i)
variable {P} {v g:Two}
variable {w₁ w₂:ι→ Two}
lemma atSome (h:P.Agree F){e:ι→Y}{b:Y}(p:Tendsto e L (𝓝 b)): P.Fell (F∘e) (F b) L:= by obtain ⟨g,q,v⟩:=h; exact ⟨_,_,spirals p q,v b, Eventually.of_forall (fun i=>v (e i))⟩
lemma rolled (h:P.Fell w₁ v L)(b:P.Fell w₂ g L): P.Fell (fun i=>w₁ i*w₂ i) (v*g) L:= by
 obtain ⟨U,u,h,k,e⟩:=h; obtain ⟨V,v',b,j,f⟩:=b; exact ⟨_,_,stackLimit h b, P.plus k j, (e.and f).mono (fun i p=>P.plus p.1 p.2)⟩
lemma hereAgree (u:H≃ᵢ H)(b:u∈P.ok g): P.Agree (fun _:Y=> g):= ⟨fun _=>u, fun x=>continuous_const, fun _=>b⟩
lemma timesAgree (h:P.Agree F)(b:P.Agree G):P.Agree (fun x=>F x*G x):=by obtain ⟨u,p,e⟩:=h; obtain ⟨g,q,v⟩:=b; exact ⟨_, nowC.mpr (fun y=>stackLimit (nowC.mp p y) (nowC.mp q y)),fun i=>P.plus (e i) (v i)⟩
lemma compAgree {i:Type*}[TopologicalSpace i]{f:i→Y}(h:P.Agree F)(k:Continuous f):P.Agree (fun i=>F (f i)):= by obtain ⟨w,e,t⟩:=h; exact ⟨fun i=>w (f i),fun x=>(e x).comp k,fun _=> t _⟩
lemma reverseAgree(h:P.Agree F): P.Agree (fun x=>(F x)⁻¹):=by obtain ⟨u,e,t⟩:=h; exact ⟨fun x=>(u x)⁻¹, nowC.mpr (fun x=> backLimit (nowC.mp e x)),fun i=>P.opp (t i)⟩
lemma congrFell (h:P.Fell w₁ g L) (p:w₁ =ᶠ[L] w₂): P.Fell w₂ g L:= by obtain ⟨_,_,q,v,z⟩:=h; exact ⟨_,_,q,v,(p.and z).mono (fun i h=> h.1 ▸ h.2)⟩
lemma agree_price (h:P.Agree F)(i:Y): ∃ u:W, u∈P.ok (F i):= by obtain ⟨v,p,q⟩:=h; exact ⟨v i, q i⟩
end Passage
end YM.Marque
