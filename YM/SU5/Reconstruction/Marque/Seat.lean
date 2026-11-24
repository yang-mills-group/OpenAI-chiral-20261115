import YM.SU5.Reconstruction.Marque.Lot
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric NormedSpace ContinuousLinearMap BridgeClub CrossedFrame
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
variable {H:Hilbert}(N:Set E4→Net H)(S:OS.Semigroup H clock)(Ω:H) (i j:Axis)
local notation "W"=> Wander H.space
local notation "Λ" ζ:max=> Wedge clock ζ
local notation "A" ζ:max=> N (Λ ζ)
local notation "U" => Picket.trans S
local notation "Φ"=> Lot N S Ω
lemma openWedge(b j:Axis):IsOpen (Wedge b j):= isOpen_lt (by fun_prop) (by fun_prop)
lemma lo {c d z:Axis}(p:c≠d)(w:d≠z)(q:c≠z)(x:E4): BridgeClub.turn c d x ∈ Wedge c z ↔x ∈ Wedge c z:=by simp[Wedge,Scope,turn_at,w.symm,q.symm]
lemma allImage {X Y:Type*}{f:X→Y}(p:Surjective f)(T:Set X)(D:Set Y)(h:∀x,x∈T↔f x∈D):f '' T=D:=by ext1 x; refine ⟨by rintro ⟨x,w,rfl⟩; exact (h x).1 w,fun e=>?_⟩; obtain ⟨x,rfl⟩:=p x; exact ⟨x,(h x).2 e,rfl⟩
structure Chair {H:Hilbert}(N:Set E4→ Net H)(Ω:H)(i:Axis) where
    D : Hilbert
    E : Hilbert
    Z : Clasp D H E
    L : Flash H
    Γ : Set H.Op
    crew : Club Z L (N (Wedge clock i)) Ω Γ
namespace Chair
variable {N S Ω i j} (z:Chair N Ω i) (a:Chair N Ω j)
noncomputable def mirror:= rain z.L
noncomputable def boost (t:ℝ):= deal (Picket.boost_pays z.Z t)
local notation "J"=> z.mirror
lemma confirm :Fleet J true:=rainPrice z.L
lemma well : J*J=1 := rain_mul ..
lemma often : J⁻¹= J:= rain_inv z.L
lemma cool : J Ω=Ω:= by rw [mirror,rain_at]; exact z.crew.opp
variable (t s:ℝ)
lemma convex : Fleet (z.boost t) false:=deal_fleet _
lemma bank (x:H): boost z t x=Picket.boost z.Z t x:= deal_at ..
lemma orbit (x:H):Continuous (fun t:ℝ=> z.boost t x):= by simp_rw [bank]; exact Picket.warm ..
lemma rise : z.boost (t+s)=z.boost t*z.boost s:= by ext1 x; change _=z.boost t (z.boost s x); simp_rw [bank]; rw [← Picket.boost_thru]; rfl -- maybe loops
lemma beginning: boost z 0=1:= by ext1 x; rw [bank,Picket.boost_first];rfl
lemma flip : boost z (-t)=(boost z t)⁻¹:= by apply Eq.symm; apply inv_eq_of_mul_eq_one_left; rw [← z.rise,neg_add_cancel,z.beginning]
variable {u:Wander H.space}{g:Bool}(p:Fleet u g) (q:u Ω=Ω)
include p q
lemma looksCred (e: Conveys u (A i) (A j)): u* z.mirror= a.mirror*u:= groundMirror _ _ p z.crew a.crew e q
lemma locksFlight(e:Conveys u (A i) (A j)) : u*z.boost t= a.boost (beamRate g t)*u:= by ext1 x; rw [wander_mul,wander_mul,bank,bank]; exact (locks _ _ p t z.crew a.crew e q x).symm
omit p q
variable (S)
lemma KernelMirror:Able N S (Ω:=Ω) z.mirror:=by
 intro x p; apply looksCred z z p.fleet p.pecan; have v:= p.ready (Λ i) (openWedge clock i); rwa [show (roller false 1:E4→E4) = id from funext roller_one,Set.image_id] at v
lemma KernelBoost:Able N S (Ω:=Ω) (z.boost t):=by
 intro x p; change x*z.boost t=z.boost (beamRate false t)*x; apply locksFlight z z t p.fleet p.pecan; have v:= p.ready (Λ i) (openWedge clock i); rwa [show (roller false 1:E4→E4) = id from funext roller_one,Set.image_id] at v
end Chair
end YM.Marque.Flow
