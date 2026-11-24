import YM.SU5.FiniteGaugeData.Poin.Mint
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
open Mint Topology Submodule
variable (u v w:M'.Chip) (f g:Test4) (V:Boundary.Action H)(pV:∀ p:Mink.Poincare,M'.Use S Ω p (V.V p))
local notation "O"=> M'.fieldMap S Ω
local notation "L"=> M'.lens S Ω
local notation "K"=> M'.Model S Ω
variable (x y : M'.Model S Ω) (s t:ℝ≥0)(T:ℝ)
abbrev Room(u:M'.Chip)(f:Test4):= fieldMap M' S Ω u f
lemma supportK (p:Lorentz)(x:E4)(z:x∈tsupport (shiftK (Poincare.motion p) g)): act p⁻¹ x ∈ tsupport g:=by
 let Q:= Poincare.motion p; apply Set.MapsTo.closure (s:=Function.support (shiftK Q g)) (t:=Function.support g) _ (act p⁻¹).continuous z; intro a h; change shiftK _ _ _≠0 at h; unfold shiftK at h; rw [Joint.push_at, ←show Mink.Poincare.motion (p⁻¹)=(Mink.Poincare.motion p)⁻¹ from by apply Poincare.ext <;> simp [Poincare.motion], Poincare.as_active] at h -- needs `motion⁻¹`
 exact h
variable (p0:Lorentz)
structure Loom : Prop where
 wall (A B:M'.Chip) (f g:Test4) (i:Axis) (s t:ℝ≥0) (T:ℝ) (_:i≠timeAxis)(_ :0<s)(_ : 0<t)
       (_:tsupport f ×ˢ tsupport g ⊆ PriceX i s t T): Commute (M'.Room S Ω A f) (M'.Room S Ω B g)
include pV
local notation "Q"=> Mink.Poincare.motion p0
local notation "A"=>shiftK Q
local notation "Z"=> βL M' p0
variable (ℓ:Loom M' S Ω)
include ℓ
lemma paysK (J I:Set E4) (F:tsupport f⊆J)(G:tsupport g⊆I)(i:Axis)(k:i≠tt)(H0:FieldWindow J I p0 i s t T)(u':0<s)(v':0<t): Commute (O u f) (O v g) :=by
 have h: Commute (O (Z u) (A f)) (O (Z v) (A g)) := ℓ.wall _ _ _ _ _ _ _ T k u' v' ?_; swap; · rintro ⟨x,y⟩ ⟨hx,hy⟩; exact Lorentz.undoes p0 x ▸ Lorentz.undoes p0 y ▸ H0.holds _ (F (supportK f p0 x hx)) _ (G (supportK g p0 y hy))
 let P:= M'.emergeC S Ω Q V pV; let E:= M'.emergeC S Ω Q⁻¹ V pV; have he: Function.LeftInverse E P:=fun x=> by unfold E P; rw [←descendC, inv_mul_cancel,idle]
 have ht (u:M'.Chip)(f:Test4)(x:K): O (Z u) (A f) (P x)= P (O u f x):= costume M' S Ω Q (u,f) V pV x -- args
 ext1 x; apply he.injective; change P (O u f (O v g x)) = P (O v g (O u f x)); rw [← ht,←ht,←ht,←ht]; exact DFunLike.congr_fun h.eq (P x)
omit pV ℓ
local notation "L'"=>M'.lens S Ω
-- matrix strip of comm. use y before x display
abbrev pay (v:M'.Chip)(f g:Test4):= inner ℂ (L' x) (L' (O v f (O u g y)))
-- orientation confusion: pay u x y v f g computes φ_v(f) φ_u(g). want comm. continuity f ↔ push. 
abbrev bilK (u v:M'.Chip)(f g:Test4)(x y:K):ℂ := inner ℂ (M'.lens S Ω x) (M'.lens S Ω (O u f (O v g y)))
def Blend (u:M'.Chip)(x y:K) : Test4→L[ℂ]ℂ:={ (innerSL ℂ (L' x)).toLinearMap.comp ((L').comp ((LinearMap.applyₗ y).comp (O u))) with
 cont:= (innerSL ℂ _).continuous.comp (spaces M' S Ω u y) }
lemma blend_apply : M'.Blend S Ω u x y f = inner ℂ (L' x) (L' (O u f y)):=rfl
#print axioms Blend
#print axioms paysK
-- Distribution.Assembl $x,y$ flight.N..
abbrev cry (g h:Test4):ℂ:= M'.bilK S Ω u v g h x y - M'.bilK S Ω v u h g x y
abbrev seraph(g:Test4): Distn E4 := M'.Blend S Ω v (O (M'.mirrorK u) (Probe.bar g) x) y - M'.Blend S Ω v x (O u g y)
local notation "θ"=>M'.cry S Ω u v x y -- args order x before? definition explicit g h after. order.
lemma schism : M'.cry S Ω u v x y f g= seraph M' S Ω u v x y f g:= by
 rw [seraph,_root_.sub_apply,blend_apply,blend_apply]; change _=inner ℂ (L (M'.operator S Ω (M'.mirrorK u) (Probe.bar f) x)) _-_; rw [agenda,Lduo, Probe.bar_twice]; rfl
lemma prism : M'.cry S Ω u v x y f g=-(seraph M' S Ω v u x y g) f:=by
 rw [← schism,cry,cry,neg_sub] -- might parsed neg applied map? parentheses semantics `− (...) f = − ((...) f)`
-- not rely pV for iff. `Mint.disperse`.
include pV ℓ
def Parallax: Set (E4 × E4):= {y| y.2-y.1∈Mink.spacelike}
lemma Mira : Mint.Patch (seraph M' S Ω u v x y) Parallax:=by
 constructor; intro a b p; obtain ⟨F,W,P,i,s,t,T,px,py,xr,yr,d,e,h,p⟩:= Mint.service a b p; refine ⟨F,W,px,xr,py,yr,?_⟩
 intro f p' g q; rw [← schism,cry]; apply sub_eq_zero.mpr; unfold bilK; apply congrArg (fun i=>inner ℂ (L x) (L i)); have he: Commute (O u f) (O v g):= p.elim (fun z=>paysK M' S Ω u v f g V pV s t T P ℓ F W p' q i d z e h) (fun z=>(paysK M' S Ω v u g f V pV s t T P ℓ W F q p' i d z e h).symm); exact DFunLike.congr_fun he.eq y
omit pV ℓ in
lemma phoney(x y:E4) : y-x∈spacelike ↔ x-y∈spacelike:=by nth_rw 1 [← neg_sub x y]; unfold spacelike m; simp only [mem_setOf,clock_neg,rest_neg,neg_sq,norm_neg]
-- Wight Locale for any ANY Test4 with PAIR.Causal
lemma leanR (p:Fields.causal f g): Commute (M'.Room S Ω u f) (M'.Room S Ω v g):=by
 ext1 y; apply lensI M' S Ω
 let z:= M'.fieldMap S Ω u f (O v g y) - M'.fieldMap S Ω v g (O u f y); have hp: tsupport f ×ˢ tsupport g ⊆ Parallax:=by rintro ⟨x,y⟩ ⟨u,v⟩; exact (phoney x y).2 (p x u y v)
 have he: cry M' S Ω u v z y f g=0:= by
    rw [schism]; apply disperse f g _ (fun g=> -seraph M' S Ω v u z y g) Parallax _ (Mira M' S Ω u v V pV z y ℓ) hp; intro f g; exact ((schism M' S Ω u v f g z y).symm).trans (prism M' S Ω u v f g z y)
 change L ( O u f (O v g y))=L (O v g (O u f y)); apply sub_eq_zero.mp; rw [←map_sub]; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; change inner ℂ (L z) (L z)=_; nth_rw 2 [show L z= _ from map_sub (L) (O u f (O v g y)) (O v g (O u f y))]; rw [inner_sub_right]; exact he
#print axioms leanR
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
