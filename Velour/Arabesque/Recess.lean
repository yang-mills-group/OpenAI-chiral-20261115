import Velour.Escutcheon.Acre
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open YM.Damask

variable {S}{H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "R"=>L.penny h A u X
local notation "Q"=>J.penny h.symm B u X

def amid (t s:ℓ)(d:ℝ):= ∀i j,i≠j→d ≤ |s j-s i| - |t j-t i|
lemma amidst {t s:ℓ}{d:ℝ}(p:0<d)(r:amid t s d): ∃g:σ,StrictMono (s ∘ g):=by
 apply permuting
 intro i j e
 by_contra l
 have a:=r _ _ l
 rw [e,sub_self,abs_zero] at a; linarith [abs_nonneg (t j-t i)]

lemma recess (g:σ)(t h s:ℓ)(d:ℝ)(r:amid t s d)
 (v:StrictMono (s ∘ g))(x:ℝ)(p:|x|≤1):
 Chipped g d 1 (soaked s) (initβ t h (imaginary x)):=by
 intro i j l
 have m:s (g i)<s (g j):=v l
 let c:= t (g j)-t (g i)
 have y:=r (g i) (g j) (g.injective.ne l.ne)
 rw [abs_of_pos (sub_pos.mpr m)] at y
 simpa [initβ,imaginary,soaked] using
  (show d ≤ 1*(s (g j)-s (g i)- |-(x*t (g j))- -(x*t (g i))|) from by
     rw [one_mul,←neg_sub',abs_neg,←mul_sub,abs_mul]
     exact y.trans (sub_le_sub_left (mul_le_of_le_one_left (abs_nonneg _) p) _))

private theorem spanBridge {f g:ℂ→ℂ}
 (p:∀x:ℝ,|x|≤1→AnalyticAt ℂ f (imaginary x))(s:∀x:ℝ,|x|≤1→AnalyticAt ℂ g (imaginary x))
 (v:∀ᶠ y:ℝ in 𝓝 0,f y=g y):f I=g I:=by
 let E:=imaginary '' Icc (-1:ℝ) 1
 have h:IsPreconnected E:= isPreconnected_Icc.image _
    ((continuous_ofReal.mul continuous_const).continuousOn)
 refine lyc E (f:=f) (g:=g)
    ⟨0,⟨by norm_num,by norm_num⟩,by simp [imaginary]⟩ h
    ?_ ?_ (v.filter_mono nhdsWithin_le_nhds)
    ⟨1,⟨by norm_num,le_rfl⟩,by simp [imaginary]⟩
 all_goals rintro _ ⟨y,i,rfl⟩; first | exact p y (abs_le.mpr i) | exact s y (abs_le.mpr i)

lemma changed_axes (r:Pact L J)
  (g k:σ)(t s l:ℓ)(d:ℝ)(e:0<d)(p:amid t s d)
    (v:StrictMono (l ∘ g))(m:StrictMono (s ∘ k)):
 R g (initβ t l I) (soaked s)= Q k (soaked s) (initβ t l I):= by
 apply spanBridge (f:=fun z=>R g (initβ t l z) (soaked s))
   (g:=fun z=>Q k (soaked s) (initβ t l z))
 · intro x _
   refine L.penny_marble h A u X g (initβ t l) (fun _=>soaked s) _ ?_
      (fun i=>initA ..) (fun i=>analyticAt_const)
   exact (opal (t ∘ g) (l ∘ g) (s ∘ g) x (0:ℝ) v).1
 · intro x y
   exact J.penny_marble h.symm B u X k (fun _=>soaked s) (initβ t l) _
       ((recess _ _ _ _ _ p m x y).pay e one_pos)
       (fun i=>analyticAt_const) (fun i=>initA ..)
 filter_upwards [pear (t ∘ g) (l ∘ g) s (0:ℝ) v] with x y
 rw [realβ]
 exact L.swap_coin J h A B u X r g k _ _ y.1 m


lemma gold_leaf (d:ℝ)(e:0<d):
 ∃c:ℝ,0≤c∧∀X g z w,Chipped g d 1 z w→ ‖L.penny h A u X g z w‖≤c:=by
 choose c i r using fun g:σ=> L.marge (silk h) A (u ∘ g) d e
 refine ⟨_,Finset.sum_nonneg (s:=Finset.univ) (fun g _=>(i g).le),fun Y g z w t=>?_⟩
 have y:=r g 1 le_rfl (z∘g) (w∘g) t ((sewnOut h ∘ Y)∘g)
 rw [one_pow,mul_one] at y
 exact y.trans (Finset.single_le_sum (f:=c) (fun i' _ =>(i i').le) (Finset.mem_univ _))

include B in
lemma rebate (r:Pact L J)(d:ℝ)(e:0<d):
 ∃c:ℝ, 0≤c∧∀X (g:σ) t s l, amid t s d → StrictMono (l ∘ g) →
 ‖L.penny h A u X g (initβ t l I) (soaked s)‖ ≤ c:=by
  obtain ⟨c,v,t⟩:=J.gold_leaf h.symm B u d e
  refine ⟨c,v,fun X g w s l p a=>?_⟩
  obtain ⟨k,y⟩:=amidst e p
  rw [L.changed_axes J h A B u X r g k w s l d e p a y]
  apply t
  simpa only [show imaginary 1=I by simp [imaginary]] using recess k w l s d p y 1 (le_of_eq abs_one)


abbrev chosenHeight (g:σ)(k:ℕ) : ℓ := hymns n k ∘ g.symm
lemma tallness (g:σ)(k:ℕ): chosenHeight g k ∘ g=hymns n k:=
  funext fun i=>congrArg _ (g.symm_apply_apply i)

theorem freePenny (r:Pact L J)(t s:ℓ)(g j:σ)
  (d:ℝ)(e:0<d)(p:amid t s d)(v:StrictMono (s ∘ j)):
 Tendsto (fun k:ℕ=> R g (initβ t (chosenHeight g k) I) (soaked s))
 atTop (𝓝 (Q j (soaked s) (initβ t 0 I))):=by
 let Z(z:ℂ)(i:Fin n):= z*(↑(g.symm i).val:ℂ)-I*t i
 have hi(n:ℕ): initβ t (chosenHeight g n) I= Z (squirt n:ℝ):=by
    funext i; simp [initβ, chosenHeight,hymns,Z]
 have hh:initβ t 0 I=Z 0:=by funext; simp [initβ,Z]
 let F(z:ℂ):= Q j (soaked s) (Z z)
 have h0:Radial (soaked s ∘ j) (Z 0 ∘ j):=by
    rw [←hh]
    simpa only [show imaginary 1=I by simp [imaginary]]
       using (recess j t 0 s d p v 1 (le_of_eq abs_one)).pay e one_pos
 have q:AnalyticAt ℂ F 0:= J.penny_marble h.symm B u X j (fun z=>soaked s) Z _ h0
     (fun _=>analyticAt_const)
     (fun _=>(analyticAt_id.mul analyticAt_const).sub analyticAt_const) 

 have tS:Tendsto (fun k=> ((squirt k:ℝ):ℂ)) atTop (𝓝 0):=by
   simpa [Function.comp_def] using (continuous_ofReal.continuousAt.comp (x:= (0:ℝ≥0))
     NNReal.continuous_coe.continuousAt).tendsto.comp squirtL
 rw [hh]
 refine (q.continuousAt.tendsto.comp tS).congr' (Eventually.of_forall ?_)
 intro k
 change F ((squirt k:ℝ):ℂ)=R g (initβ t (chosenHeight g k) I) (soaked s)
 rw [L.changed_axes J h A B u X r g j t s (chosenHeight g k) d e p (by rw [tallness];exact hymnsP ..) v,
   hi]
#print axioms freePenny
