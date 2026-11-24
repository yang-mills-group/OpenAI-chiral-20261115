import Velour.Escutcheon.Blazon
import YM.SU5.FiniteGaugeData.Poin.Sue
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

local notation "D"=> L.drifts h A u X
local notation "Rc"=>L.ringCost J u

include B
lemma chasing (t d s:ℓ)(r:Pact L J)(w:StrictMono d)
 (v:Rank Rc→ℝ)(y:Injective v)(a:ℝ):
 D (initβ t d I) (soaked s) a=
 ∑ i, hoops Rc (risen ∘ v) (risen a) i * D (initβ t d I) (soaked s) (v i):=by
 let F(c:ℝ)(z:ℂ):= D (initβ t d z) (soaked s) c
 let G(z:ℂ):= ∑ i, hoops Rc (risen ∘ v) (risen a) i * F (v i) z
 have m(x:ℝ):re ∘ initβ t d (imaginary x)=d:= by
    ext i; simp [initβ,imaginary]
 have l(c x):AnalyticAt ℂ (F c) (imaginary x):= L.driftA h A u X
      (initβ t d) (fun _=>soaked s) (imaginary x) (fun _=> initA ..) (fun _=> analyticAt_const)
      ((m x).symm ▸ w) (fun i =>rfl) c
 refine starship (f:=F a) (g:=G) (l a) (fun x=> Finset.analyticAt_fun_sum _ fun i _=>
     analyticAt_const.mul (l _ _)) ?_
 filter_upwards [pear t d s (0:ℝ) w] with z k
 unfold G F
 rw [realβ]
 exact L.orbiting J h A B u X _ _ r k.1 v y a


omit B
local notation "Ris"=> _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.rise

abbrev spunG:= L.G ∘ u
abbrev risers (z w:ℒ): Bin n H.Op := Ris S (silk h) A z w (L.m ∘ u)
abbrev gemK(z w:ℒ)(x:Points n):ℂ:= 
 inner ℂ L.Ω.val (pitch S (L.spunG u) (L.risers h A u z w) x L.Ω.val)

lemma gems (t s:ℓ)(z w:ℒ)(p:Radial z w):
 R 1 (spill z t) (spur w s)
 =L.gemK h A u z w (points (posed h X t s)):= stunts S _ _ A z w
   (sewnOut h ∘ X) (L.spunG u) _ t s L.vacU p

lemma drifts_gem (t d s:ℓ)(p:StrictMono d)(r:ℝ):
 D (initβ t d I) (soaked s) r=
 L.gemK h A u (θδ r d) (ηδ r d) (points (posed h X (tβ t s r) (sβ t s r))):=by
 have j:=uβ t d s 1 r
 have k:=vβ t d s 1 r
 have w:imaginary 1=I:=by simp [imaginary]
 rw [w,one_smul,mul_one] at j k
 change R 1 (bτ t d s r I) (bχ t d s r I)=_
 rw [j,k]
 exact L.gems h A u X _ _ _ _ (char r n d p)
#print axioms chasing
#print axioms drifts_gem

