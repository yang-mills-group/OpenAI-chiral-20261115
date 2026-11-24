import YM.SU5.Reconstruction.Based.Affinity
import YM.SU5.Reconstruction.Based.Wire
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
open SlabMark Finset Fock Lat Laurent Cube Spire Vale Pastry Peaks Dial Phase Lifted Skye Tenant Rush Tulip Girt Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace LineCharge
variable (s:ℕ)
open Rooted Orbitals Fock
open YM.CF.Signal.Ovation.Transit
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)(χ: displayAlgebra Y H V G.history G.clipped j false (C j)→⋆ₐ[ℂ]ℂ)
local notation "Ξ" => sameRead Y H V G j (C j) χ s
local notation "Ms" n:max=> momentm Y n s
local notation "S₀" m:max=> Journey.side Y m s
local notation "L" n:max => (Y.voyage n).CapeT s
local notation "Z" n:max k:max=> ((Y.voyage n).X (Y.uv k)).gram s
variable (m w:ℕ)(z:Cover)
local notation "issue" z:max n:max=> denZ (Z m n) Λ.U (L m) z
noncomputable def posted (g:Dome (tent Y H)): Mark (Journey.side Y m s):= send Y H m s (g.val (Ms m))
noncomputable def countEnergy (g:Dome (tent Y H)) (x:Orbit (Journey.side Y m s)):ℂ:= inner ℂ (mateK (S₀ m)) (acts (posted Y H s m g (drawn (L m) x)) (issue x w))
lemma posted_mult (f g:Dome (tent Y H)): posted Y H s m (f*g)=posted Y H s m f * posted Y H s m g:= by
 let e:= terrain Y H (Y.ir m) s
 exact cast_rule e (f.val _) (g.val _)
where cast_rule {p q:Side}(h:p=q)(f g:Mark p): (show Mark q from h ▸ (f*g))=(show Mark q from h ▸ f)*(show Mark q from h ▸ g):= by subst q; rfl
lemma posting_real (F: Dome (tent Y H))(x:Cover)(z:ℂ)(p:Rooted.Orbitals.Communicates ((tent Y H).c (momentm Y m s)) x z (F.val (momentm Y m s))): Communicates (Journey.side Y m s) x z (posted Y H s m F):=  helper (terrain Y H (Y.ir m) s) p
where helper {n v:Side}{f:Mark n}(e:n=v)(h:Communicates n x z f): Communicates v x z (show Mark v from e ▸ f):=by subst v; exact h

lemma weight_point {f:Dome (tent Y H)}(p: Ferry Y s m w)(v: sharp Y H s m w f.val≠0): ∃ x:Orbit (Journey.side Y m s), countEnergy Y H s m w f x≠0:=by
 by_contra q; push Not at q; apply v
 obtain ⟨_,_,t⟩:= Journey.paid Y H s (p:=p) ((marque ..).1 f.property); let ν:= countEnergy Y H s m w f; have e : ∫ x,ν x∂city (Journey.side Y m s)=0:=by simp_rw [show ∀x,ν x= 0 from q]; exact integral_zero _ _ -- parser
 rw [t]; change (∫ x, ν x∂ _)/_=0; rw [e,zero_div]
lemma asked (f g:Dome (tent Y H))(x:Orbit (Journey.side Y m s))(h:countEnergy Y H s m w (f*g) x≠0): posted Y H s m f (drawn (L m) x)≠0 ∧ posted Y H s m g (drawn (L m) x)≠0:= by
 unfold countEnergy at h; rw [posted_mult,Pi.mul_apply] at h
 constructor <;> intro a <;> apply h <;> simp [a]
local notation "route" g:max=> matchWith Y H j z g
-- a diagnostic: ordered at PRI lower x, upper y poses in user's footprint, and at THIS true
-- input of the shared sharp gauge-period theory. No claim no other probes $s$ in that cost.
structure Addressable (x y:Dome (tent Y H)) (n d:ℕ):Prop where
 witnessed:∃ e:Orbit (Journey.side Y n s), countEnergy Y H s n d (matchWith Y H j z (x*y)*(x*y)) e≠0 ∧ denZ (Z n d) Λ.U (L n) e≠0 ∧
      posted Y H s n x (drawn (L n) e)≠0 ∧ posted Y H s n y (drawn (L n) e)≠0
 paid : 0< (sharp Y H s n d (matchWith Y H j z (x*y)*(x*y)).val).re
 onTime: Ferry Y s n d ∧ partitionZ (Z n d) Λ.U (L n)≠0
lemma activeWeight (F:Dome (tent Y H)) {u:Orbit (Journey.side Y m s)}(h:countEnergy Y H s m w F u ≠0): denZ (Z m w) Λ.U (L m) u≠0:=by intro d; unfold countEnergy at h; rw [d,map_zero,inner_zero_right] at h; exact h rfl
lemma active_legs (f g:Dome (tent Y H))(u:Orbit (Journey.side Y m s))(h:posted Y H s m (f*g) (drawn (L m) u)≠0): posted Y H s m f (drawn (L m) u)≠0 ∧ posted Y H s m g (drawn (L m) u)≠0:=by
 rw [posted_mult,Pi.mul_apply] at h; exact ⟨left_ne_zero_of_mul h,right_ne_zero_of_mul h⟩
include H in
lemma pricePartition(p:Ferry Y s m w) : partitionZ (Z m w) Λ.U (L m)≠0:=
 (Journey.paid Y H s (p:=p) ((marque ..).1 (1:Dome (tent Y H)).property)).2.1
lemma buyable {x y:Dome (tent Y H)} (p:Ferry Y s m w)(v:0< (sharp Y H s m w (matchWith Y H j z (x*y)*(x*y)).val).re) : Addressable Y H s j z x y m w:= by
 let A:=matchWith Y H j z (x*y); let F:= A*(x*y)
 have g:sharp Y H s m w F.val≠0:=fun h=> v.ne' (congrArg Complex.re h)
 obtain ⟨u,w'⟩:=weight_point Y H s m w p g
 exact ⟨⟨u,w',activeWeight Y H s m w F w', active_legs Y H s m x y u (asked Y H s m w A (x*y) u w').2⟩,v,p,pricePartition Y H s m w p⟩

lemma true_receptor (x y:Dome (tent Y H))(p:sameRead Y H V G j (C j) χ s (x*y)≠0):
    ∃ z: Cover, ∀ᶠ t in atTop, Addressable Y H s j z x y (i (G.rows t)) (k (G.columns t)) := by
 obtain ⟨z,h,v⟩:= turnup Y H V G C j χ s _ p; refine ⟨z,?_⟩; filter_upwards [G.history.finance s,v] with t g h
 exact buyable Y H s j _ _ z g h -- order

end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.true_receptor
