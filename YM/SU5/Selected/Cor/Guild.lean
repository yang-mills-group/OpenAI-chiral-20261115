import YM.SU5.Selected.Cor.Wickets
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel Tapestry Papal
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
-- use C : Arena false only (assembly neutral). 
local notation "Ch"=> CapCharacter Y H V Q Qc j false C
local notation "Test"=> Vacancy.observable (tent Y H) false
local notation "readχ"=> phaseRead Y H V Q Qc j C
local notation "F₀" i:max=> cap Y H V i Q Qc j false C
local notation "N" i:max=> liftCap Y H V Q Qc j false C i
namespace Fern
-- recovery linear maps. Bool r. decide. c+ lab.
variable (s n:ℕ)
local notation "N'"=> n
variable {S T:Finset Cover}{k0 d:ℝ} {f g:Family (tent Y H)}
local notation "lux"=> Sermon.luxury (tent Y H)
variable (a':Sermon.luxury (tent Y H) f S)
-- $v impossible cap. elementary via scaling.
def gentle {f:Family (tent Y H)} {S:Finset Cover}(h:InTest (tent Y H) true S false f) : Test:= ⟨f, Tower.aux_test h, fun p=>by cases p⟩
private lemma emptyCost {M:Type} [AddCommGroup M][Module ℂ M] (x:M)(u:-x=x):x=0:=by
 have he:(2:ℂ) • x=0:= by rw [two_smul]; nth_rw 1 [←u]; exact neg_add_cancel _
 exact (smul_eq_zero.mp he).resolve_left (by norm_num)
include V Q Qc C
namespace Cloak
lemma forbidden (x:Test) (e:Tower.mirror K 0 0 (Tower.mirror K 1 0 x.val) = -x.val): (N s) x=0:=by
 -- `$a.val` infer notations. avoid kernel heart. use N elems in B (CStar linear). `dual_any` equality as `N` with ★.
 have h(v:Axis)(x:Test) : (N s) (dual Y H v false x) = star ((N s) x) := Subtype.ext (dual_any Y H V Q Qc j false C v s x)
 let V':=dual Y H 0 false (dual Y H 1 false x); let p:= (N s) V'; apply emptyCost ((N s) x); have hp:weighted false x (-1:ℂ)= V':= Subtype.ext (show (-1:ℂ) • x.val=_ from (neg_one_smul _ _).trans e.symm)
 rw [← neg_one_smul ℂ,←read_scale Y H V Q Qc j false C s x (-1),hp]; exact (h 0 _).trans ((congrArg star (h 1 x)).trans (star_star _))
lemma priced0 (χ:Ch)(z:Test)(e: (N s) z=0) : E s z.val=0∧ (readχ χ) s z.val=0:= by
 have he:(F₀ s) z=0:= congrArg Subtype.val e
 refine ⟨?_,?_⟩; · rw [←inspected Y H V s Q Qc j false C (F:=z),he]; simp
 rw [phase_read, e, map_zero]
end Cloak

-- Prop capturing all refinement uses. price zero preserved χ,E & cap explicitly (proof even though projection Cp2 identities). name input `X`. refine both factors.
local notation "MS"=> volumeAround Λ l n
local notation "V₁"=> stream Y H D s n
structure Alight (c k₁:ℝ) (X X':Family (tent Y H))(S T:Finset Cover): Prop where
  place : GalleryG Λ l s c k₁ S T
  inspires: lux X S
  blazes : lux X' T
  -- global read & propagate.
  vision (z z':Test)(f:z.val=X)(g:z'.val=X') (χ : CapCharacter Y H V Q Qc j false C) (n:ℕ):
    let u:= upward Y H Q false z s n; let v:= upward Y H Q false z' s n;
    u.val∈ observ K (volumeAround Λ l n S) true ∧ v.val∈ observ K (volumeAround Λ l n T) true ∧ upward Y H Q false (composed false z z') s n = composed false u v ∧ liftCap Y H V Q Qc j false C s (composed false z z') = liftCap Y H V Q Qc j false C (s+n) (composed false u v) ∧
    liftCap Y H V Q Qc j false C (s+n) u=0∧ liftCap Y H V Q Qc j false C (s+n) v=0∧
    E (s+n) u.val=0∧ E (s+n) v.val=0∧ phaseRead Y H V Q Qc j C χ (s+n) u.val=0∧ phaseRead Y H V Q Qc j C χ (s+n) v.val=0∧ phaseRead Y H V Q Qc j C χ (s+n) (u.val*v.val)= phaseRead Y H V Q Qc j C χ s (X*X') ∧ E (s+n) (u.val*v.val)= E s (X*X')
#print Alight.mk
include a' in
lemma alight (t: Sermon.luxury (tent Y H) g T) (c : GalleryG Λ l s k0 d S T) : Alight Y H V Q Qc j C s k0 d f g S T:=by
 refine ⟨c,a',t,?_⟩
 intro z z' hp ht χ n; let u:=upward Y H Q false z s n; let v:=upward Y H Q false z' s n; have he:upward Y H Q false (composed false z z') s n=composed false u v:= by
    apply Subtype.ext; change stream Y H D s n (z.val*z'.val)= stream _ _ _ _ _ z.val*stream _ _ _ _ _ z'.val; rw [hp,ht]; exact woven_product Y H Q.circuit s n a'.1.widen t.1.widen c.detached
 have hx:(N (s+n)) (composed false u v)=(N s) (composed false z z'):= he ▸ read_refines Y H V Q Qc j false C s n (composed false z z')
 have h₁:(N (s+n)) u=0:=(read_refines Y H V Q Qc j false C s n z).trans (Cloak.forbidden Y H V Q Qc j C s z (hp ▸ a'.2.2))
 have h₂:(N (s+n)) v=0:=(read_refines Y H V Q Qc j false C s n z').trans (Cloak.forbidden Y H V Q Qc j C s z' (ht ▸ t.2.2))
 obtain ⟨i,i'⟩:= Cloak.priced0 Y H V Q Qc j C (s+n) χ u h₁; obtain ⟨l,l'⟩:= Cloak.priced0 Y H V Q Qc j C (s+n) χ v h₂
 have hv(n:ℕ)(V':Test)(X:Finset Cover) (p:lux V'.val X) : (upward Y H Q false V' s n).val∈ observ K (volumeAround Λ _ n X) true:= Tower.chroma Y H Q.circuit s n ((obs_in ..).2 ⟨p.1.widen,p.2.1⟩)
 subst f g
 refine ⟨hv n z S a',hv n z' T t,he,hx.symm,h₁,h₂,i,l,i',l',?_,?_⟩
 · change (readχ χ) (s+n) (composed false u v).val= (readχ χ) s (composed false z z').val; rw [phase_read,phase_read,hx]
 change E (s+n) (composed false u v).val= E s (composed false z z').val
 rw [←inspected Y H V (s+n) Q Qc j false C (F:=composed false u v), ←inspected Y H V s Q Qc j false C (F:=composed false z z'), (show (F₀ (s+n)) (composed false u v)=(F₀ s) (composed false z z') from congrArg Subtype.val hx)]
namespace Alight
-- indeed cap of SAME family product mark, not naive multiply factor caps. ANY large refinement. pair (z,z'). consumers
variable (A₀:Alight Y H V Q Qc j C s k0 d f g S T)(χ:CapCharacter Y H V Q Qc j false C)
include A₀
lemma rigorousNE (hP:E s (f*g)≠0 ∨ phaseRead Y H V Q Qc j C χ s (f*g) ≠ 0) (z z':Test)(f':z.val=f)(g':z'.val=g) :
    let u:= upward Y H Q false z s n; let v:=upward Y H Q false z' s n; (cap Y H V (s+n) Q Qc j false C (composed false u v))≠ (cap Y H V (s+n) Q Qc j false C u)*(cap Y H V (s+n) Q Qc j false C v) :=by
 subst f g; let u:= upward Y H Q false z s n; let v:=upward Y H Q false z' s n; change _≠_*_; intro e; let F:= composed false z z'; obtain ⟨a,b,c,k',p,t,h,i⟩:= A₀.vision z z' rfl rfl χ n; let g:=(N (s+n)) (composed false u v); have h:(N s) F=0:=by rw [show (N s) F=_ from k']; apply Subtype.ext; rw [show g.val= _ from e,show cap _ _ _ _ _ _ _ _ _ u=0 from congrArg Subtype.val p]; exact zero_mul _ -- tune
 exact hP.elim (fun e=> e (Cloak.priced0 Y H V Q Qc j C s χ F h).1) (fun e=> e (Cloak.priced0 Y H V Q Qc j C s χ F h).2)
end Alight
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms alight
#print axioms Cloak.forbidden
#print axioms Alight.rigorousNE
