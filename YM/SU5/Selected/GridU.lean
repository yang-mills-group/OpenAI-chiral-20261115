import YM.SU5.Selected.Addition

/-! Dense Euclidean grid of shifts on this history. All notches, combined
with genuinely real (r≥0) heat. Not yet asserting strong-continuity of
transverse spatial movement. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open MeshClock
local notation "M"=> timeMesh Λ

noncomputable abbrev shift (a : Trans j) (x : marks (timeMesh Λ)) :=
    ((ladder Y H V G.history.circuit j 0 strict C).crew a).play x
local notation "U"=>shift Y H V G j strict C
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
local notation "W"=>Ark.Ht Y H G.history.circuit j 0 strict C

instance gridCount (Λ : Preparation) : Countable (marks (timeMesh Λ)) := by
  refine Function.Surjective.countable (f:=fun x:ℕ×ℤ=>notch (timeMesh Λ) x.1 x.2) (fun x=>?_)
  obtain ⟨i,v,rfl⟩:= notch_exists (timeMesh Λ) x
  exact ⟨(i,v),rfl⟩

section
variable (a b : Trans j) (x y : marks (timeMesh Λ))
lemma shift_group : U a x * U a y=U a (x+y) := ((ladder Y H V G.history.circuit j 0 strict C).crew a).piles x y
lemma shift_origin : U a 0=1 := ((ladder Y H V G.history.circuit j 0 strict C).crew a).play_zero
lemma shift_neg : U a (-x) * U a x=1 := by rw [shift_group,neg_add_cancel,shift_origin]
lemma shift_star : star (U a x)=U a (-x) := by
  change ContinuousLinearMap.adjoint _= _
  ext1 y
  apply ext_inner_left ℂ; intro i
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [Germ.Players.shift_g W _ (-x),neg_neg] -- maybe rw with U alias
lemma shift_unitary : U a x ∈ unitary ( (W).Op ) := by
  rw [Unitary.mem_iff]
  rw [shift_star,shift_group,shift_group,add_neg_cancel,neg_add_cancel,shift_origin]; exact ⟨rfl,rfl⟩
lemma shift_commutes : Commute (U a x) (U b y) := (ladder Y H V G.history.circuit j 0 strict C).cCom a b x y
lemma shift_heat (r : ℝ≥0) : Commute (U a x) (Q r) := ladder_time Y H V G.history.circuit j 0 strict C a r x
lemma notch_comp {s u}(f:Entry Y H s j strict u)(p:0<u)(n:ℤ) :
    U a (notch M s n) * B s f p =
    B s (alongS Y H s j strict u f a n) p * U a (notch M s n) :=
  shape_across Y H V s G.history G.clipped j strict C u f p a n
lemma shift_ground (p : Γ) : U a x p.val=p.val := by
  obtain ⟨s,n,rfl⟩:=notch_exists (timeMesh Λ) x
  unfold shift; rw [on_ladder]; exact ((formal Y H V s G.history j strict C p.val).1
    ((Submodule.mem_iInf _).1 p.property s)).2 a n

end

lemma full_joint (x : A) : x∈Aurora Y H V G.history j strict C ↔
    (∀ t:ℝ≥0, Q t x=x) ∧ (∀ a:Trans j, ∀ t, U a t x = x) := by
  constructor
  · intro h; exact ⟨floor_rise Y H V G.history j strict C ⟨x,h⟩, fun a t=>shift_ground Y H V G j strict C a t ⟨x,h⟩⟩
  rintro ⟨p,q⟩
  rw [Aurora,Submodule.mem_iInf]
  intro s
  refine (formal Y H V s G.history j strict C x).2 ⟨p,fun i z=>?_⟩
  rw [←on_ladder Y H V s G.history.circuit j 0 strict C i z]
  exact q i _

local notation "A₀"=>catalog Y H V G j strict C

/-- Apply symmetry of spatial shifts on the joint ground subspace. -/
lemma cap_lattice (a : Axis) (x y : observable K strict) (s : ℕ) (t : ℤ)
    (p : x.val = relocate K a t y.val) : (P s) x=(P s) y := by
  obtain ⟨c⟩:=anyporch Y H s j strict y
  rcases eq_or_ne a j with h|h
  · subst a; rw [onAny Y H V s G.history G.clipped j strict C c]
    apply cap_moved_entry Y H V G j strict C s c.span _ _ _ (c.rise - t)
    rw [p,relocate_sums K j _ _ y.property.1,sub_add_cancel]
    exact c.yes
  let a' : Trans j := ⟨a,h⟩
  let z := alongS Y H s j strict c.span c.fwd a' t
  have ht : z.val.val= relocate K j c.rise x.val := by
    rw [p]
    change relocate K a t _=_; rw [c.yes, Vacancy.commZ K a j _ _ y.property.1] -- order
  rw [cap_moved_entry Y H V G j strict C s c.span z x c.pos c.rise ht,
    cap_moved_entry Y H V G j strict C s c.span c.fwd y c.pos c.rise c.yes]
  let m := notch (timeMesh Λ) s t
  let xU := U a' m
  have he:xU * (B s c.fwd c.pos)=(B s z c.pos)*xU:=notch_comp Y H V G j strict C a' c.fwd c.pos t
  ext1 v; apply ext_inner_left ℂ; intro l
  change inner ℂ l ((π) ((B s z c.pos) v.val))=inner ℂ l ((π) ((B s c.fwd c.pos) v.val))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change inner ℂ (l.val:W) _=inner ℂ (l.val:W) _
  conv_lhs =>
    rw [← shift_ground Y H V G j strict C a' m v,
      show (B s z c.pos) (U a' m v.val)= (U a' m) ((B s c.fwd c.pos) v.val) from
        congrArg (fun d : A →L[ℂ] A => d v.val) he.symm, ← shift_ground Y H V G j strict C a' m l]
  exact ((ladder Y H V G.history.circuit j 0 strict C).crew a').inner_g _ _ _ _

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.full_joint
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.cap_lattice
