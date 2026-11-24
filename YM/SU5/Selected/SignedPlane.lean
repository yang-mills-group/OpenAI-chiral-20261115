import YM.SU5.Selected.Arrive

/-! # RP for every registered axis half plane of every resolution, despite single-tick parity.

4B offsets. Reduces to a PSD statement on the origin space and `walking`, after applying the
very same coherent transfer enough times (gains extra width with actual `volumeAround`). No claim
about complete analyticity/real-spacetime rotation or infinitesimal planes supported by wide
observables (will need extra continuity and symmetry).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "J" => Heat.gaugeShift Λ.block
local notation "stepₓ" => stepTest Y H j r
local notation "T₁" => chime K j
local notation "θ" => mirror K j
local notation "θ₀" => mirror K j 0
local notation "τ" s:max => tick Y H s j 0 r
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "η₀" => leave Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "m" => marked Y H V Q Qc j r C χ
variable (s : ℕ)
-- reflect about gauge site ANY z where test. All gauge shifts by units 4B.
def looking (z : ℤ) (x : Test) : Test :=
  ⟨θ z x.val, aux_test (axial K j z x.property.1.paid.choose_spec),
    fun h => covariant_flips K j _ x.property.1.paid.choose_spec (x.property.2 h)⟩
local notation "L" => looking Y H j r

def glance (z : ℤ) (x : Test) := composed r (L z x) x
local notation "g" => glance Y H j r

private lemma gauge_step (z : ℤ) (x : Test) : L (J z) x=(stepₓ z (dual Y H j r x)) := by
  apply Subtype.ext; change θ (J z) x.val = θ (J z) (θ₀ (θ₀ x.val)); congr 1; exact (reversal _ _ _ x.property.1.paid.choose_spec).symm
include V Q Qc C
lemma at_seam (z : ℤ) (x : Test) (v : Axis) :
    (M s) (looking Y H v r (J z) x)=star ((M s) x) := by
  rw [gauge_step Y H v r,stationarity]; exact Subtype.ext (dual_any Y H V Q Qc j r C v s x)
omit V Q Qc C
lemma across_patch (u v : ℤ) (p : Test) (w : ℤ) (q : w=u+2*v) :
    stepₓ v (g (J u) p) = g (J w) (stepₓ v p) := by
  apply Subtype.ext; change (T₁) (J v) ((θ (J u) p.val)*p.val)= θ (J w) ((T₁) (J v) p.val) * (T₁) (J v) p.val
  rw [chime_product]; refine congrArg (fun x:Family K=>x*(T₁) (J v) p.val) ?_
  have he : u = (u+v)-v:=by omega
  let h := p.property.1.paid.choose_spec
  change T₁ (J v) (θ (J u) p.val)= θ (J w) (T₁ (J v) p.val)
  rw [←moted K j (J (u+v)) (J u) (J v) (axial K j (J u) h) (by unfold gaugeShift; ring),reversal K j (J u) h,
     ←moted K j (J w) (J (u+v)) (J v) h (by rw [q]; unfold gaugeShift; ring),reversal K j (J w) (axial K j _ h)]

-- say scaleZ
abbrev scalesP (z : ℤ) (i : ℕ) := (Λ.R.L.val:ℤ)^i*z
local notation "q" => scalesP (Λ:=Λ)
-- e Exclus
include Q
lemma glance_up (x : Test) (z : ℤ) (p : Finset Cover) (t : InTest K true p false x.val)
    (v : Tower.region j z (tent Y H).ℓ p) (n : ℕ) : upward Y H Q r (g z x) s n =
      g (q z n) (upward Y H Q r x s n) := by
  apply Subtype.ext; change stream Y H D s n ((θ z x.val)*x.val)=_
  rw [woven_product Y H Q.circuit s n (axial (tent Y H) j z t) t (mirror_detached Λ l v v),stream_flipped Y H Q.circuit _ _ _ _ (aux_test t)]; rfl
omit Q
lemma imminent (S : Finset Cover) (z : ℤ) (h : Tower.region j z (tent Y H).ℓ S) (n : ℕ) :
    Tower.region j (q z n) ((K).ℓ+n) (Tower.volumeAround Λ l n S) := by
  induction n with
  | zero=> simpa [Tower.volumeAround,scalesP] using h
  | succ n ih =>
    rw [volumeAround,← Nat.add_assoc, show q z (n+1)= (Λ.R.L.val:ℤ)*(q z n) from by unfold scalesP; rw [pow_succ',mul_assoc]]
    exact strict_one Y H j ih

-- sufficient after scaling: write new plane as J w', choose min nonnegative tick `a` with shifted to J(-a), a=0 or 1.
lemma closest (S : Finset Cover) (x : ℤ) (z u : ℤ) (n t : ℕ) (p : x=z+2*u) (v : t ≤ 1) (h : x= -(t:ℤ))
    (hn : (J (1:ℤ)) ≤ n) (H' : Tower.region j (J z) ((K).ℓ+n) S) :
    Tower.region j 0 (K).ℓ (Tower.address j (J u) S) := by
  have h0 : 0 ≤ 4*(Λ.block.val:ℤ) := by positivity
  intro i e; obtain ⟨y,ey,rfl⟩ := mem_image.mp e
  rw [moves,if_pos rfl]; specialize H' y ey
  have hz : J z + 2*J u = -(J (t:ℤ)) := by
    rw [←show J (z+2*u) = J z+2*J u from ?_, ←p,h]
    · unfold Heat.gaugeShift; ring
    · unfold Heat.gaugeShift; ring
  have hv : (J (t:ℤ)) ≤ J 1 := by unfold Heat.gaugeShift; push_cast; apply mul_le_mul_of_nonneg_left (by exact_mod_cast v) h0
  rw [Nat.cast_add] at H'; omega

include V Q Qc C U
lemma final_meter (x : F₊ s) (t : ℕ) (u : Test) (e : u=toTest Y H j r s x) :
    m s (g (-J (t:ℤ)) u)= inner ℂ (walking Y H V Q Qc j r C U s t ((η s) x)) ((η s) x) := by
  have hp : θ 0 ((τ s) t x).val = θ (-J (t:ℤ)) u.val := by
    subst u; change θ 0 (T₁ _ x.val)= θ _ x.val
    let he := (toTest Y H j r s x).property.1.paid.choose_spec; unfold toTest at he; rw [←moted K j 0 (-J (t:ℤ)) (J (t:ℤ)) he (by omega),reversal K j 0 (axial K j _ he)] -- not unfold toTest?
  have h : g (-J (t:ℤ)) u=bornTest Y H j r s ((τ s) t x) x := by
    apply Subtype.ext; subst u; exact congrArg (fun y : Family K=>y*x.val) hp.symm
  exact (congrArg (m s) h).trans ((affirmation Y H V Q Qc j r C U s ((τ s) t x) x).symm.trans (congrArg (fun z : U.H=>inner ℂ z ((η s) x)) (tempo_now Y H V Q Qc j r C U s t x).symm))
omit V Q Qc C U in
private lemma diagonal (X : Hilbert) (f : X.Op) (v : 0≤f) (x : X): 0 ≤ inner ℂ (f x) x := by
  have p := (ContinuousLinearMap.isPositive_iff_complex _).1 ((ContinuousLinearMap.nonneg_iff_isPositive _).1 v) x; rw [←p.1]; exact RCLike.ofReal_nonneg.mpr p.2

omit V Q Qc C U in
private lemma halves (x : ℤ) : ∃ (u : ℤ) (t : ℕ), t≤1 ∧ x+2*u= -(t:ℤ) := by
  rcases em (x%2=0) with h|h
  exact ⟨-(x/2),0,by omega,by omega⟩
  exact ⟨-(x/2)-1,1,by omega,by omega⟩

lemma rp_rank (x : Test) (z : ℤ) (p : Finset Cover) (t : InTest K true p false x.val)
    (v : Tower.region j (J z) (tent Y H).ℓ p) : 0 ≤ m s (g (J z) x) := by
  let n := 4*Λ.block.val
  let w := q z n; let X := volumeAround Λ l n p
  have he : q (J z) n= J w:= by unfold Heat.gaugeShift w scalesP; ring
  obtain ⟨u,k,h,hx⟩:= halves w -- omit
  let y := upward Y H Q r x s n; let T := stepₓ u y
  have ht := proceeds Y H Q.circuit s n t
  have hz : Tower.region j (meshface (Λ:=Λ) 0 (s+n)) (K).ℓ (Tower.address j (J u) X) := by
    rw [area0]; exact closest Y H j X (-(k:ℤ)) w u n k hx.symm h rfl (le_of_eq (by unfold gaugeShift n; push_cast; ring)) (he ▸ imminent Y H j _ _ v n)
  let f := asField Y H j r (s+n) T (flow_port K j (J u) ht.1) hz
  have hh : m (s+n) (g (-J (k:ℤ)) T) = m s (g (J z) x) := by
    have he1 : upward Y H Q r (g (J z) x) s n=g (J w) y := by rw [glance_up Y H Q j r s x (J z) p t v n,he]
    have he2 : g (-J (k:ℤ)) T=stepₓ u (g (J w) y) := by rw [show -(J (k:ℤ))= J (-(k:ℤ)) from by unfold gaugeShift; ring]; exact (across_patch Y H j r w u y (-(k:ℤ)) hx.symm).symm
    rw [he2, ←he1]; unfold marked; rw [whole_shift,read_refines]
  rw [←hh,final_meter Y H V Q Qc j r C U (s+n) f k T (Subtype.ext rfl)]; exact diagonal U.H _ (reserve_pos Y H V Q Qc j r C U _ (atom_positive Y H V Q Qc j r C (s+n) k)) _
end YM.CF.Buffered.Afterglow.Tower.Selection
