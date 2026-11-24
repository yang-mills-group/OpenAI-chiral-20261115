import YM.SU5.Selected.PairFactor
import YM.SU5.Selected.Character

/-! # A test on supports with disjoint **physical** shields and its survival

ANY sufficiently large translation, any chosen separation (gauge lattice unit level zero).
When propagated up the refinements the two supports never even approach each other in these
units. Proves survival in E(s) in the sector comparison evaluated at a character of ground
compression. Specifically, the lower bound is on the actual reading of the **product mark**
on these two Euclidean supports (not the product of caps), in that component. The gauge/matter
factorization this rules out is precisely `pairFactors`. Does not assert non-clustering of
these two mixed insertions; even large enough center separations to get cluster values would be
fine. Does not separately control any error to a gauge-fixed propagator or distinguish local
gauge blocking from e.g. fermion dynamics as the cause of the footprint. Qualifiers on the
single probe see `Fixed.lean`. This is one deliberately limited sense of interaction in this
history, not yet a claim of it in a Minkowski theory.
-/
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
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "M" s:max => liftCap Y H V Q Qc j false C s
local notation "Ch" => CapCharacter Y H V Q Qc j false C
open CF.Pannier.Chancel Tapestry

structure Placement (S : Finset Cover) (s z : ℕ) (δ R0 : ℝ) : Prop where
  positiveHalf : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (plow K j z S)
  separated : Detached Λ l (reflectedBox j 0 (plow K j z S)) (plow K j z S)
  disjoint : Disjoint (reflectedBox j 0 (plow K j z S)) (plow K j z S)
  below : printedHere Λ l s (reflectedBox j 0 (plow K j z S)) (cabin R0 ∩ {x | x j ≤ -δ})
  above : printedHere Λ l s (plow K j z S) (cabin R0 ∩ {x | δ ≤ x j})

lemma eventually_placement (S : Finset Cover) (s : ℕ) {δ : ℝ} (p : 0 ≤ δ) :
    ∀ᶠ z in atTop, ∃ R0 : ℕ, Placement Y H j S s z δ R0 := by
  let L := precisionAt Λ s; let h := reserve Λ l
  have ht : 0 < L := positiveScale ..
  obtain ⟨k,g⟩ := exists_nat_gt (L * δ)
  have hv : Tendsto (fun z : ℕ => ruler (K).B * (z:ℤ)) atTop atTop :=
    Tendsto.const_mul_atTop' (ruler_gene _) tendsto_natCast_atTop_atTop
  filter_upwards [(eventually_all_finset S).2 (fun x _ => hv.eventually_ge_atTop ((h:ℤ)+k-x j))] with z e
  let P := plow K j z S; let P' := reflectedBox j 0 P
  obtain ⟨c, hc1, hc2⟩ := ((fundCabin Λ l s P).and (fundCabin Λ l s P')).exists
  have he : Ledge Λ l P j k := by
    intro x t; obtain ⟨x,w,rfl⟩ := plow_stays K j z S t
    rw [moves,if_pos rfl]; specialize e x w; unfold h at e; omega
  have he₁ : Tower.region j 0 (reserve Λ l) P := fun x u => le_trans (by omega : (0:ℤ) + reserve Λ l ≤ (k:ℤ) + ↑(reserve Λ l)) (he x u)
  have hk : δ < markZ Λ s k := (lt_div_iff₀ ht).2 (by rw [Int.cast_natCast]; simpa only [mul_comm L δ] using g)
  have hx : ∀ x ∈ P', x j ≤ -(h:ℤ)-k := by
    intro x t; obtain ⟨i,p,rfl⟩ := mem_image.mp t; specialize he i p
    rw [reflected_coord]; unfold h; omega
  refine ⟨c,⟨by rw [area0]; exact he₁, mirror_detached Λ l he₁ he₁, ?_, fun x v z w=>?_, fun x v z w=>?_⟩⟩
  · apply Finset.disjoint_left.mpr; intro i u v; specialize he i v; specialize hx i u; unfold h at hx; have h := margin_good Λ l; omega
  · refine ⟨hc2 _ v w, ?_⟩
    change _ ≤ -δ; apply le_trans _ (neg_le_neg hk.le)
    specialize hx x v
    unfold markZ; change _ ≤ -(↑(k:ℤ)/L : ℝ)
    rw [← neg_div,le_div_iff₀ ht]; have hv := (abs_le.mp (w j)).2; have hu : (x j:ℝ) ≤ -(↑(reserve Λ l):ℝ)-(k:ℕ) := by exact_mod_cast hx
    unfold L; rw [Int.cast_natCast]; linarith only [hv,hu]
  exact ⟨hc1 _ v w, hk.le.trans (brought Λ l s j k P he x v w)⟩

lemma Placement.physical {S : Finset Cover} {s z n : ℕ} {δ c : ℝ} (p : Placement Y H j S s z δ c) :
    let Sn := volumeAround Λ l n (reflectedBox j 0 (plow K j z S))
    let Tn := volumeAround Λ l n (plow K j z S)
    Detached Λ l Sn Tn ∧ printedHere Λ l (s+n) Sn (cabin c) ∧
      printedHere Λ l (s+n) Tn (cabin c) ∧
        ∀ x∈Sn, ∀ y∈Tn, ∀ u ∈ Tapestry.shield Λ l (s+n) x,
          ∀ v ∈ Tapestry.shield Λ l (s+n) y, 2*δ ≤ dist u v := by
  have h₁ := transport_location Λ l s n _ _ p.below
  have h₂ := transport_location Λ l s n _ _ p.above
  refine ⟨Around_detaches Λ l p.separated _, fun x v y w => (h₁ x v w).1,
    fun x v y w => (h₂ x v w).1, fun x v y w u l0 q l1 =>?_⟩
  apply le_trans _ (dist_le_pi_dist u q j); rw [Real.dist_eq]
  have hh : u j ≤ -δ := (h₁ x v l0).2; have hg : δ ≤ q j := (h₂ y w l1).2
  linarith only [neg_le_abs (u j-q j), hh,hg]

def mixedPair (F : Test) (z : ℕ) : Test :=
  composed false (dual Y H j false (moved Y H j false z F)) (moved Y H j false z F)

include V Q Qc C
lemma gain_pair (χ : Ch) (s z : ℕ) (F : Test) (x : F₊ s) (p : x.val = relocate K j z F.val) :
    let read := marked Y H V Q Qc j false C χ s
    (↑(‖read F‖^2 : ℝ):ℂ) ≤ read (mixedPair Y H j F z) := by
  unfold marked mixedPair
  have he := rp_of_char Y H V Q Qc j false C χ s x; dsimp only at he ⊢
  rw [show toTest Y H j false s x = moved Y H j false z F from Subtype.ext p] at he
  change (↑(‖χ ((M s) (moved Y H j false z F))‖^2):ℂ) ≤_ at he
  rwa [invariant Y H V Q Qc j false C s z F (moved Y H j false z F) rfl] at he -- might rw RHS too? 

abbrev phaseRead (χ : Ch) := accessReading Y H V Q Qc j C χ.toAlgHom.toLinearMap
local notation "χR" => phaseRead Y H V Q Qc j C
lemma phase_read (s : ℕ) (χ : Ch) (F : Test) : (χR χ) s F.val = χ ((M s) F) :=
  access_read ..
lemma phase_unit (s : ℕ) (χ : Ch) (S : Finset Cover) : Scopes K S ((χR χ) s) :=
  access_scopes Y H V Q Qc j C _ χ.map_one s S

variable {s : ℕ} {F : Family (tent Y H)} {O : Set RSpace} {m : ℕ} {u : Fin m → Cover}
  {T : Finset Cover} {w : SU.Slot} {b' : ℝ}

/-- Two-separated witnesses test the same nonfactorization. At distance arbitrarily prescribed
in units of gauge mesh at level zero (not necessarily exactly δ, get at least this). `e` is a
margin already seen by the character. Gives estimate on Euclidean signed component value at
finite physical separation, true also of all later transports. Controls SEPARATED SHIELDS (use
`Placement.physical`). Not yet transporting to a cluster vacuum or Lorentz theory. -/
lemma pair_survives (χ : Ch) (h : PhysicalTexture Y H F w s T u O b') {e : ℝ}
    (p : 0 ≤ e) (g : e < ‖(χR χ) s F‖) {z : ℕ} {δ c : ℝ} (v : Placement Y H j T s z δ c) :
    (¬ pairFactors j K z T (Window.family w) u ((χR χ) s)) ∧
    ∀ n : ℕ,
      let x := relocate K j z F
      let Sn := volumeAround Λ l n (reflectedBox j 0 (plow K j z T))
      let Tn := volumeAround Λ l n (plow K j z T)
      let G := stream Y H D s n (mirror K j 0 x)
      let F' := stream Y H D s n x
      G ∈ observ K Sn true ∧ F' ∈ observ K Tn true ∧
        stream Y H D s n (afterShift j K z F F) = G * F' ∧
        (χR χ) (s+n) (G*F') = (χR χ) s (afterShift j K z F F) ∧
        (↑(e^2) : ℂ) < (χR χ) (s+n) (G*F') := by
  let u' := h.enter Y H false
  let Q' := mixedPair Y H j u' z
  have hx := (phase_read Y H V Q Qc j C s χ Q')
  have hS : (moved Y H j false z u').val ∈ observ K (plow K j z T) true := by
    let hz := (FilTest h.initiates).widen
    exact (obs_in ..).2 ⟨flow_port K j _ hz,chime_cov K j _ hz h.gauge⟩
  let hz := (obs_in ..).1 hS
  let x := asField Y H j false s (moved Y H j false z u') hz.1 v.positiveHalf
  have he := gain_pair Y H V Q Qc j C χ s z u' x rfl
  let d := (χR χ) s (afterShift j K z F F)
  have hg : (↑(‖(χR χ) s F‖^2 : ℝ):ℂ) ≤ d := by
    change (↑(‖(χR χ) s u'.val‖^2):ℂ) ≤ (χR χ) s Q'.val
    rw [phase_read, hx]; exact he
  have hw : (↑(e^2) : ℂ)< d := lt_of_lt_of_le (RCLike.ofReal_lt_ofReal.mpr (show e ^ 2 < ‖(χR χ) s F‖ ^ 2 from (sq_lt_sq₀ p (norm_nonneg _)).2 g)) hg
  constructor
  · intro Q
    have r0 : d=0 := after_detect j K _ (phase_unit Y H V _ Qc j C s χ _) (phase_unit Y H V _ Qc j C s χ _) v.disjoint h.inject Q h.initiates h.initiates
    rw [r0] at hw; exact (RCLike.ofReal_nonneg.mpr (sq_nonneg e)).not_gt hw
  intro n
  let ht := obs_flip K j 0 hS
  let a' := moved Y H j false z u'; let b'0 := dual Y H j false a'; let H0 := stream Y H D s n b'0.val; let H1 := stream Y H D s n a'.val
  let H2 := stream Y H D s n Q'.val
  have hp : H2 = H0 * H1 := woven_product Y H Q.circuit s n ((obs_in ..).1 ht).1 hz.1 v.separated
  have h0 : (χR χ) (s+n) (H0*H1) = d := by
    rw [←hp]
    change (χR χ) (s+n) (upward Y H Q false Q' s n).val = (χR χ) s Q'.val
    rw [phase_read,hx, read_refines]
  exact ⟨Tower.chroma Y H Q.circuit s n ht,Tower.chroma Y H Q.circuit s n hS, hp, h0,h0.symm ▸ hw⟩
end YM.CF.Buffered.Afterglow.Tower.Selection
