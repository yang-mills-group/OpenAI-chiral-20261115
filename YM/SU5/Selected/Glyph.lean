import YM.SU5.Selected.Sustain
/-!
# OS dictionary on a spectral character of the joint-ground algebra

`Entry` means a strictly positive aligned time-slab presentation. Evaluation in the
selected vacuum is on the entrance product **after** multiplying, rep not shortened by
projecting between paid components. Prove actual Hilbert OS reflection positivity of ALL the
supported marks in the selected character (in particular get selected-axis adjoints, positive
correlations across disjoint supports, even time/space motion, and exact compatibility with
higher rungs). Also prove the OS space construction here is a genuine GNS dictionary.

NOT a QFT reconstruction claim. The OS dictionary here is still only on the
filtered tower layout (no all-rotation or Minkowski statements).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 280000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
/-- Mark at a translated lattice of the mesh. Same mark notation for different choices of level. -/
def moveMark (n : ℤ) (x : Marks (tent Y H) strict) : Marks (tent Y H) strict := by
  obtain hp := marksSpec strict x
  exact ⟨relocate K j n x.val, move_ok K j n hp.1, fun e => chime_cov K j (gaugeT K n) hp.1.paid.choose_spec (hp.2 e)⟩
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
/-- Change of registrar for shift of an arbitrary mark by `d` time ticks of the mesh
on this level. -/
def verandMove (F : Marks (tent Y H) strict) (x : Veranda Y H s j strict F) (d : ℤ) :
    Veranda Y H s j strict (moveMark Y H j strict d F) :=
  ⟨x.rise-d, x.span, x.pos, x.fwd, Eq.trans x.yes (by
    change _=relocate K j (x.rise-d) (relocate K j d F.val)
    rw [relocate_sums K j _ _ (marksSpec strict F).1, sub_add_cancel])⟩
lemma waiting (x : Marks (tent Y H) strict) (d : ℤ) :
    (Ε s) (moveMark Y H j strict d x)=(Ε s) x := by
  let p := Classical.choice (anyporch Y H s j strict (show observable K strict from x))
  exact (drive_response Y H V s Q Qt j strict C f (verandMove Y H s j strict x p d)).symm.trans
    (drive_response Y H V s Q Qt j strict C f p)
theorem all_waiting (x : Τ) (d : ℤ) (u : Axis) : ((Ε s)) ((Υ u) d x) = ((Ε s)) x := by
  -- across every axis using the SAME character
  let Q' := Classical.choice (voyage_H Y H V Q.circuit u 0 strict)
  rw [← across_response Y H V s Q Qt j strict C f ((Υ u) d x) u Q',
    waiting,across_response]
lemma ranks_read (F : Τ) (a : ℕ) : (Ε (s+a)) (upward Y H Q strict F s a) = ((Ε s)) F := moves_up ..
/-- Character connection across axes also makes the 'real structure' independent of which axis
on this *response*, despite θ on the marks not independent. -/
lemma all_mirror (x : Τ) (a : Axis) :
    (Ε s) (dual Y H a strict x)=star ((Ε s) x) := by
  unfold response
  have ht : (located Y H V s Q Qt j strict C (dual Y H a strict x)) = star (located Y H V s Q Qt j strict C x) :=
    Subtype.ext (real_structure Y H V Q Qt j strict C a (Classical.choice (voyage_H Y H V Q.circuit a 0 strict)) (s,x))
  rw [ht, map_star]

def account : Marks (tent Y H) strict →ₗ[ℂ] ℂ := f.toAlgHom.toLinearMap.comp (located Y H V s Q Qt j strict C)
lemma accounts (x : Τ) : account Y H V s Q Qt j strict C f x = response Y H V s Q Qt j strict C f x := rfl

noncomputable def indoor : Hilbert := { space := PositiveLinearMap.GNS (atCharacter Y H V Q Qt j strict C f) }
local notation "Ρ" => indoor Y H V Q Qt j strict C f
noncomputable def procession : driveAlgebra Y H V Q Qt j strict C →⋆ₐ[ℂ]
    (indoor Y H V Q Qt j strict C f).Op := (Φ).gnsStarAlgHom
noncomputable def arrive (x : driveAlgebra Y H V Q Qt j strict C) : indoor Y H V Q Qt j strict C f := appear (Φ) x
local notation "Oa" => arrive Y H V Q Qt j strict C f
noncomputable def doorstep := (arrive Y H V Q Qt j strict C f) 1
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B

lemma arrive_vac : Oa 1=Ω := rfl
lemma arrive_mean (x : 𝔅) : inner ℂ Ω (Oa x) = Φ x := fibre_first (Φ) x
lemma arrive_mul (x y : 𝔅) : (Π x) (Oa y)=Oa (x*y) := fibre_mul (Φ) x y
lemma arrive_vec (x : 𝔅) : Oa x=(Π x) Ω := fibre_vec (Φ) x
lemma arrive_dense : DenseRange (arrive Y H V Q Qt j strict C f) := fibre_dense (Φ)
lemma arrive_pair (x y : 𝔅) : inner ℂ (Oa x) (Oa y) = Φ (star x*y) := fibre_pair (Φ) x y
lemma arrive_cont : Continuous (arrive Y H V Q Qt j strict C f) := fibre_cont (Φ)

lemma ready : ‖Ω‖ = 1 := fibre_vacuum Φ (setupState Y H V Q Qt j strict C f).unit_norm
lemma home (x : PinMark j) : (Π (travelAt Y H V Q Qt j strict C x)) Ω = Ω := by
  obtain ⟨t,hx⟩ := tours j x
  rw [←hx]
  exact VacuumState.stationary Φ _ (travellers Y H V Q Qt j strict C) (setupState Y H V Q Qt j strict C f) t
lemma hinges (n : ℕ) : (Π (ψ s n)) Ω = Ω := home Y H V Q Qt j strict C f (.inl (s,n))
lemma jamb (x : Trans j) (d : marks Μ) : (Π (Σ₁ x d)) Ω=Ω := by
  obtain ⟨u,v,hd⟩ := notch_exists Μ d
  rw [←hd]
  exact home Y H V Q Qt j strict C f (.inr (x,u,v))

lemma entry_read {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) :
    Φ (E₀ s x p) = (Ε s) (actorLabel Y H s j strict x.val) := by
  rw [setup]; unfold response
  exact congrArg f (Subtype.ext (compress_entry Y H V s Q Qt j strict C x p))
lemma entrance_adj {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) :
    star (E₀ s x p)= E₀ s (SlabMark.inverse Y H s j strict w x) p := Subtype.ext (respects Y H V s Q Qt j strict C w x p)
lemma entrance_pair {w u : ℕ} (x : Entry Y H s j strict w) (p : 0 < w)
    (y : Entry Y H s j strict u) (q : 0 < u) :
    (E₀ s x p)*(E₀ s y q)= E₀ s (edit Y H s j strict w u x y) (by omega) :=
  Subtype.ext (edit_comp Y H V s Q Qt j strict C w u x y p q)
lemma entrance_heat {w : ℕ} (p : 0 < w) : (E₀ s (identity Y H s j strict w) p)=ψ s w := Subtype.ext (ticket_birth Y H V s Q Qt j strict C w p)

/-- Actor label given the subalgebra instances. -/
def futureMark : (Tower.Field Y H s j 0 strict) →ₗ[ℂ] Marks (tent Y H) strict where
  toFun v := actorLabel Y H s j strict v
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
local notation "M₁" t:max => futureMark Y H t j strict
lemma future_val (x : 𝔙 s) : ((M₁ s) x).val=x.val := rfl

/-- Incoming actor in the *selected* OS Hilbert. Width of these labels is arbitrary so
can be stated on every point of the tower, including strict `Observ` tests. -/
private lemma bud_equal_of_le (w n) (x : Entry Y H s j strict w) (y : Entry Y H s j strict n) (p : 0 < w) (q : 0 < n)
     (h : y.val=x.val) (v : w≤n) : Oa (E₀ s x p) = Oa (E₀ s y q) := by
   obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le v
   have he : E₀ s y q = (E₀ s x p)*(ψ s k) :=
     Subtype.ext (shape_right Y H V s Q Qt j strict C w w x p k y (congrArg Subtype.val h))
   rw [he, arrive_vec Y H V Q Qt j strict C f (E₀ s x p), arrive_vec Y H V Q Qt j strict C f ((E₀ s x p)*(ψ s k)), map_mul]
   change _=(Π (E₀ s x p)) ((Π (ψ s k)) Ω); rw [hinges]
private lemma bud_equal_entry (w n) (x : Entry Y H s j strict w) (y : Entry Y H s j strict n) (p : 0 < w) (q : 0 < n) (h : y.val=x.val) :
    Oa (E₀ s x p) = Oa (E₀ s y q) := by
   rcases le_total w n with v|v
   · exact bud_equal_of_le Y H V s Q Qt j strict C f w n x y p q h v
   exact (bud_equal_of_le Y H V s Q Qt j strict C f n w y x q p h.symm v).symm
private lemma opened (x : 𝔙 s) : ∃ v : Ρ, ∀ (w : ℕ) (y : Entry Y H s j strict w)
    (p : 0 < w), y.val=x → Oa (E₀ s y p) = v := by
  obtain ⟨w,p,y,rfl⟩ := artist_fits_slab Y H s j strict x
  refine ⟨Oa (E₀ s y p), fun n y' p' h => ?_⟩
  symm; exact bud_equal_entry Y H V s Q Qt j strict C f w n y y' p p' h
noncomputable def bud (x : 𝔙 s) : indoor Y H V Q Qt j strict C f := (opened Y H V s Q Qt j strict C f x).choose
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
lemma turns {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) : a₀ s (x.val) = Oa (E₀ s x p) := ((opened Y H V s Q Qt j strict C f x.val).choose_spec w x p rfl).symm
lemma call (x : 𝔙 s) : inner ℂ Ω (a₀ s x) = (Ε s) ((M₁ s) x) := by
  obtain ⟨w,p,y,rfl⟩ := artist_fits_slab Y H s j strict x
  rw [turns Y H V s Q Qt j strict C f y p,arrive_mean]
  exact entry_read Y H V s Q Qt j strict C f y p
lemma root : a₀ s (unity Y H j 0 strict s) = Ω := by
  let x := SlabMark.identity Y H s j strict 1
  rw [show unity Y H j 0 strict s=x.val from rfl, turns Y H V s Q Qt j strict C f x zero_lt_one, arrive_vec]
  rw [show (E₀ s x zero_lt_one)=ψ s 1 from entrance_heat Y H V s Q Qt j strict C zero_lt_one]
  exact hinges Y H V s Q Qt j strict C f 1

/-- OS Gram equality. Also a recipe for products in this C*-state. -/
lemma earns (x y : 𝔙 s) : inner ℂ (a₀ s x) (a₀ s y) = (Ε s) ((Θ ((M₁ s) x))*((M₁ s) y)) := by
  obtain ⟨w,p,u,rfl⟩ := artist_fits_slab Y H s j strict x
  obtain ⟨r,q,v,rfl⟩ := artist_fits_slab Y H s j strict y
  rw [turns Y H V s Q Qt j strict C f u p, turns Y H V s Q Qt j strict C f v q,
    arrive_pair,entrance_adj,entrance_pair, entry_read]
  -- pay by moving translated mirror back. Fock mirror orientation.
  rw [← waiting Y H V s Q Qt j strict C f ((Θ (_))*_) w]
  apply congrArg ((Ε s)); apply Subtype.ext
  simp only [actorLabel, editor]
  change mirror K j (gaugeT K w) u.val.val * relocate K j w v.val.val = relocate K j w ((mirror K j 0 u.val.val)*v.val.val)
  rw [relocate_mul, mirror_cancel K j _ 0 (test_entry Y H s j strict u), sub_zero, gaugeT_zero]
lemma flourishes (t : ℕ) (p : s ≤ t) (x : 𝔙 s) :
    a₀ t (Raise Y H Q.circuit j 0 strict s t p x)= a₀ s x := by
  obtain ⟨w,k,u,rfl⟩ := artist_fits_slab Y H s j strict x
  let a := furnished Y H s Q j strict w u t p
  let e : 0 < L₀^(t-s)*w := Nat.mul_pos (pow_pos Λ.R.L.property _) k
  change a₀ t a.val= _
  rw [turns Y H V t Q Qt j strict C f a e,turns Y H V s Q Qt j strict C f u k]
  exact congrArg (Oa) (Subtype.ext (refined_box Y H V s Q Qt j strict C w u k t p).symm)
lemma earns_above (t r : ℕ) (p : s ≤ t) (q : r ≤ t) (x : 𝔙 s) (y : 𝔙 r) :
    inner ℂ (a₀ s x) (a₀ r y) = (Ε t)
      ((Θ (upward Y H Q strict ((M₁ s) x) s (t-s)))*(show Τ from upward Y H Q strict ((M₁ r) y) r (t-r))) := by
  rw [← flourishes Y H V s Q Qt j strict C f t p, ← flourishes Y H V r Q Qt j strict C f t q,
    earns]; rfl

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.earns
