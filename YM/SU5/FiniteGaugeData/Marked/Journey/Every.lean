import YM.CF.Buffered.Form

/-!
# RP beginning at any fixed observation level within a Donor purchase.
Follows Buffered.DonorGram (here work backwards for the iteration
so can take every supported mark at EACH native level).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
variable (A : Steps m B L) {D J w U : ℕ} (v : Stencil.LaurentRadius j L D) (L' : 3 ≤ L.val) (T : Granted P X R q d n Q A J)
variable (t : ∀ k<n,LoomLaw (R k) w) (p : Margin L D w J U)
local notation "Ω" i:max=> cell m B L i
local notation "ρ" i=> denZ (X i) P (R i)
local notation :max "out_" i:max=>nextMark (ho:=ho) (j:=j) X R q d Q A i
include P v L' T t p
lemma sooty (a:Axis){i:ℕ} (h:i<n)(s:ℤ){f:Mark (Ω i)}(u:AtSupport false (band (Ω i) a s U) f):
    AtSupport false (band (Ω (i+1)) a ((L.val:ℤ)*s) U) ((out_ i) f) ∧
    markedRead (reflMark a s f*f) (R i) (ρ i) = markedRead (reflMark a ((L.val:ℤ)*s) ((out_ i) f)*(out_ i) f) (R (i+1)) (ρ (i+1)):=by
  obtain ⟨g⟩:= T.grant i h; obtain ⟨V,b,c,Y,l⟩:= g.cap
  let K:= apt m B L i
  have we:= T.branch i h
  have vt:= surround K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ u (t _ h) (T.aligned i h)
  rw [T.radius i h] at vt
  refine ⟨vt.mono (margin_band a _ p K rfl L'),?_⟩
  have hz:= separated_mult K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ _ (u.refl a s) u (t _ h) (fun x px y py=> margin_separate a s p x y px py)
  have hs:= rising K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) a s (T.aligned i h) u we Y (g.power.symm ▸ v) g.legal.1 g.legal.2
  rw [single_num P X R q d n Q A v T (((u.refl a s).mono (subset_univ _)).mulM (u.mono (subset_univ _))) h]; unfold nextMark; rw [hz,hs]; rfl

variable (Z:Buffered.Donor P X R n)
include Z
local notation "ζ" z:max=> gaugeShift B z
lemma onward (a:Axis) (i:ℕ)(h:i≤ n)(z:ℤ)(f:Mark (Ω i))(w_:AtSupport false (band (Ω i) a (ζ z) U) f):
    0 ≤ markedRead (reflMark a (ζ z) f*f) (R i) (ρ i) := by
  let E(i:ℕ):= ∀ z:ℤ,∀ f:Mark (Ω i),AtSupport false (band (Ω i) a (ζ z) U) f → 0 ≤ markedRead (reflMark a (ζ z) f*f) (R i) (ρ i)
  have he: E n:=by
    intro s f u; obtain ⟨X',Y,w,h,V⟩:= Z.grants; obtain ⟨x,y,t,s',A_⟩:=Z.roof
    exact summit_gram P _ _ Z.pin Z.scroll _ _ Z.top h V s' A_ (T.noTies n le_rfl) a s _ (u.mono (band_anti a (ζ s) (Nat.zero_le _))) Z.warm
  have ht(i:ℕ)(h:i<n)(e:E (i+1)):E i:=by
    intro s f u; obtain ⟨r,h'⟩:= sooty P X R q d n Q A v L' T t p a h (ζ s) u
    rw [show (L.val:ℤ)*(ζ s)=gaugeShift B (L.val*s:ℤ) from by unfold gaugeShift; ring] at r h'; rw [h']; exact e _ _ r
  have H(k:ℕ)(h:k≤n):E (n-k):=by
    induction k with | zero=>simpa using he | succ k ih=> exact ht (n-(k+1)) (by omega) ((show n-k=n-(k+1)+1 by omega) ▸ ih (by omega))
  exact (show E i from (show n-(n-i)=i by omega) ▸ H (n-i) (Nat.sub_le ..)) z f w_

end YM.CF.Buffered.Afterglow.Journey
