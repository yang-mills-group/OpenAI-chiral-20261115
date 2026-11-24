import YM.SU5.Reconstruction.Cashier.AtMint
/-! Real physical volumes for sensing! -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 290000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
open Chambers

-- spatial/times symmetric planning permit. length clock as Height positive
variable (s w :ℕ)
def alcove (g:ℝ): Set RSpace := {x|∀ i: Axis, x∈ strip i 0 g}
lemma alcove_in_strip (g:ℝ)(i:Axis): alcove g ⊆ strip i 0 g:=fun _ q=>q i
lemma alcove_mono {a b:ℝ} (p:a≤b): alcove a ⊆ alcove b:=fun _ h i=> ⟨(h i).1,(h i).2.trans p⟩ -- implicit coerces?
lemma alcove_compact (g:ℝ): IsCompact (alcove g):=by
 have hp: alcove g= Set.univ.pi fun (_:Axis)=> Set.Icc (0:ℝ) g := Set.ext (fun i=> ⟨fun h a _=> h a,fun h a=> h a (Set.mem_univ a)⟩)
 rw [hp]; exact isCompact_univ_pi (fun i=> isCompact_Icc)
lemma alcove_separate (a b:ℝ) (p:RSpace){j:Axis} (t:a<p j) : Disjoint (alcove a) (slides p (alcove b)):=by
 apply Set.disjoint_left.mpr; rintro _ h ⟨_,g,rfl⟩; have hx:=(h j).2; simp only [Pi.add_apply] at hx; linarith [(g j).1]

/- all clock measures in fermion-mesh height -/
def hOne (Λ:Preparation) (s w:ℕ):ℝ≥0:= whenly (timeMesh Λ) s w
def hAll (Λ:Preparation) (s w n:ℕ):ℝ≥0:= whenly (timeMesh Λ) s (2*w*n)
def bOne (Λ:Preparation) (s w:ℕ): marks (timeMesh Λ):= notch (timeMesh Λ) s w
def bAll (Λ:Preparation) (s w n:ℕ): marks (timeMesh Λ):= notch (timeMesh Λ) s (2*w*n:ℕ)
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b"=> bOne Λ s w
local notation "ℓ" n:max=> bAll Λ s w n
lemma bTime : (b:ℝ)=(hOne Λ s w:ℝ):= natural_time ..
lemma aTime (n:ℕ) : ((bAll Λ s w n):ℝ)=(hAll Λ s w n:ℝ):= natural_time ..
lemma hall_schedule (n:ℕ): hAll Λ s w n = (2 * n) * hOne Λ s w:= by simp only [hOne,hAll,whenly]; push_cast; ring -- nnreal
lemma hstep (n:ℕ): ((hAll Λ s w (n+1)):ℝ)=(2:ℝ)*hOne Λ s w+hAll Λ s w n:= by simp_rw [hall_schedule]; push_cast; ring
@[simp] lemma bbeginning : ℓ 0=0:= by simp [bAll,notch_zero]
lemma gPositive {w:ℕ}(hw:0<w): 0<(hOne Λ s w:ℝ):= when_pos (timeMesh Λ) s w hw
lemma tPositive {w:ℕ}(hw:0<w){n:ℕ}(ht:0<n): 0<(hAll Λ s w n:ℝ):= when_pos (timeMesh Λ) s (2*w*n) (by positivity)
open Lat
-- `$granite(w)` moves along the positive diagonal exactly at count w*2. -/
def granite (w:ℕ): Cover:=fun _ => ((2*w:ℕ):ℤ)
lemma strikes (i:Axis) : ((stamps Λ s (granite w) i:ℝ))=2*(g₁:ℝ) := by
 have he:= aTime (Λ:=Λ) s w 1; rw [hall_schedule] at he; push_cast at he -- may simp width
 simpa only [bAll,Nat.mul_one,stamps_at,granite,Nat.cast_one,mul_one,one_mul] using he
local notation "r₁"=> coordinates Λ (stamps Λ s (granite w))
lemma first_in {w:ℕ}(hw:0<w)(n:ℕ) : alcove (hOne Λ s w) ⊆ alcove (hAll Λ s w (n+1)):=
 alcove_mono (by rw [hstep]; linarith only [gPositive (Λ:=Λ) s hw,(hAll Λ s w n).property])
lemma second_in (n:ℕ) : slides (r₁) (alcove (hAll Λ s w n))⊆ alcove (hAll Λ s w (n+1)):=by
 rintro _ ⟨x,p,rfl⟩ i; specialize p i; change 0≤ x i+((stamps Λ s (granite w) i):ℝ) ∧ _
 simp only [Chambers.strip,Set.mem_setOf_eq] at p; set a:=x i with ha; change _ ∧ a+((stamps Λ s (granite w) i):ℝ)≤ (hAll Λ s w (n+1):ℝ)
 rw [strikes,hstep]; constructor <;> linarith only [p.1,p.2,(hOne Λ s w).property]
lemma dedicated {w:ℕ}(h :0<w)(n:ℕ) : Disjoint (alcove (hOne Λ s w)) (slides (coordinates Λ (stamps Λ s (granite w))) (alcove (hAll Λ s w n))):= by
 apply alcove_separate (j:=0); rw [coord_at,strikes]; linarith only [gPositive (Λ:=Λ) s h]

variable {S:Finset Cover}{q d:Bool}
lemma roomKit (p:∀ j, Between (tent Y H) j 0 (ruler Λ.block * w) S) {f:Dome K}{b':Bool} (h: InTest (tent Y H) d S false f.val) (hV:b'=true → CovCover (tent Y H) f.val) : f∈insideAt Λ l K b' (alcove g₁) s:=by
 have hp: PhaseChoice.SupportedPhysically Λ l s S (alcove g₁):=by rw [supported_iff]; exact fun _ h i=> (supported_iff ..).1 ((strip_seats Y H i s w).2 (p i)) h
 exact (mem_insideAt ..).2 ⟨⟨S,by cases d; exact h.widen; exact h, hp⟩,hV⟩

-- one-level placement proof works at ALL future refinements
variable {J : Calibration} {x y : Dome (tent Y H)}{w}
def lined (J:Calibration)(w:ℕ)(y:Dome J): Dome J:= reposition J (granite w) y
lemma lineNotes {w:ℕ}(p:0<w){n:ℕ} (a:x ∈ insideAt Λ l K q (alcove (hOne Λ s w)) s) (hp:y∈insideAt Λ l K q (alcove (hAll Λ s w n)) s) : x * lined K w y ∈ insideAt Λ l K q (alcove (hAll Λ s w (n+1))) s :=
 Subalgebra.mul_mem _ (insideAt_mono (first_in (Λ:=Λ) s p n) a) (insideAt_mono (second_in (Λ:=Λ) s w n) (here_cov Y H q _ s _ y hp))
include V in
lemma level_exact {w:ℕ}(p:0<w){n:ℕ} (a:x∈insideAt Λ l K q (alcove (hOne Λ s w)) s) (h:y∈insideAt Λ l K d (alcove (hAll Λ s w n)) s): ticket Y H G s (x * lined K w y)= ticket Y H G s x * move K (stamps Λ s (granite w)) (ticket Y H G s y):=by
 rw [move_at Y H V G (stamps Λ s (granite w)) s y (granite w) rfl]
 exact ticket_separated Y H G a (here_cov Y H _ _ _ _ y h) (dedicated s p n)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.level_exact
