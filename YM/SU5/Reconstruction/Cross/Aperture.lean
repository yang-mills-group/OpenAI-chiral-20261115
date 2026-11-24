import VerifiedSatinSelectedSectors
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
/-!
# Native atlas of time-ordered marking positions
See `the construction notes`. Scope Euclidean. `v` in placement Λ already in physical
level-zero MATTER units. Γ is the `mill` mesh from Selected.
This convention extends throughout this Atlas. Eχ used on non-neutral labels also
(in its `observable false` sense, even), not declaring those gauge-invariant.
-/
section
variable (s : ℕ) (j : Axis)
structure Gate (f : Marks (tent Y H) false) where
  width : ℕ
  pos : 0 < width
  entry : Entry Y H s j false width
  base : ℤ
  price : f.val= SlabMark.relocate (tent Y H) j base entry.val.val
  start : ℤ
  slack : ℕ
namespace Gate
variable {f : Marks (tent Y H) false} (g : Gate Y H s j f)
-- test before precision accounting. At t≥s which y-grid for kernels? separate.
variable {Y H s j}
def full (g : Gate Y H s j f) : ℕ := g.width+g.slack
def left (g : Gate Y H s j f) (v : Axis → ℝ) : ℝ := (v j) + bell Μ s g.base - bell Μ s g.start
def right (g : Gate Y H s j f) (v : Axis→ℝ) : ℝ := bell Μ s g.slack - g.left v
def admits (g : Gate Y H s j f) (v : Axis→ℝ) := 0 ≤ g.left v ∧ 0≤g.right v
def within_ (g : Gate Y H s j f) (v : Axis→ℝ) := 0 < g.left v ∧ 0<g.right v
lemma allows (g : Gate Y H s j f) {v : Axis→ℝ} (p : g.within_ v) : g.admits v :=⟨p.1.le,p.2.le⟩
theorem open_gate (g : Gate Y H s j f) : IsOpen {v: Axis→ℝ|g.within_ v} := by
 have ht : Continuous (fun v=> g.left v) := ((continuous_apply j).add continuous_const).sub continuous_const
 exact (isOpen_lt continuous_const ht).inter (isOpen_lt continuous_const (continuous_const.sub ht (g:=fun v=> g.left v) (f:=fun _=> bell Μ s g.slack))) -- syntax
end Gate
end

section physical_grid
-- TODO surround later
variable (X : Calibration) (j : Axis)
-- useful translation identities
lemma cad_congr {x y : Cover} (t : List Axis) (F : Family X)
    (p : ∀ i∈t,x i=y i) : cad X t x F=cad X t y F:=by
  induction t with
  | nil=> exact Eq.refl (F : Family X)
  | cons i t ih=> rw [cad_step,cad_step,p i List.mem_cons_self, ih (fun i e=>p i (List.Mem.tail _ e))]
lemma chart_unitStep {v:ℤ} (x:Family X) (p:TestFamily X true x) :
    Vacancy.chart X (v • step j) x = SlabMark.relocate X j v x := by
  rw [chart_piece X j _ p]
  have h(i:Axis)(u:i∈spare j (look j)): (v • step j:Cover) i=0:=by
     obtain ⟨w,h,rfl⟩:=List.mem_map.mp u; simp [w.property] -- use simp
  rw [cad_congr X _ x (y:=0) h,cad_zero X _ p]; congr 2; simp
end physical_grid

abbrev seeMesh (M:Mesh) := Axis→ marks M
-- use `placement` aliases, generic M
noncomputable abbrev toR {M:Mesh}(x:seeMesh M) : Axis→ℝ:=fun i=>(x i:ℝ)
noncomputable def grid (M : Mesh)(s:ℕ)(v:Cover):seeMesh M:=fun i=> notch M s (v i)
lemma grid_eval (M : Mesh) (s:ℕ) (v:Cover) (i:Axis) : ((grid M s v i : marks M):ℝ)=bell M s (v i):=rfl
lemma bell_sub (M : Mesh)(s:ℕ) (x y:ℤ): bell M s (x-y)=bell M s x-bell M s y:=by simp [bell,_root_.sub_mul]
lemma bell_nonneg (M:Mesh)(s:ℕ)(x:ℤ): 0≤bell M s x ↔ 0≤ x:=by simpa only [bell,Int.cast_zero,zero_mul] using (bell_le M s 0 x)
lemma castor_nat (M:Mesh)(s t n:ℕ): castor M s t n = (MeshClock.acts M s t n:ℕ):=by simp [castor, MeshClock.acts]
lemma notch_neg (M:Mesh)(s:ℕ)(i:ℤ): notch M s (-i)= -notch M s i:=Subtype.ext (by change bell _ _ _ = - bell _ _ _; simp [bell])
lemma grid_neg (M:Mesh)(s:ℕ)(w:Cover): -(grid M s w)= grid M s (-w):= funext fun i=> (notch_neg M s (w i)).symm
lemma real_grid_dense (M:Mesh) : DenseRange (toR (M:=M)) := by
 -- Pi
 exact DenseRange.piMap (f:=fun (_ : Axis) (x : marks M)=> (x:ℝ)) (fun _ : Axis=> (daylight M).denseRange_val)
lemma toR_cont (M:Mesh) : Continuous (toR (M:=M)) := continuous_pi fun i=> continuous_subtype_val.comp (continuous_apply i)
lemma grid_higher (M:Mesh)(v:seeMesh M) : ∀ᶠ t : ℕ in atTop, ∃ i:Cover, grid M t i = v:=by
  have h(i:Axis): ∀ᶠ t:ℕ in atTop, ∃ z:ℤ, notch M t z=v i := by
    obtain ⟨s,z,hz⟩ := notch_exists M (v i); filter_upwards [eventually_ge_atTop s] with t ht
    exact ⟨_, (notch_up M s t ht z).trans hz⟩
  filter_upwards [eventually_all.mpr h] with t ht
  choose a ha using ht; exact ⟨a,funext ha⟩
lemma widths_up (M:Mesh)(s t x y:ℕ) : (MeshClock.acts M s t (x+y):ℕ)= MeshClock.acts M s t x+ MeshClock.acts M s t y:= adds ..
-- `T` Denote the time-mark unit 8B as mill M. For given ε requests may use any rung high enough.
lemma castor_add (M:Mesh)(s t:ℕ)(x y:ℤ) : castor M s t (x+y)=castor M s t x+ castor M s t y:=by simp [castor,mul_add]

namespace Gate
variable {Y H} {s t : ℕ} {j : Axis}
variable {f : Marks (tent Y H) false} (g : Gate Y H s j f) (p : s≤t) (v:Cover)
include p
local notation "Λ₀" => (timeMesh Λ)
local notation "X" q:max => MeshClock.acts Λ₀ s t q
lemma fees (h : g.admits (toR (M:=Λ₀) (grid Λ₀ t v))) :
    ∃ a b:ℕ, g.left (toR (M:=Λ₀) (grid Λ₀ t v))=whenly Λ₀ t a ∧
           g.right (toR (M:=Λ₀) (grid Λ₀ t v))=whenly Λ₀ t b ∧
           a+b= MeshClock.acts (timeMesh Λ) s t g.slack ∧
           (a:ℤ)= v j + castor (timeMesh Λ) s t g.base - castor (timeMesh Λ) s t g.start := by
 let a:= v j + castor Λ₀ s t g.base-castor Λ₀ s t g.start
 let b:=castor Λ₀ s t g.slack - a
 have he: g.left (toR (M:=Λ₀) (grid Λ₀ t v))=bell Λ₀ t a:=by unfold left a; rw [bell_sub,bell_add, refineZ _ s t p, refineZ _ s t p]; rfl
 have hf: g.right (toR (M:=Λ₀) (grid Λ₀ t v))=bell Λ₀ t b:=by unfold b right; rw [he,bell_sub Λ₀ t (castor Λ₀ s t g.slack) a,refineZ _ s t p]
 have ha : 0≤ a:= (bell_nonneg Λ₀ t a).mp (he ▸ h.1)
 have hb : 0≤ b:= (bell_nonneg Λ₀ t b).mp (hf ▸ h.2)
 have ha':(a.toNat:ℤ)=a:=Int.toNat_of_nonneg ha
 have hb':(b.toNat:ℤ)=b:=Int.toNat_of_nonneg hb
 refine ⟨a.toNat,b.toNat,?_,?_,?_,ha'⟩
 · rw [he]; exact (congrArg (bell Μ t) ha'.symm).trans (natural_time Μ t a.toNat)
 · rw [hf]; exact (congrArg (bell Μ t) hb'.symm).trans (natural_time Μ t b.toNat)
 have h:a+b= (X g.slack:ℕ):=by unfold b; rw [castor_nat]; omega
 omega
end Gate
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.Gate.fees
