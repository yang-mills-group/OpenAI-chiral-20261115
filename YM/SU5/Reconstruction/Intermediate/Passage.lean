import YM.SU5.Reconstruction.Intermediate.Placement
import YM.SU5.Reconstruction.Intermediate.Climate
/-! Pose stewardship across ARCH. Check every cap norm really sees the low charge, including through Stamp footprints staying T-positive even when sVV varies. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker -- may clobber K.Gauge representation norms
attribute [local instance] opCStarAlgebra
variable (m t s:ℕ)
local notation "𝗠" i:max j:max=> Journey.side Y i j
local notation "🎨" i:max=> (Y.voyage m).CapeT i
open LocalLimit.Intermediate Harbour
variable (T:ℕ) (F:Intermediate.Room T→ Corr (Λ.Ctor (Y.ir m) T))(z:Intermediate.Room T)
variable (P:Ramp) (r:ℝ≥0)
local notation "Θ" f:max=> Tilted.Ramp.bill P f
local notation "QB" => Harbour.screen Y m t T F z
local notation "pB" j:max => partitionZ (QB j) Λ.U ((Y.voyage m).CapeT j)
local notation "fe" => consultancy Y (i:=m) (k:=t) (s:=T) (F:=F) z
local notation "wb" i:max=> Harbour.earns Y m t T F z i
variable {U V' : Finset Cover}
local notation "Bu" n:max=> volumeAround Λ l n U
local notation "Bv" n:max=> volumeAround Λ l n V'
open Push.SectorMeasure
-- use arbitrary F,upwards uncert after startup not used
noncomputable def assembleNext (f:Mark (𝗠 m s)) : Mark (𝗠 m (s+1)):= nextMark (ho:=Λ.R.odd_side) (j:=Λ.K.j) (Harbour.screen Y m t T F z) (Y.voyage m).CapeT Chi.canonical Λ.J.d (Harbour.earns Y m t T F z) (steps Λ.V (Y.ir m) Λ.block (Y.uv t)) s f
noncomputable def climb (f:Mark (Journey.side Y m s)) (n:ℕ) : Mark (𝗠 m (s+n)) := match n with
 | 0=>f
 | n+1=> assembleNext Y m t (s+n) T F z (climb f n)
local notation "τ" n:max=> climb Y m t s T F z n -- f n?
local notation "fop" => assembleNext Y m t s T F z
local notation "A" => steps Λ.V (Y.ir m) Λ.block (Y.uv t) s
variable (ht:T ≤ Y.uv t) (pf: Harbour.campus Y m t T F)(tz:Harbour.phaseMoney Y m t T F z)
include ht pf tz
local notation "ρ" => Harbour.installed Y ht pf tz
local notation "Kq" => (Vale.apt (Y.ir m) Λ.block Λ.R.L s)
lemma step_pays (i:s<T) {g:Mark (Journey.side Y m s)}{u:Bool}(p:AtSupport u (Satin.region U (𝗠 m s)) g): AtSupport u (Satin.region (wingspan Λ l U) (𝗠 m (s+1))) (assembleNext Y m t s T F z g):= by
 obtain ⟨l'⟩:= (ρ).grant s i
 have h:= surround Kq A Λ.K.j (wb s).val (QB (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (QB (s+1)).beta ((Y.voyage m).CapeT s) (Journey.legal _) ((Y.voyage m).ownership s).paid.bill ((ρ).branch s i) l'.legal.1 l'.legal.2 _ p (Journey.tissue Y m s) ((ρ).aligned s i)
 rw [(ρ).radius s i] at h
 exact h.mono (next_contains U _ (𝗠 m s) Kq)
lemma step_angle (i:s<T){f:Mark (Journey.side Y m s)} (u:AtSupport false (Satin.region U (𝗠 m s)) f): fop (P.bill f)= P.bill (fop f) :=
 Ramp.RampRise Kq A Λ.K.j (wb s).val _ Λ.R.odd_side _ _ (QB (s+1)).beta ((Y.voyage m).CapeT s) P ((ρ).aligned s i) u ((ρ).branch s i) ((Y.voyage m).ownership s).paid (Journey.legal Λ) (threshold Y).1 (threshold Y).2
lemma step_tensor (i:s<T){f:Mark (Journey.side Y m s)} (p:CanInspect Y m s P r U V' f) : fop (P.bill f*f) = P.bill (fop f) * fop f:=by
 rw [←step_angle Y m t s T F z P ht pf tz i p.siteF]
 exact separated_mult Kq A Λ.K.j (wb s).val _ Λ.R.odd_side _ _ (QB (s+1)).beta _ (Journey.legal Λ) ((Y.voyage m).ownership s).paid.bill ((ρ).branch s i) (threshold Y).1 (threshold Y).2 _ _ p.siteT p.siteF (Journey.tissue Y m s) (p.gap Y m s P r)
lemma step_colors (i:s<T){f:Mark (Journey.side Y m s)}{b : Bool}(p:AtSupport b (Satin.region U (𝗠 m s)) f)(u:covariant f) : covariant (assembleNext Y m t s T F z f):= fun w=>
 pushHarmony Kq A Λ.K.j (wb s) _ Λ.R.odd_side Chi.canonical Λ.J.d (QB (s+1)).beta _ (Journey.legal _) ((Y.voyage m).ownership s).paid ((ρ).branch s i) (threshold Y).1 (threshold Y).2 ((ρ).aligned s i) p.env p w (u _)
variable {f:Mark (Journey.side Y m s)}
local notation "hr" n:max => climb Y m t s T F z f n
variable (p:AtSupport false (Satin.region U (Journey.side Y m s)) f)
 (p':AtSupport false (Satin.region V' (Journey.side Y m s)) (P.bill f))
include p p'
lemma ascent (n:ℕ) (i:s+n ≤ T) : AtSupport false (Satin.region (Bu n) (𝗠 m (s+n))) (hr n) ∧ AtSupport false (Satin.region (Bv n) (𝗠 m (s+n))) (P.bill (hr n)) ∧ (covariant f → covariant (hr n)) := by
 induction n with
 | zero=> exact ⟨p,p',id⟩
 | succ n ih=>
   obtain ⟨a,b,c'⟩:=ih (by omega)
   let f₀:=hr n
   have g: s+n<T:=by omega
   let f₁ := assembleNext Y m t (s+n) T F z f₀
   refine ⟨step_pays Y m t _ T F z ht pf tz g a,?_,fun x=>step_colors Y m t _ T F z ht pf tz g a (c' x)⟩
   change AtSupport false (Satin.region (wingspan Λ l (Bv n)) (𝗠 m (s+n+1))) (P.bill (assembleNext Y m t (s+n) T F z f₀)); rw [←step_angle Y m t (s+n) T F z P ht pf tz g a]
   exact step_pays Y m t (s+n) T F z ht pf tz g b
omit p p'
lemma budget_of (i:s<T){g:Mark (Journey.side Y m s)}(b:AtSupport false Finset.univ g): fe s g= fe (s+1) (fop g):= by
 have hw:= Harbour.funded_compare Y ht pf z tz s (s+1) i.le i
 unfold Harbour.consultancy; rw [hw]; exact congrArg (· / partitionZ (QB (s+1)) Λ.U ((Y.voyage m).CapeT (s+1))) (single_num Λ.U _ _ _ _ _ _ _ (Journey.legal Λ) (ρ) b i)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
