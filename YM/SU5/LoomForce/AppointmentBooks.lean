import YM.SU5.LoomForce.WakeBooks
import YM.SU5.LoomForce.Stage1
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Laurent Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Clock Hookah Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Gleam Gleam.Wake
open Jewel Onyx Vale Pressure
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
universe u
variable {I : Type u} [Fintype I] (P : Spine) (K : P.Register) {X : ℝ}{Mc:ℕ} (J: PreparedInvestment P K X Mc)
local notation "Γ" => P.run
local notation "Λ" => P.par

local notation "F₀" => Prototype.goldF
variable (A:ℝ)(f:I → PlaqAxes)(g:I → Twah.DirSpin) (T:I→Gaia) (W:ℕ→I→ Cover)
  (hA : 0 < A) (a:∀ i, Appoint P.par A (fun s=> W s i) (T i))
def feather (f:I→PlaqAxes)(g:I→Twah.DirSpin)(x:I→ Cover)(i:I):Staff:= adjacent (x i) (f i) (g i)

include a hA
lemma living_at (H:ℝ) (h:A<H) {r:ℕ}(p:4 ≤ r) : Packs P H (fun s=>feather f g (W s)) (fun _ => r) := by
  constructor
  exact lt_trans hA h
  have v := Filter.eventually_all.mpr (fun i:I=>fitting P hA (a i) (a i) (f i) (f i) (g i) (g i) h p)
  filter_upwards [v] with s w; apply Eventually.of_forall; intro n
  choose e t u using w
  let Z:ℕ:= univ.sup e; let N:=matterSide P s n; let o:Seat N:=wrap (More N) 0
  refine ⟨Z,0,o,?_,by simpa using (BProof.coin_pos .. |>.le),?_⟩
  · cases isEmpty_or_nonempty I
    · simp only [Z,univ_eq_empty, Finset.sup_empty]; change (↑(0:ℕ):ℝ)≤ _; simpa using (BProof.coin_pos .. |>.le)
    obtain ⟨i,-,hi⟩:= Finset.sup_mem_of_nonempty (s:=univ) (f:=e) univ_nonempty -- uses typeof .3?
    rw [show Z=e i from ?_]; exact t i; exact hi.symm
  intro i; refine ⟨((u i N).1).trans (Corona.halo_mono (Finset.le_sup (mem_univ i)) (Subset.refl _)), adj_pays _ _ _ p⟩

omit [Fintype I] in
lemma appointment_consignment (q : ∀ i j,T i=T j→∀ᶠ s in atTop,W s i=W s j) : Consigned P A (fun s=>feather f g (W s)) g f T T := by
  refine ⟨hA, ?_, ?_,fun s i=>rfl,fun s i=>rfl,q⟩
  · exact a
  exact a

def carpet (P : Spine) (tag : I → Sewer) (A : ℝ) (f : I→ PlaqAxes) (g : I→ Twah.DirSpin) (β : ℕ → ℝ) (r : ℕ) (L : List I)
    (u : I → Cover) (s : ℕ) : Papal.Weaver := threadRoll P tag L A s β (feather f g u) r
def inked (tag : I → Sewer) (f : I→ PlaqAxes) (g : I→ Twah.DirSpin)(T : I→ Gaia)(L : List I):ℂ:=
    (1/2:ℂ)^L.length * quoted tag L (wakeZ g T) (wakeG T f)
variable (tag:I→ Sewer)(L:List I){l:ℕ}(p:4 ≤ l)
include J p
lemma uptakes {σ : ℕ → ℕ} {β : ℕ → ℝ} (t:Pooling Γ (takenVolume P) (takenCutoff P) σ β)
    (q : ∀ i j,T i=T j→∀ᶠ s in atTop,W s i=W s j) (u : L.Pairwise (fun i j=> T i≠T j)) :
    Tendsto (fun s => infiniteE P s (carpet P tag A f g β l L (W s) s)) atTop (𝓝 (inked tag f g T L)) :=
    true_books _ _ J _ t (living_at P A f g T W hA a (A+1) (by linarith) p)
      (appointment_consignment P A f g T W hA a q) tag L u

omit J hA a
omit [Fintype I] in
lemma living_support (C : I→ Cover)(s : ℕ)(β : ℕ→ℝ) : InTest P.calibration true
    (wholeSky (feather f g C) l L) false (household P.calibration (carpet P tag A f g β l L C s)) := by
  unfold carpet; let W0(s:ℕ) := feather f g C; let b(s:ℕ):=l; have h:=restore (A:=A) (b:=b) (β:=β) P W0 tag L s; rw [show feather f g C=W0 s from rfl,h]
  exact (ream_label _ _ _ tag _ (fun i=>adj_pays _ (f i) (g i) (e:=0) p) _ L P.calibration).smul _

omit p [Fintype I] in
lemma living_cert (C:I→ Cover)(s : ℕ)(β : ℕ→ℝ) : CovCover P.calibration (household P.calibration (carpet P tag A f g β l L C s)) := by
  unfold carpet; let W0(s:ℕ) := feather f g C; let b(s:ℕ):=l; have h:=restore (A:=A) (b:=b) (β:=β) P W0 tag L s; rw [show feather f g C=W0 s from rfl,h]; exact covariant_scale _ (fun m=> speak_many _ _ _ _ tag L (W0 s) (b:=l) _) _ -- uses local open syntax

-- calibration identities CP1
omit p [Fintype I]
theorem stitch_yes (s l : ℕ)(β : ℕ → ℝ) (B: Staff) : stitch P A s β B l none= weaving P A B l s β := by
  unfold stitch weaving; rw [spool,smul_smul,split_ampl P]; apply congrArg (fun x:ℂ=> x • B.rungWeave _ _ _); unfold glow; push_cast; ring
private lemma adjust (s : ℕ) : (sPow P.par s A:ℂ)^3/16 = ((frayR P.par A s:ℂ)^3/2) * (zoomR P.par A s:ℂ)^3 := by
  let x:= (sPow P.par s A:ℂ); have hx : x^2 ≠0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (BProof.coin_pos ..|>.ne'))
  have he:= split_ampl (A:=A) P s; unfold ampl at he; apply mul_right_cancel₀ hx; exact Eq.trans (by ring : x^3 /16 * x^2=x^5/16) he
lemma stitch_tone (s l:ℕ)(β:ℕ→ℝ)(B:Staff)(U:clan):stitch P A s β B l (some U)=Yoke.pill P.par A s U B.u B.spin := by
  unfold stitch Yoke.pill; rw [spool,smul_smul,adjust]

#print axioms uptakes
#print axioms living_support
#print axioms living_cert
#print axioms stitch_tone
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
