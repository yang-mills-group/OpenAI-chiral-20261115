import YM.SU5.Reconstruction.Intermediate.Passage
/-! # Endeavour with a specific survey. Keep time doors CP24. Uniform bookkeeping on those solvers for this query. -/
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
variable (ht:T ≤ Y.uv t) (pf: Harbour.campus Y m t T F)(tz:Harbour.phaseMoney Y m t T F z)
local notation "pβ" i:max => temper (projectA Y m t) T Λ.δ i z
local notation "scan" => climb Y m t s T F z
structure Stops (U V': Finset Cover) : Prop where
 zone (d:ℕ): Fits Y m (s+d) P r (Acres P r) (volumeAround Λ l d U) ∧ Fits Y m (s+d) P r (P.s.act '' Acres P r) (volumeAround Λ l d V') ∧ PhaseChoice.FullDistances (volumeAround Λ l d V'∪volumeAround Λ l d U) (Journey.side Y m (s+d)) ∧ Detached Λ l (volumeAround Λ l d V') (volumeAround Λ l d U)
include ht pf tz
variable (q:Stops Y m s P r U V'){g:Mark (Journey.side Y m s)} (p:AtSupport false (Satin.region U (Journey.side Y m s)) g) (p':AtSupport false (Satin.region V' (Journey.side Y m s)) (P.bill g))
include q p p'
lemma still_bought (d:ℕ)(i:s+d ≤ T): CanInspect Y m (s+d) P r (Bu d) (Bv d) (scan g d):=
 let h:=q.zone d; let hz:= ascent Y m t s T F z P ht pf tz p p' d i; ⟨hz.1,hz.2.1,h.1,h.2.1,h.2.2.1,h.2.2.2⟩
lemma reading (d:ℕ)(i:s+d ≤ T):
    fe s (P.bill g*g)= fe (s+d) (P.bill (scan g d)*scan g d):= by
 induction d with
 | zero=>rfl
 | succ d ih=>
   have hv := still_bought Y m t s T F z P r ht pf tz q p p' d (by omega)
   refine (ih (by omega)).trans ?_
   let Z:= scan g d
   let g₁:= assembleNext Y m t (s+d) T F z Z
   change fe (s+d) (P.bill Z*Z) = fe (s+d+1) (P.bill (assembleNext _ _ _ _ _ _ _ Z) * g₁)
   have ha:s+d<T:=by omega
   rw [budget_of Y m t (s+d) T F z ht pf tz ha ((hv.siteT.mono (Finset.subset_univ _)).mulM (hv.siteF.mono (Finset.subset_univ _))), step_tensor Y m t (s+d) T F z P r ht pf tz ha hv]
omit ht pf tz q p p'

noncomputable def upperSession (x:Mark (Journey.side Y m T)) := let X':= topGram Y m t T (F z) (temper (projectA Y m t) T Λ.δ T z);
    markedRead (P.bill x * x) ((Y.voyage m).CapeT T) (denZ X' Λ.U ((Y.voyage m).CapeT T)) / partitionZ X' Λ.U ((Y.voyage m).CapeT T)
lemma sessionPrice (x:Mark (Journey.side Y m T)): upperSession Y m t T F z P x= fe T (P.bill x*x):= by unfold upperSession Harbour.consultancy; rw [Harbour.launchGram_eq]
noncomputable def ticketPrice (x:Dome (tent Y H)):= sharp Y H s m t ((P.cuspF (tent Y H) x.val)*x.val)
lemma ticketMeasure(x:Dome (tent Y H)): ticketPrice Y H m t s P x= let X':= ((Y.voyage m).X (Y.uv t)).gram s;
  let f:= Tapestry.exhibit Y H s m x.val; markedRead (P.bill f*f) ((Y.voyage m).CapeT s) (denZ X' Λ.U ((Y.voyage m).CapeT s)) / partitionZ X' Λ.U ((Y.voyage m).CapeT s):= by
  rw [ticketPrice,actualRead,actual_product, exhibits]
local notation "i'" n:max=> i (G.rows n)
local notation "k'" n:max=> k (G.columns n)
local notation "𝕀" => i ∘ G.rows
local notation "ℕ𝕌" => k ∘ G.columns
lemma pay_height : ∀ᶠ n:ℕ in atTop, (Y.voyage (i' n)).kick ≤ k (G.columns n) := (G.history.finance 0).mono fun i t=> t.depth -- inference.B.Err
noncomputable abbrev basement (f:Dome (tent Y H)) : Mark (Journey.side Y m s):= Tapestry.exhibit Y H s m f.val
noncomputable abbrev measured (f:Dome (tent Y H)):Mark (Journey.side Y m s):= P.bill (basement Y H m s f)*basement Y H m s f
private lemma displaySense(x:Dome (tent Y H)): Tapestry.exhibit Y H s m (windTilt P K x*x).val= measured Y H m s P x:=by
 change exhibit _ _ _ _ (P.cuspF (tent Y H) x.val * x.val)=_; rw [actual_product, exhibits]
lemma boundedProfile (x:Dome (tent Y H)): ∃ b:ℝ,0<b ∧ ∀ m:ℕ, Envelope (measured Y H m s P x) ∧ ∀ y,‖measured Y H m s P x y‖≤ b:= by
 let U':Dome (tent Y H):= windTilt P K x*x; obtain ⟨q,t⟩ := ((marque ..).1 U'.property).paid; obtain ⟨b,d⟩:= Journey.valuation _ _ t
 refine ⟨max b 1, zero_lt_one.trans_le (le_max_right ..),fun m=>?_⟩; rw [← displaySense]; refine ⟨(exhibited Y H s m q t).env, fun y=> le_trans ?_ (le_max_left b 1)⟩; exact ((displayPositive (terrain Y H (Y.ir m) s) b _).1 (d (momentm Y m s))) y

structure Accurate (x:Dome (tent Y H))(ε:ℝ) : Prop where
 warm : Valued Y m t T F z s
 qualify : pB T≠0
 norm_current : ‖ticketPrice Y H m t s P x- consultancy Y (i:=m) (k:=t) (s:=T) (F:=F) z s (measured Y H m s P x)‖ ≤ ε
open Py.Rate.LocalLimit.Donor -- may beambig
include V
open Py
lemma accessible (x:Dome (tent Y H))(ε:ℝ)(h:0<ε): ∀ᶠ n in atTop, s< Py.buoy (Y.ivory (k (G.columns n))) ∧ ∀ d:ℕ, d≤ Y.uv (k (G.columns n)) → Py.buoy (Y.ivory (k' n)) ≤ d →
   ∀ F:Intermediate.Room d→ Corr (Λ.Ctor (Y.ir (i' n)) d), Harbour.campus Y (i' n) (k' n) d F → ∀ z:Intermediate.Room d, Harbour.phaseMoney Y (i' n) (k' n) d F z→ Accurate Y H (i' n) (k' n) s d F z P x ε := by
 obtain ⟨b,hB,q⟩:= boundedProfile Y H s P x
 have hp:Tendsto (k ∘ G.columns) atTop atTop:= (V.pick.grow_k.comp G.history.growsB).tendsto_atTop
 have hv:= (Y.UV.tendsto_atTop.comp hp).eventually (shrinks (T:=Y.meter) (τ:=Y.τ) (C:=Λ.C) s Λ.b (div_pos h hB))
 filter_upwards [pay_height Y H G,hp.eventually (Harbour.alwaysInstalled Y s), hv] with n v z' u
 obtain ⟨a,c⟩:= (z'); refine ⟨a,?_⟩; intro d e he Gq j zPtr kPtr
 let t'' := i' n; let k'' := k' n; have w:Valued Y t'' k'' d Gq zPtr s:= c _ v d e he _ j _ kPtr; refine ⟨w,?_,?_⟩
 · rw [←funded_compare Y e j zPtr kPtr s d (a.le.trans he) le_rfl]; exact w.1.valid
 rw [ticketMeasure]; refine (Harbour.wholeStamp Y v (le_trans a.le (le_trans he e)) w (measured Y H t'' s P x) (q t'').1 (q t'').2).trans ?_
 exact (mul_le_mul_of_nonneg_left (u _ ((Y.voyage t'').domain k'' v)) hB.le).trans_eq (mul_div_cancel₀ _ hB.ne') -- check
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
