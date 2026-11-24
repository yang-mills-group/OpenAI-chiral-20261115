import YM.SU5.May.TorqueStep
import YM.SU5.Reconstruction.Hygrometry.Constellation
import YM.SU5.Reconstruction.Intermediate.Recommended
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
local notation "v∅" n:max=> i (G.rows n)
local notation "𝒪" s:max=> Py.buoy (Y.ivory s)
variable (x:Dome (tent Y H))
variable {ε:ℝ}
namespace Torque
open Py.Rate.LocalLimit.Donor
open Py Therapies 
local notation "N(" n ")" => i (G.rows n)
local notation "C[" n "]"=> turnUp Y (i (G.rows n))
local notation "Vb" m:max T:max=> blankMenu Y m T
local notation "Ζ" m:max t:max T:max z:max=> upperSession Y m t T (blankMenu Y m T) z
local notation "Π" m:max t:max T:max z:max=> phaseInspector Y m t T 0 (temper (projectA Y m t) T Λ.δ T z)
local notation "μ" m:max t:max d:max s:max z:max a:max=> climb Y m t s d (blankMenu Y m d) z (basement Y H m s x) a
-- always high at polynomial, not at buoy for this trajectory beyond the step. But consultants keep actual law.
structure Cred (m t d:ℕ)(z:Intermediate.Room d):Prop where
  high: turnUp Y m=d
  menu: d≤Y.uv t
  carrier: phaseMoney Y m t d (blankMenu Y m d) z
  real: phaseInspector Y m t d 0 (temper (projectA Y m t) d Λ.δ d z)≠ 0
include V
lemma roll_easy (p:x∈insideAt Λ l (tent Y H) true (Acres P r) s)(e:0<ε): ∀ᶠ n in atTop, let m:= i (G.rows n); ∀ᶠ t:ℕ in atTop, (∃ (a:ℕ)(z:Intermediate.Room (s+a)),0<a ∧ Cred Y m t (s+a) z) ∧ ∀ (a:ℕ)(z:Intermediate.Room (s+a)), Cred Y m t (s+a) z → ‖ticketPrice Y H m t s P x-upperSession Y m t (s+a) (blankMenu Y m (s+a)) z P (climb Y m t s (s+a) (blankMenu Y m (s+a)) z (basement Y H m s x) a)‖ ≤ ε := by
 obtain ⟨U,W,q⟩:= formed Y H V G s P r x p; obtain ⟨b,h,u⟩:= boundedProfile Y H s P x
 filter_upwards [((V.pick.grow_i.comp G.history.growsA).tendsto_atTop).eventually (securities Y s _ (div_pos e h)),q] with n ⟨p0,a0,r0⟩ w
 let m' := i (G.rows n); dsimp only; filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (turnUp Y m'), eventually_ge_atTop (Y.voyage m').kick] with t t₁ t₂
 obtain ⟨d,hd,e'⟩: ∃ d:ℕ,C[n]=s+d ∧ 0<d:=by
    refine ⟨C[n]-s,?_,?_⟩ <;> (change s < turnUp Y (i (G.rows n)) at p0; omega)
 let F':= blankMenu Y m' (s+d)
 have hf:s+d ≤ Y.uv t:= hd ▸ t₁
 have hs:=sprung Y m' t (s+d); obtain ⟨z,tz⟩:= possible Y hf hs
 have hq: partitionZ (topGram Y m' t (s+d) (F' z) (temper (projectA Y m' t) (s+d) Λ.δ (s+d) z)) Λ.U ((Y.voyage m').CapeT (s+d))≠0:= by
    rw [← launchGram_eq,← funded_compare Y hf hs z tz s (s+d) (by omega) le_rfl]; exact (r0 t t₂ _ hf hd.le F' hs z tz).1.valid
 refine ⟨⟨d,z,e', hd,hf,tz,hq⟩,fun i' z eξ=>?_⟩
 have hx := audit_spend Y H m' t s (s+i') (Vb m' (s+i')) z P r x w eξ.menu (sprung ..) eξ.carrier i' le_rfl
 rw [sessionPrice,← hx.2.2,ticketMeasure] -- let n etc.
 have hw:= r0 t t₂ _ eξ.menu eξ.high.le _ (sprung ..) z eξ.carrier
 refine (Harbour.paid_here Y t₂ ?_ hw _ (u m').1 (u m').2).trans ((mul_le_mul_of_nonneg_left a0 ?_).trans_eq ?_)

 all_goals first|exact h.le|exact le_trans (Nat.le_add_right s i') eξ.menu|exact mul_div_cancel₀ ε h.ne' -- linter


local notation "ℐ" f:max m:max => I s (windTilt P (tent Y H) f*f).val m
local notation "𝓔" f:max => E s (windTilt P (tent Y H) f*f).val
omit V
-- permit budget test on actual explorar.Fixed m first. Need rank estimates.
noncomputable def Belt: Prop:= ∀ (s:ℕ)(x:Dome (tent Y H)),x∈insideAt Λ l (tent Y H) true (Acres P r) s→∀ ε:ℝ,0<ε→∃ᶠ n in atTop, ∃ᶠ d in atTop,∃ (a:ℕ)(z:Intermediate.Room (s+a)), Cred Y (i (G.rows n)) (k d) (s+a) z ∧ -ε ≤ (upperSession Y (i (G.rows n)) (k d) (s+a) (blankMenu Y (i (G.rows n)) (s+a)) z P (climb Y (i (G.rows n)) (k d) s (s+a) (blankMenu Y (i (G.rows n)) (s+a)) z (basement Y H (i (G.rows n)) s x) a)).re
include V
lemma solar (p:Belt Y H G P r) : Rectitude Y H V G P r:= by
 apply born Y H V G P r
 intro s' y h ε u
 -- change binder notation h; use fresh
 let z:= windTilt P K y*y
 have ht:= PhaseChoice.final_limit Y H G s' z.val ((marque ..).1 z.property)
 have hv:= V.together s' z.val ((marque ..).1 z.property)
 have ht0: Tendsto (fun n=> (ticketPrice Y H (i (G.rows n)) (k (G.columns n)) s' P y).re) atTop (𝓝 (E s' z.val).re):= Complex.continuous_re.continuousAt.tendsto.comp ht
 suffices he: -(ε/2)< (E s' z.val).re by
    exact ((ht0.eventually (Ioi_mem_nhds he)).mono fun w g=> by
      have hx: -(ε/2)<(ticketPrice Y H (i (G.rows w)) (k (G.columns w)) s' P y).re:= g
      exact le_trans (neg_le_neg (half_le_self u.le)) hx.le).frequently
 have q: 0< ε/8:=by positivity
 have hw: ∃ᶠ n in atTop, -ε/4 ≤ (I s' z.val (i (G.rows n))).re:= by
    refine ((p s' y h (ε/8) q).and_eventually (roll_easy Y H V G s' P r y h q)).mono ?_
    intro n h
    let m':=i (G.rows n); let K':= ticketPrice Y H m'
    have hl:Tendsto (fun d=> (ticketPrice Y H m' (k d) s' P y).re) atTop (𝓝 (I s' z.val m').re):= Complex.continuous_re.continuousAt.tendsto.comp (hv.inner _)
    refine le_of_tendsto_of_tendsto_of_frequently (f:=fun _=>-ε/4) (g:= fun d=>(K' (k d) s' P y).re) ?_ hl ?_
    · exact tendsto_const_nhds
    refine (h.1.and_eventually (V.pick.grow_k.tendsto_atTop.eventually h.2)).mono ?_; rintro d ⟨⟨a,b,u,v⟩,g⟩
    let T:= upperSession Y m' (k d) (s'+a) (blankMenu Y m' (s'+a)) b P (climb Y m' (k d) s' (s'+a) (blankMenu Y m' (s'+a)) b (basement Y H m' s' y) a)
    have he: -(ε/8) ≤ T.re:= v
    let x:=K' (k d) s' P y
    have hx:‖x-T‖≤ ε/8:= g.2 _ _ u
    have hp:= (Complex.abs_re_le_norm (x-T)).trans hx; rw [Complex.sub_re] at hp; change -ε/4 ≤ x.re; linarith [(abs_le.mp hp).1]
 have q: Tendsto (fun n=> (I s' z.val (i (G.rows n))).re) atTop (𝓝 (E s' z.val).re):= Complex.continuous_re.continuousAt.tendsto.comp ((hv.periods).comp G.history.growsA.tendsto_atTop)
 have hp:= ge_of_tendsto_of_frequently q hw
 linarith
#print axioms solar
end Torque
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
