import YM.SU5.May.FloeOpen
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
local notation "T" n:max => Therapies.paceFloor Y H G n
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
variable (F:Intermediate.Room R→ Corr (Λ.Ctor (Y.ir m) R))(z: Intermediate.Room R)
open Therapies
variable (G':Mark (Journey.side Y m s))(v:ℝ)
-- mixture already actual phase, NOT absolute weighting. outside signed distance isolatable
noncomputable def share (G':Mark (Journey.side Y m s)) (v:ℝ)(X:Set (Pane (Journey.side Y m s))): ℂ :=
 let u:Orbit (Journey.side Y m s)→ℂ := fun i=> letterRead (G' (i.1,(Y.voyage m).CapeT s i)) (tap Y m t s v i) - dotCurrency Y m t s G' * beamZ _ (tap Y m t s v i)
 (∫ i in Prod.fst ⁻¹' X,u i ∂city _)/phaseInspector Y m t s 0 v
local notation "hβ" x:max=> temper (projectA Y m t) s Λ.δ s x
local notation "Π" => blankMenu Y m s
local notation "Ɛ" x:max => dotCurrency Y m t s x
local notation "Bz" v:max=> tap Y m t s v
local notation "φz" v:max=> phaseInspector Y m t s 0 v
local notation "N" => (𝗠 m s)
local notation "Fμ" v:max i:max => letterRead (G' (drawn ((Y.voyage m).CapeT s) i)) (tap Y m t s v i)
local notation "εμ" v:max i:max => beamZ (𝗠 m s) (tap Y m t s v i)
local notation "Rμ" v:max i:max => (Fμ v i- (Ɛ G')*(εμ v i))
variable (X:Set (Pane (Journey.side Y m s))) (ξ:ℝ)
def Inlet (f:Mark (Journey.side Y m s)) (ξ:ℝ) (X:Set (Pane (Journey.side Y m s))): Prop:= Typical X ∧ 0<(prior SU.group (More (Journey.side Y m s))) X ∧ ∀ (i:Orbit (Journey.side Y m s)),i.1∈X → flags (Y.meter.a s).threshold i.1=∅ ∧∀ β:ℝ, beamZ _ (tap Y m t s β i)≠0 ∧ ‖Directly Y m t s β i f-dotCurrency Y m t s f‖< ξ
noncomputable def shelter (v:ℝ)(G':Mark (Journey.side Y m s))(X:Set (Pane (Journey.side Y m s)))(δ:ℝ): Prop:= ∃ ξ:ℝ,0< ξ ∧ Inlet Y m t s G' ξ X ∧ ξ*(∫ i: Orbit (Journey.side Y m s), ‖beamZ _ (tap Y m t s v i)‖ ∂city _)/‖phaseInspector Y m t s 0 v‖≤ δ -- can sharpen to absolute on part.X.
variable (f: Integrable (tap Y m t s v) (city _)) (k:MeasurableSet X)(p:Envelope G')(e:phaseInspector Y m t s 0 v≠0)
include f p e
lemma arrangedCash (hX:MeasurableSet X): markedRead G' ((Y.voyage m).CapeT s) (tap Y m t s v)/(φz v)= dotCurrency Y m t s G' + share Y m t s G' v X + share Y m t s G' v Xᶜ:=by
 have hp: Integrable (fun i:Orbit N=> Fμ v i) (city _):= mark_integrable ((Y.voyage m).ownership s).paid.bill p f
 have ht: Integrable (fun i:Orbit N=> εμ v i) (city _):= (beamL (Journey.side Y m s)).integrable_comp f
 let h:= Prod.fst (β:= Ids N) ⁻¹' X; have he := integral_add_compl (μ:=city N) (f:=fun i=>Rμ v i) (hX.preimage measurable_fst) (hp.sub (ht.const_mul _)) -- notation i maybe shadow h etc 
 suffices H: share Y m t s G' v X + share Y m t s G' v Xᶜ=(markedRead G' ((Y.voyage m).CapeT s) (tap Y m t s v)-Ɛ G' *(φz v))/(φz v) by rw [add_assoc,H, sub_div, mul_div_assoc, div_self e, mul_one]; abel
 rw [share,share,← add_div]; apply congrArg (· / φz v) -- wrong side tune
 -- maybe change_
 change (∫ i in h,Rμ v i ∂city _)+(∫ i in hᶜ,Rμ v i∂city _)=_
 rw [he,integral_sub hp (ht.const_mul _),integral_const_mul]; rfl
lemma share_paid (δ:ℝ)(q:shelter Y m t s v G' X δ): ‖share Y m t s G' v X‖≤ δ:=by
 obtain ⟨ξ,u,t',a⟩:= q; have hx:=t'.1; have hp := mark_integrable ((Y.voyage m).ownership s).paid.bill p f; have ht: Integrable (fun i:Orbit N=>εμ v i) (city _):= (beamL (Journey.side Y m s)).integrable_comp f
 rw [share, norm_div]; refine le_trans (div_le_div_of_nonneg_right ?_ (norm_nonneg _)) a
 let F : Set (Orbit N):= Prod.fst ⁻¹' X; change ‖∫ v' in F,Rμ v v' ∂city _‖ ≤ _
 refine (norm_integral_le_integral_norm ..).trans (le_trans (b:= ∫ i in F,ξ * ‖εμ v i‖ ∂city _) ?_ ?_)
 · apply setIntegral_mono_on (μ:=city N) (s:=F) (f:=fun i=> ‖Rμ v i‖) ((hp.sub (ht.const_mul _)).norm.integrableOn) ((ht.norm.const_mul _).integrableOn) (hx.2.1.measurableSet.preimage measurable_fst); intro i h; obtain ⟨c,c₁⟩:= (t'.2.2 i h).2 v; rw [←burnerAt Y m t s G' i v c]; change ‖Directly Y m t s v i G' * (εμ v i) - Ɛ G' * (εμ v i)‖≤ξ * ‖εμ v i‖; rw [←_root_.sub_mul, norm_mul]; exact mul_le_mul_of_nonneg_right c₁.le (norm_nonneg _)
 rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ u.le; exact setIntegral_le_integral ht.norm (Eventually.of_forall fun _=> norm_nonneg _)
lemma locateCost (h:∀ δ:ℝ,0<δ→ Sufficient Y m t s δ G' (dotCurrency Y m t s G')) (δ:ℝ)(tδ:0<δ): ∃ X:Set (Pane (𝗠 m s)), shelter Y m t s v G' X δ:=by
 let C:=(∫ i:Orbit N,‖εμ v i‖ ∂city _)/‖φz v‖; let y:= 1+C; have u:0< y:= by have hg:0≤C:=div_nonneg (integral_nonneg (fun _=> norm_nonneg _)) (norm_nonneg _); linarith only [show y=1+C from rfl,hg]
 let ξ:=δ/y; obtain ⟨X,a,b,g⟩:=h ξ (div_pos tδ u); have hp:= div_mul_cancel₀ δ u.ne'; refine ⟨X, ξ,div_pos tδ u,⟨a,b,g⟩,?_⟩; rw [mul_div_assoc]; exact le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (a:=C) (b:=1) zero_le_one) (div_pos tδ u).le) (le_of_eq hp) -- tune names
omit e f p
local notation "UX" X:max=> Prod.fst ⁻¹' X
lemma office_chance (h:Inlet Y m t s G' ξ X) : 0< (city (Journey.side Y m s)) (Prod.fst ⁻¹' X) := by
 rw [city]; rw [show Prod.fst ⁻¹' X=X ×ˢ (Set.univ: Set (Ids N)) from (by ext; simp),Measure.prod_prod,measure_univ,mul_one]; exact h.2.1
include f in
/-- YES even at the real data. ∫ ‖beam‖ has patch funding. Can't use as shift of actual phase. -/
lemma hearts (h:Inlet Y m t s G' ξ X): 0<∫ i in Prod.fst ⁻¹' X, ‖beamZ _ (tap Y m t s v i)‖∂city _:=by
 let W:Set (Orbit N):= Prod.fst ⁻¹' X; let B(i:Orbit N):=‖εμ v i‖
 apply (integral_pos_iff_support_of_nonneg (f:=B) (μ:=(city N).restrict W) (fun i =>norm_nonneg _) (((beamL N).integrable_comp f).norm.integrableOn (s:=W))).mpr
 have hp:0<((city N).restrict W) W:=by rw [Measure.restrict_apply_self]; exact office_chance Y m t s G' X ξ h
 exact lt_of_lt_of_le hp (measure_mono (fun i g=> (norm_pos_iff.mpr ((h.2.2 _ g).2 v).1).ne')) -- compile
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.locateCost
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.share_paid
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.hearts
