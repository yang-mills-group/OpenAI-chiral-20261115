import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Facelift
/-! # Masks after selection. All Slots. Capitalize the whole law. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Vacancy
open Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel
open Buffered.Concord (Meter meter_p meter_time)
open Dial -- tune
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (C : Arena Y H Q.circuit 0 0 false)
variable (L : Finset (Face ℤ)) (S : Finset Cover) (p : restsOn L S)
local notation "TC" x:max => tintMark L (Meter x) (tent Y H)
local notation "A" => actor Y H s Q.circuit 0 0 false C
local notation "π" => (Aurora Y H V Q 0 false C).orthogonalProjectionOnto
local notation "Ω" => seat0 Y H V Q 0 false C
local notation "φ" x:max => located Y H V s Q Qt 0 false C x
variable {J : Calibration} {x : Family (tent Y H)} {a' C' : ℝ}
open Branch -- tune

-- get directly small price on ground. exact geometry. Then constrain masked F as well or instead.
variable (f : Marks (tent Y H) true)
def applique (i : ℕ) : Marks (tent Y H) true := (⟨TC i, aux_test (tint_price L S (Meter i) K p|>.widen), fun _=> tint_sing L (Meter i) K⟩ : Marks K true)*f -- tune operation
local notation "tagW" x:max => applique Y H L S p f x
local notation "B" x:max => (show Marks K false from bosonLabel K x)

lemma diff_small (h : InTest (tent Y H) true S false f.val) (q : Tower.region 0 0 ((tent Y H).ℓ) S) :
    Tendsto (fun i:ℕ=> (located Y H V s Q Qt 0 false C (B (tagW i))).val Ω) atTop
      (𝓝 ((located Y H V s Q Qt 0 false C (B f)).val Ω)):=by
  let y (i:ℕ) := B (tagW i)-B f
  have he i : InTest K true S false (y i).val:= corner_tests Y H L S p h i
  let v (i:ℕ) : Tower.Field Y H s 0 0 false := ⟨(y i).val,(purpose_ok ..).mpr ⟨⟨S,he i,by rw [area0]; exact q⟩,nofun⟩⟩
  refine Metric.tendsto_nhds.mpr fun ε e=>?_
  filter_upwards [Metric.tendsto_nhds.mp (vignette Y H V s L S p h) (ε^2) (by positivity)] with i g
  rw [dist_zero_right] at g; let x:= actor Y H s Q.circuit 0 0 false C (v i)
  have he : E s (mirror (tent Y H) 0 0 (unveil Y H L f.val i)*(unveil Y H L f.val i))= inner ℂ x x:=by unfold x; rw [stems Y H V,area0]; rfl
  rw [he,inner_self_eq_norm_sq_to_K] at g; change ‖((‖x‖:ℂ)^2)‖<_ at g; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at g
  rw [dist_eq_norm, show _- _=((located Y H V s Q Qt 0 false C (y i)).val Ω) from Eq.symm ?_]; swap
  · change (φ (_-_)).val Ω=_; rw [map_sub]; rfl
  change ‖(cap Y H V s Q Qt 0 false C (actorLabel Y H s 0 false (v i))) Ω‖ < _
  rw [cap_plant Y H V]; exact lt_of_le_of_lt ((Aurora Y H V Q 0 false C).norm_orthogonalProjectionOnto_apply_le x) (lt_of_pow_lt_pow_left₀ 2 e.le g)
lemma high_glare (h : InTest (tent Y H) true S false f.val) (q : Tower.region 0 0 ((tent Y H).ℓ) S)
    (w : ‖(located Y H V s Q Qt 0 false C (1+B f)).val Ω‖^2 ≤ 1/2048) :
    ∀ᶠ i in atTop, ‖(located Y H V s Q Qt 0 false C (1+B (tagW i))).val Ω‖^2≤1/1500:= by
  let a(x:Marks (tent Y H) true) : (Aurora Y H V Q 0 false C):=(φ (B x)).val Ω
  have he(x:Marks (tent Y H) true): (φ (1+B x)).val Ω=Ω+a x:=by rw [map_add,located_one]; rfl
  simp_rw [he]; rw [he] at w; let H' := ((diff_small Y H V s Q Qt C L S p f h q).const_add (Ω)).norm.pow 2
  exact H'.eventually (ge_mem_nhds (lt_of_le_of_lt w (by norm_num)))
lemma mixed_after (x : Marks (tent Y H) true) (h : ‖(located Y H V s Q Qt 0 false C (1+B x)).val Ω‖^2≤1/1500) : 3/4 ≤ ‖E s x.val‖ := by
  let f:= (φ (1+B x)).val Ω; have he : inner ℂ Ω f=1+E s x.val:=by rw [show inner ℂ Ω f=_ from (inspected (F:=(show Marks (tent Y H) false from 1+B x)) Y H V s Q Qt 0 false C)]; change E s (1+x.val)=_; rw [E_add Y H V s TestFamily.oneT (marksSpec true x).1,E_unit Y H V]
  have ht:= norm_inner_le_norm (𝕜:=ℂ) Ω f; rw [norm_one_vac Y H V,one_mul] at ht; change ‖f‖^2≤1/1500 at h
  have hx : (1:ℝ) ≤ ‖inner ℂ Ω f‖+‖E s x.val‖:= by
    refine (le_of_eq ?_).trans (norm_sub_le ..); rw [he, add_sub_cancel_right,norm_one]
  nlinarith only [hx,ht,h,norm_nonneg f]

section gospel
open OS.Ground
variable (P : Panel Y H V Q Qt 0 false C) (hp : Issued Y H V Q Qt 0 false C P)
local notation "R" x:max z:max => response Y H V s Q Qt 0 false C (P.character x) z
-- variant all_wines, two purchases. ensure simultaneously hits masked & full. loosen.
include hp in
lemma hero (f' : SU.Slot×Bool→ observable (tent Y H) true)
    (h' : ∀ z, ‖(φ (1+B (f' z))).val Ω‖^2 ≤ 1/1500) :
    ∃ᶠ i in ae P.μ, ∀ z, 3/4 ≤ ‖(R i (B (f' z)))‖:=by
  let f (z:SU.Slot×Bool) := B (f' z); let W(i:P.X)(z:SU.Slot×Bool):= R i (1+f z); let c (i:P.X) (z:SU.Slot×Bool):= ‖W i z‖^2
  let T i := ∑ z:SU.Slot×Bool,c i z
  letI := hp.normalized
  have h1 (z) : Integrable (fun i=> c i z) P.μ:= Continuous.integrable_of_hasCompactSupport (((hp.weak (φ (1+f z))).norm).pow _) (HasCompactSupport.of_compactSpace _)
  have hT : Integrable T P.μ:= integrable_finsetSum _ fun i _=> h1 i
  have he z:(∫ i,c i z∂P.μ) ≤ (1:ℝ)/1500:= (Panes.Shines.energyMatch («A»:= (displayAlgebra Y H V Q Qt 0 false C)) hp (φ (1+f z))).trans_le (h' z)
  have hh : ∃ᶠ i in ae P.μ,T i < (1:ℝ)/16:=by
    intro k; have hz : ∀ᵐ i ∂P.μ,T i ≥ (1:ℝ)/16:=k.mono fun i => le_of_not_gt
    have hi : (∫ i,T i∂P.μ) ≥ 1/16:=by simpa using integral_mono_ae (integrable_const _) hT hz
    have hi0:(∫ i,T i∂P.μ) ≤ (90:ℝ)/1500:=by unfold T; rw [integral_finsetSum _ (fun i _=> h1 i)]; refine (Finset.sum_le_sum (fun i _=> he i)).trans ?_; rw [Finset.sum_const,Finset.card_univ,Fintype.card_prod,SU.slots]; norm_num
    linarith
  apply hh.mono; intro i hi z
  let r := response Y H V s Q Qt 0 false C (P.character i) (f z)
  have hv0:c i z<1/16:= lt_of_le_of_lt (Finset.single_le_sum (fun x _=> show 0≤ c i x from sq_nonneg _) (Finset.mem_univ z)) hi
  have hv: ‖W i z‖≤1/4:=by unfold c at hv0; nlinarith
  have hW: W i z-r=1:=by change P.character i (φ (1+f z))-P.character i (φ (f z))=_; rw [map_add,map_add,located_one,map_one]; ring
  change _≤ ‖r‖
  linarith only [hv,norm_sub_le (W i z) r, show (1:ℝ)=‖W i z-r‖ from by rw [hW,norm_one]]

variable {q d w : ℕ} (c : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
local notation "D₀" => payout d q w
local notation "G" => grain (payout d q w)
local notation "S₀" => Sen (grain (payout d q w)) (payout d q w)
local notation "T₀" => grindset (booty (grain (payout d q w)) d q)
local notation "T₁" => grindscape (booty (grain (payout d q w)) d q) (Sen (grain (payout d q w)) (payout d q w))
local notation "V'" i:max x:max => displacement Y H V Q Qt 0 false C (P.character x) i (c i)
abbrev paints_for (q d w : ℕ) (u : ℝ) (x : P.X) (f f' : SU.Slot → observable (tent Y H) true) : Prop :=
    let o := grain (payout d q w); let z:= booty o d q; let S:=Sen o (payout d q w); let T:= grindscape z S
    ∀ (l : SU.Slot), (f' l).val=tintMark (grindset z) u (tent Y H)*(f l).val ∧ restsOn (grindset z) T ∧
      (∀ (m : Side) (v : Fields ((tent Y H).c m)) (r : Fin (q^4)), SU.group.chord (faceValue (onC _ v.1) (facet (z r))) ≤ u→ (f' l).val m v=0) ∧
      (ThresholdInteraction Y H V s Q Qt 0 C S (P.character x) (f l) l o q d ∧
        ThresholdInteraction Y H V s Q Qt 0 C T (P.character x) (f' l) l o q d) ∧
      ∀ j:Axis, ThresholdInteraction Y H V s Q Qt j (c j) S (V' j x) (f l) l o q d ∧
        ThresholdInteraction Y H V s Q Qt j (c j) T (V' j x) (f' l) l o q d

include hp
lemma actuated (R₁ Z : ℝ) (p : Papal.Korn Y H q d w R₁ Z) : ∀ᶠ s in atTop,
    ∃ (u : ℝ) (f f' : SU.Slot → observable (tent Y H) true), 0<u ∧ ∃ᶠ x in ae P.μ, paints_for Y H V s Q Qt C P c q d w u x f f' := by
  filter_upwards [covalues Y H V Q Qt C p] with s h
  choose f b using h
  have h0 := grind_rest (booty (grain D₀) d q) S₀
  let f'(i:ℕ)(l:SU.Slot) : Marks (tent Y H) true:= applique Y H T₀ T₁ h0 (f l) i
  have hT(z) : (f z).val∈ Filigree (tent Y H) (family z) (booty (grain D₀) d q) T₁:= fil_larger S₀ subset_union_left (b z).indeed.mark_mem
  have hgl z : ∀ᶠ i:ℕ in atTop, ‖(located Y H V s Q Qt 0 false C (1+B (f' i z))).val Ω‖^2 ≤ 1/1500:= by
    have hw := grind_between (booty (grain D₀) d q) S₀ (between_grain p.limit 0 _ (le_refl _)) (b z).indeed.anchors_here
    exact high_glare Y H V s Q Qt C T₀ T₁ h0 (f z) ((FilTest (hT z)).widen) (fun i x=> (hw i x).1) (b z).price
  obtain ⟨i,v⟩:= (eventually_all.mpr hgl).exists
  let u (z : SU.Slot×Bool) : observable (tent Y H) true := if z.2 = true then f z.1 else f' i z.1
  have ht z : ‖(located Y H V s Q Qt 0 false C (1+B (u z))).val Ω‖^2 ≤ 1/1500:= by unfold u; split; exact (b _).price.trans (by norm_num); exact v _
  refine ⟨Meter i,f,f' i,meter_p _,((hero Y H V s Q Qt C P hp u ht).and_eventually (full_house Y H V Q Qt 0 false C P hp c)).mono ?_⟩
  intro x ⟨k,h,H'⟩ z; have he := b z; let r:= booty (grain D₀) d q
  have hz' : FixedLink Y H V s Q Qt z (grain D₀) q d T₁ (f' i z):=freeze Y H V s Q Qt (f' i z) _ he.indeed.anchor_inj (fun i=> Finset.mem_union_left _ (he.indeed.anchors_here i)) (fil_tinted T₀ T₁ _ h0 (hT z)) ((mixed_after Y H V s Q Qt C _ (v z)).trans' (by norm_num))
  have hx : 1/4≤ ‖response Y H V s Q Qt 0 false C (P.character x) (B (f z))‖:=by
     specialize k (z,true); rw [show u (z,true)=_ from (if_pos (show (z,true).snd=true from rfl) : u (z,true)=f z)] at k; linarith
  have hx' : 1/4≤ ‖response Y H V s Q Qt 0 false C (P.character x) (B (f' i z))‖:=by
     have hh:= k (z,false); rw [show u (z,false)=f' i z from if_neg Bool.false_ne_true] at hh; linarith
  refine ⟨rfl,h0,?_,⟨threshold_interaction Y H V s Q Qt 0 C _ _ (f z) (survive Y H V s Q Qt 0 C he.indeed h hx), threshold_interaction Y H V s Q Qt 0 C _ _ (f' i z) (survive Y H V s Q Qt 0 C hz' h hx')⟩, fun k'=> ?_⟩
  · intro m v i' q'; change tintMark T₀ (Meter i) _ _ _*_=_; rw [tint_here, clay_absent T₀ _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i')) (meter_p i) q', Complex.ofReal_zero, zero_smul,zero_mul]
  exact ⟨threshold_interaction Y H V s Q Qt k' (c k') _ _ _ (survive Y H V s Q Qt k' (c k') he.indeed (H' k') (by rw [across_response]; exact hx)),threshold_interaction Y H V s Q Qt k' (c k') _ _ _ (survive Y H V s Q Qt k' (c k') hz' (H' k') (by rw [across_response]; exact hx'))⟩
end gospel
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.actuated
