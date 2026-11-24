import YM.CF.Phase.Sound

/-!
# Volume-independent admissible chiral determinant line

One section for the full colored band with all copies, simultaneously at all
bundles represented by this periodic grid, continuous and equivariant. This is
a nonperturbative statement; not just the Lie algebra anomaly test. Not
itself a continuum-anomaly comparison or a path-integral existence theorem.
Uses an auxiliary unit field but needs no new fermion species.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def unscaled (m B : Side) (c : Part m B) (U : Skin m B) (x : Cue m) : Wave (Mind m B) := Complex.exp (-accord m B c U x) • filled (lens m B c U) (pair m B U x)
def sized {n : Type*} [Fintype n] (v : Ket n) := ((‖v‖:ℂ)⁻¹) • v
def sound (m B : Side) (c : Part m B) (U : Skin m B) := sized (unscaled m B c U (cue_from U).choose)
section
variable (c : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B} (g : Guard U e) {x y : Cue m} (h : ZeroF m B U x) (k : ZeroF m B U y)
include b g h
lemma chain_unit : IsUnit (stage (lens m B c U) (pair m B U x)) := (bow_ok c b g (show Verified _ _ margin _ _ {0} from h) (stick_in _ (Finset.mem_singleton_self 0))).2
lemma chain_full : filled (lens m B c U) (pair m B U x)≠0 := bow_full c b g (show Verified _ _ margin _ _ {0} from h) (stick_in _ (Finset.mem_singleton_self 0))
lemma chainP : unscaled m B c U x≠0 := smul_ne_zero (Complex.exp_ne_zero _) (chain_full c b g h)
include k
lemma chain_w : unscaled m B c U x=unscaled m B c U y := by
  unfold unscaled; rw [←log_fill c b g x y h k,smul_smul, ←Complex.exp_add,←transpose_mean c b U g x y h k, show -(accord m B c U x+_) + logs m B c U x y= -accord m B c U x by abel] -- tune
omit k
lemma sonic : sound m B c U=sized (unscaled m B c U x) := by
  rw [sound,chain_w c b g (cue_from U).choose_spec h]
omit h
/-- Gauge action by the values at the actual fermion sites. -/
lemma band_g (t : Site (Domain m B)→E) : sound m B c (gauge t U)=turnW (t ∘ node) (sound m B c U) := by
  obtain ⟨x,hx⟩ := cue_from U
  rw [sonic c b (g.cov t) ((twist_0 U x t).mpr hx), sonic c b g hx, turnW]
  rw [unscaled, unscaled, lens_g c b g, pair_g,filled_twist,accord_g c b t x g hx]
  rw [sized,sized, map_smul,map_smul, norm_smul, norm_smul, act_unit_norm]
lemma unity : Sea (lens m B c U) (sound m B c U) := by
  obtain ⟨x,H⟩ := cue_from U
  have he := chainP c b g H
  rw [sonic c b g H]; constructor
  · unfold sized unscaled; rw [map_smul,map_smul]; congr 2 -- tune
    unfold filled; rw [←act_mul,show lineOp (lens m B c U)*_=_ from (line_proj (lensP c b g)).isIdempotentElem]
  unfold sized; rw [norm_smul]; simp [he]
omit g
lemma pair_cont : ContinuousOn (fun a:Skin m B×Cue m => pair m B a.1 a.2) (payer m B e) := by
  let f := fun t:Skin m B×Cue m=>(t.1,slot m t.2, stick (0:Row)); intro t ht
  apply ContinuousAt.continuousWithinAt; let F := fun u:Skin m B × ArrayF m × Sq=>bow m B u.1 u.2.1 u.2.2
  change ContinuousAt (F ∘ f) _
  have he : ContinuousAt F (f t) := bow_at b ht.1 (show Verified _ _ margin _ _ {0} from ht.2) (stick_in 0 (Finset.mem_singleton_self 0))
  have H : Continuous f := continuous_fst.prodMk (((slot_cont m).comp continuous_snd).prodMk continuous_const)
  exact he.comp H.continuousAt
lemma unscaled_cont : ContinuousOn (fun u:Skin m B×Cue m=>unscaled m B c u.1 u.2) (payer m B e) := by
  have he := accord_cont c b
  have H := pair_cont (m:=m) b
  have ht : ContinuousOn (fun u:Skin m B×Cue m=>lens m B c u.1) (payer m B e) := (lens_cont c b).comp continuous_fst.continuousOn (fun _ g=>g.1)
  let F := fun t:Skin m B×Cue m=> (lens m B c t.1,pair m B t.1 t.2)
  let K := fun t:Skin m B×Cue m=>Complex.exp (-accord m B c t.1 t.2)
  let T := fun t : Op (Mind m B) × Op (Mind m B) => filled t.1 t.2
  have hK : ContinuousOn K _ := Complex.continuous_exp.comp_continuousOn he.neg
  have hT : Continuous T := filled_cont
  change ContinuousOn (K • (T ∘ F)) _; exact hK.smul (hT.comp_continuousOn (show ContinuousOn F _ from ht.prodMk H))
lemma melody : ContinuousOn (sound m B c) {U | Guard U e} := by
  let Y := {U : Skin m B| Guard U e}; intro U h
  obtain ⟨x,H⟩ := cue_from U; have hg : ZeroF m B U x := H
  let f := fun t:Skin m B=>(t,x)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  have he : payer m B e∈ Filter.map f (nhdsWithin U Y) := by
    -- eventual
    rw [Filter.mem_map]; filter_upwards [self_mem_nhdsWithin, show {t|f t∈{t:Skin m B × Cue m|ZeroF m B t.1 t.2}}∈ nhdsWithin U Y from nhdsWithin_le_nhds ((IsOpen.mem_nhds ((open0 m B).preimage hf)) hg)] with t ht hy; exact ⟨ht,hy⟩
  let L := fun t:Skin m B=>unscaled m B c t x
  have hL : ContinuousWithinAt L Y U := by
    let K := fun t:Skin m B × Cue m=>unscaled m B c t.1 t.2
    change Filter.Tendsto (K ∘ f) _ (𝓝 (K (f U)))
    have Hf : ContinuousWithinAt K (payer _ _ e) (f U) := unscaled_cont c b (f U) (show _ from ⟨h,H⟩)
    exact Filter.Tendsto.comp Hf (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt.continuousWithinAt,Filter.mem_map.mp he⟩)
  have hp := chainP c b (show Guard U e from h) H
  have hz : ContinuousWithinAt (fun t => sized (L t)) Y U := by
    let J := fun t : Skin m B => (↑‖L t‖:ℂ)
    have hJ : ContinuousWithinAt J Y U := Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hL.norm
    have hk : J U≠0 := by simpa [J,L] using hp
    change ContinuousWithinAt (J⁻¹ • L) Y U; exact (hJ.inv₀ hk).smul hL
  exact hz.congr_of_eventuallyEq ((show ∀ᶠ t in nhdsWithin U Y, f t ∈ payer m B e from Filter.mem_map.mp he).mono (fun t h => sonic c b h.1 h.2)) (sonic c b h H)
end
/-- All sufficiently large block sizes. -/
theorem orbit : ∃ n:ℕ, ∀ B : Side, n≤B.val → ∃ e>0, ∀ (m : Side) (c : Part m B),
    ContinuousOn (sound m B c) {U | Guard U e} ∧ ∀ U : Skin m B, Guard U e →
    IsStarProjection (lens m B c U) ∧ Sea (lens m B c U) (sound m B c U) ∧
      ∀ t, sound m B c (gauge t U)=turnW (t ∘ node) (sound m B c U) := by
  obtain ⟨n,H⟩ := all_room; refine ⟨n,fun B h=>?_⟩; obtain ⟨e,p,k⟩ := H B h; have he := k e p.le le_rfl
  exact ⟨e,p,fun m c=>⟨melody c he, fun U g=> ⟨lensP c he g,unity c he g,band_g c he g⟩⟩⟩
end YM.CF.Phase
