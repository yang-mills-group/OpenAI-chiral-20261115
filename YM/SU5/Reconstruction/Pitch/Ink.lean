import YM.SU5.Reconstruction.Pitch.Distinct
import YM.SU5.Reconstruction.Pitch.SumRule
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i qc : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i qc I E)
  (G : GroundExtension (i := i) (k := qc) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

variable (a:Axis) (c : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
local notation "τ"=> marks (loomD Λ)
local notation "Δ"=> Atlas Λ
local notation "A"=> Warden Y H V G a c
local notation "H₀" x:max=> indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S₀" x:max=> ride Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "X₀" x:max=> OSvector Y H V G j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "I₀"=> flank j 0
local notation "F"=> Domain Y H G false (flank j 0)
local notation "V₀" x:max=> osValue Y H V G a (c a) x
local notation "W" p:max x:max=> leader Y H V G a c p x
variable (p:Atlas Λ) (x y: Warden Y H V G a c) (k:0≤ p j) (h:leader Y H V G a c p x=y)
local notation "px" p:max=> pitches Λ j p
local notation "κ" p:max=> constellation p K
open ConePrice SelectionAnalysis
local notation "Pf" p:max k:max x:max=> promenadeFront Y H G j p x k
local notation "T"=> transportT Y H V G a c j p x y k h
open OS.Semigroup
-- In-product closures comparing at SAME clock, but opposite center observers. Actual discrimination using Joint origin (commuting filtered pricing in CStar reps). Key: produce any PAIR of VACUUM amplitudes via the dense precursor data at all future τ stamps, w/out Full.
open SelectionAnalysis
variable (r:ℝ)(u:0≤r)
local notation "FF"=> Domain Y H G true (flank j r)
local notation "Vf" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "ρ" x:max=> procession Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S"=>driveAlgebra Y H V G.history G.clipped j false (c j)
local notation "B"=>traveller Y H V G.history G.clipped j false (c j)
local notation "b"=> (SelectionAnalysis.concord (traveller Y H V G.history G.clipped j false (c j)))
local notation "Hp"=> ((H₀ x).space × (H₀ y).space)
local notation "Wf" x:max=> joint (B) (ρ x)
local notation "Jp" x:max=>(Wf x).starProjection
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
variable (v: weft Λ)(v₀:0≤v)
variable (Vx : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)))
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
local notation "uY" f:max=> nearer Y H G j r u f
local notation "θ'"=> flipMark j K
-- footprint costs explicitly on REGISTERED CP1 weighted true-motion gauge-carrier.
local notation "N'"=> Domain Y H G false Set.univ
noncomputable def prepareTurn (v:weft Λ)(f: F)(p:0≤v) : Domain Y H G false (flank j 0):= ⟨trek K j v f.val, forward_bar Y H G v j 0 0 (by rw [zero_add]; exact p) f.val f.property⟩
def Ink (r δ:ℝ) (v:weft Λ):Prop:= ∀ f: Sky (tent Y H),f∈D true (flank j r)→ ∀ (u':flipMark j K f*trek K j v f∈ Domain Y H G false univ)(hc:flipMark j K f * f ∈ D false Set.univ),
    0≤ (osValue Y H V G a (c a) x ⟨flipMark j K f*trek K j v f,u'⟩).re+ δ * (osValue Y H V G a (c a) x ⟨flipMark j K f*f,hc⟩).re
include u v₀
-- always funded so can ask. support certificate when r or ($r+p$) positive ensures legs disjoint.
lemma inquire (f: FF): flipMark j K f.val*trek K j v f.val ∈ D true Set.univ ∧ flipMark j K f.val*f.val ∈D true Set.univ :=by
 let t:F:= nearer Y H G j r u f; have ht:f.val∈ D true I₀:= domain_mono Y H G (TimeMesh.flank_mono j u) f.property
 exact ⟨paired_forever Y H G j _ _ ht (forward_bar Y H G v j 0 0 (by rw [zero_add]; exact v₀) _ ht),paired_forever Y H G j _ _ ht ht⟩
lemma chargeT (δ:ℝ): Ink Y H V G a c j x r δ v ↔ ∀ f:FF, let t:= (uY f); 0 ≤ (inner ℂ ((X₀ x) t) ((X₀ x) (prepareTurn Y H G j v t v₀))).re+ δ * ‖(X₀ x) t‖^2 := by
 let I'(f:FF): F:= prepareTurn Y H G j v (nearer Y H G j r u f) v₀
 have he(f:FF) (δ:ℝ) (u':flipMark j K f.val*trek K j v f.val ∈N')(p: flipMark j K f.val*f.val∈N'):
    (osValue Y H V G a (c a) x ⟨flipMark j K f.val*trek K j v f.val,u'⟩).re+δ*(osValue Y H V G a (c a) x ⟨flipMark j K f.val*f.val,p⟩).re=
     (inner ℂ ((X₀ x) (uY f)) ((X₀ x) (I' f))).re+ δ*‖(X₀ x) (uY f)‖^2:=by
     rw [← inner_self_eq_norm_sq (𝕜:=ℂ),registered_pair,registered_pair,os_across]
     rfl
 constructor
 · intro p f; obtain ⟨q,w⟩:=inquire Y H G j r u v v₀ f; let hp:= domain_loose Y H G _ q; let ht:=domain_loose Y H G _ w
   exact (p f.val f.property hp ht).trans_eq (he f δ hp ht) -- dep type
 intro p f x v g; exact (he ⟨f,x⟩ δ v g).symm ▸ p ⟨f,x⟩
local notation "L'" v:max x:max=> leader Y H V G a c (eject j v) x
local notation "Ts" v:max v0:max x:max y:max p:max=> heatT Y H V G a c j x y v v0 p
local notation "ℜ" v:max=> Real.toNNReal (v:ℝ)
omit u in
lemma chargeT_native (p: L' v x=y) (f:F): (X₀ x) (prepareTurn Y H G j v f v₀) = (Ts v v₀ x y p) ((S₀ y).E (Real.toNNReal (v:ℝ)) ((X₀ y) f)):=by
 let q:= eject j v; have g:0≤ q j:= by unfold q; rwa [eject_at];
 have h:= native_taste Y H V G a c j q x y g p f; rw [show pitches Λ j q= ℜ v from (by unfold pitches q; rw [eject_at])] at h; exact Eq.symm (h.trans (congrArg (X₀ x) (Subtype.ext (cover_solo ..))))
include Vx
lemma recouples (δ:ℝ)(p:Ink Y H V G a c j x r δ v): L' v x=x:=by
 let y:= leader Y H V G a c (eject j v) x; let T₀:= Ts v v₀ x y rfl
 change y=x; by_contra! vY
 have e:0≤ eject j v j:= by rwa [eject_at];
 have Vy:= victory_transfer Y H V G a c j (eject j v) x y e rfl Vx
 let U:= { g : (H₀ x).space × (H₀ y).space | 0 ≤ (inner ℂ g.1 (T₀ ((S₀ y).E (ℜ v) g.2))).re+δ*‖g.1‖^2};
 have h : (dressing Y H V G a c j x y r u:Set ((H₀ x).space×(H₀ y).space)) ⊆ U := by
    refine closure_minimal ?_ (isClosed_le continuous_const (Continuous.add (Complex.continuous_re.comp (continuous_fst.inner (((T₀).continuous.comp ((S₀ y).E _).continuous).comp continuous_snd))) (continuous_const.mul (continuous_fst.norm.pow _))))
    rintro z ⟨f,rfl⟩
    change 0 ≤ (inner ℂ _ ((Ts v v₀ x y rfl) ((S₀ y).E (ℜ v) ((X₀ y) (uY f))))).re+ _;
    rw [←chargeT_native]; exact (chargeT Y H V G a c j x r u v v₀ δ).1 p f
 let δ':ℝ:= -(δ+1);
 have hp:(S₀ y).E (ℜ v) (Ω y)=Ω y:= (lamp_fixed ..|>.1 (resides_real Y H V G.history G.clipped j false (c j) _).1) _ -- tune
 have ht:= h (separate_already Y H V G a c j x y r u Vx Vy (Ne.symm vY) 1 (δ':ℂ));
 change 0≤ (inner ℂ ((1:ℂ) • Ω x) (T₀ ((S₀ y).E (ℜ v) ((δ':ℂ) • (Ω y))))).re+δ*‖(1:ℂ) • (Ω x)‖^2 at ht
 rw [one_smul,map_smul,hp,map_smul,show T₀ (Ω y)=Ω x from carry_vac Y H V G a c j _ x y e rfl, inner_smul_right,inner_self_eq_norm_sq_to_K,beam_pure] at ht
 change 0 ≤ Complex.re ((δ':ℂ)* ((1:ℂ)^2))+_ at ht
 simp only [one_pow,mul_one,Complex.ofReal_re] at ht; unfold δ' at ht; linarith

-- numeric sector estimate with all singlet data. horizon any r.
omit Vx
omit v₀ in
lemma picture_dense : DenseRange (fun f:Domain Y H G true (flank j r)=> (X₀ x) (nearer Y H G j r u f)):=by
 apply (TimeMesh.dense_flanks Y H V G j (c j) _ r).mono
 rintro _ ⟨v,h,w,rfl⟩; exact ⟨⟨v,h⟩,rfl⟩
lemma ink_operator (δ:ℝ) (e:L' v x=x) : Ink Y H V G a c j x r δ v ↔ ∀ f:H₀ x, 0 ≤ (inner ℂ f ((Ts v v₀ x x e) ((S₀ x).E (ℜ v) f))).re+δ*‖f‖^2 :=by
 rw [chargeT Y H V G a c j x r u v v₀]; simp_rw [chargeT_native Y H V G a c j x x v v₀ e]; constructor
 · intro p1 f
   refine closure_minimal (t:={g:H₀ x|0≤ (inner ℂ g ((Ts v v₀ x x e) ((S₀ x).E (ℜ v) g))).re+δ*‖g‖^2}) ?_ (isClosed_le continuous_const (Continuous.add (Complex.continuous_re.comp (continuous_id.inner ((Ts v v₀ x x e).continuous.comp ((S₀ x).E (ℜ v)).continuous))) (continuous_const.mul (continuous_id.norm.pow _)))) (picture_dense Y H V G a c j x r u f)
   rintro _ ⟨v,rfl⟩; exact p1 v
 exact fun u f=> u _
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
