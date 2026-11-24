import YM.SU5.Reconstruction.Pitch.Taste
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
private lemma commutingX {t:marks (dainty Λ)} (s:Axis)(f:Sky J): constellation p J (stride J s t f)=stride J s t (constellation p J f) :=by
 rw [← advance_even, ← cover_solo, cover_plus,←cover_solo _ s (accept Λ t), cover_plus, add_comm p]
include k h
lemma arcs_move (v: ℝ≥0) (f:H₀ y) : T ((S₀ y).E v f)=(S₀ x).E v (T f):=by
 let S:= S₀ y; let S':= S₀ x
 have comm {W':Hilbert} (Z:OS.Semigroup W' j) (x y:ℝ≥0) (v:W') : Z.E x (Z.E y v)=Z.E y (Z.E x v):=by rw [←ContinuousLinearMap.comp_apply,←ContinuousLinearMap.comp_apply,←Z.time, ←Z.time, add_comm x]
 -- Apply on E p dense. Continuous purchase on ψ endpoints enough.
 have he (t:marks (dainty Λ))(t₀:0≤t)(f: F): let a':ℝ≥0:=Real.toNNReal (t:ℝ); T (S.E a' (S.E (px p) ((X₀ y) f)))=S'.E a' (T (S.E (px p) ((X₀ y) f))):=by
    intro a'; rw [comm S a' (px p), native_taste Y H V G a c j p x y k h f]; dsimp only [a',S',S]; rw [time_even Y H V G a c y j t t₀,time_even Y H V G a c x j t t₀, native_taste]; exact congrArg (X₀ x) (Subtype.ext (commutingX p j f.val))
 apply congrFun (a:=f) ((escapes Y H V G a c j p y).equalizer
    ((T).continuous.comp (S.E v).continuous)
    ((S'.E v).continuous.comp (T).continuous) _)
 funext f
 have hp: (fun v:ℝ≥0=> T (S.E v (S.E (px p) ((X₀ y) f))))=(fun v:ℝ≥0=> S'.E v (T (S.E (px p) ((X₀ y) f)))):=by
    apply (fills (dainty Λ)).denseRange_val.equalizer ((T).continuous.comp (S.continuousE _)) (S'.continuousE _); funext v; obtain ⟨a,b,e⟩:= MeshClock.split _ v.property; dsimp only [Function.comp_apply]; let t:perch Λ:= notch (dainty Λ) a b
    have ht : (t:ℝ)= (v.val:ℝ) := (natural_time _ a b).trans (congrArg (fun x:ℝ≥0=>(x:ℝ)) e)
    have h := he t (show 0≤ (t:ℝ) from ht.symm ▸ v.val.property) f
    dsimp only at h; rw [ht, Real.toNNReal_coe] at h; exact h
 exact congrFun hp v
local notation "U" x:max u:max v:max=> ((outfit Y H V G a c x j).crew u).play v
lemma matches_even (u:Trans j)(v:marks (dainty Λ))(f:H₀ y) : T ((U y u v) f)= (U x u v) (T f):=by
 apply congrFun (a:=f) ((escapes Y H V G a c j p y).equalizer
    ((T).continuous.comp (U y u v).continuous) ((U x u v).continuous.comp (T).continuous) _)
 funext w; dsimp only [Function.comp_apply]; rw [←ContinuousLinearMap.comp_apply, comm_heat Y H V G a c y,ContinuousLinearMap.comp_apply,owns_play, native_taste,native_taste,owns_play]; exact congrArg (X₀ x) (Subtype.ext (commutingX p u.val w.val))
local notation "Ω" x:max=> doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
lemma carry_vac : transportT Y H V G a c j p x y k h (Ω y)=Ω x:=by
 have he:(S₀ y).E (px p) (Ω y)= Ω y:=(lamp_fixed (S₀ y) _).1 (resides_real Y H V G.history G.clipped j false (c j) _).1 (px p)
 let f : F:=⟨1,domain_one ..⟩; let p:= native_taste Y H V G a c j p x y k h f
 rw [show (X₀ y) f=Ω y from vacuum_ticket .., he] at p; refine p.trans (Eq.trans (congrArg (X₀ x) ?_) (vacuum_ticket Y H V G j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)))); exact Subtype.ext (cover_id ..)
variable (q1: Atlas Λ) (k':0≤ q1 j) (z:Warden Y H V G a c) (h₁:leader Y H V G a c q1 y=z)
omit h
include k'
lemma pitches_sum : px (p+q1) = pitches Λ j p + pitches Λ j q1:= by
 apply NNReal.coe_injective; have h:0≤ (p+q1) j:= add_nonneg k k'; rw [NNReal.coe_add,pitches,pitches,pitches,Real.coe_toNNReal _ k,Real.coe_toNNReal _ k',Real.coe_toNNReal _ h]; rfl
include h h₁
-- actual orientation of the Frame leg: (p then q) on character, hence transportT on y in χ, and on z in y, equals transportT on z in χ. Does not assume rotations; spin labels still live in the Tickets.
lemma sum_rule : (transportT Y H V G a c j q1 y z k' h₁).trans (T)=
     transportT Y H V G a c j (p+q1) x z (add_nonneg k k') (by rw [←leading_plus,h,h₁]):=by
 apply DFunLike.coe_injective; apply (escapes Y H V G a c j (p+q1) z).equalizer (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _)
 funext f; let Z₁:= transportT Y H V G a c j q1 y z k' h₁
 dsimp only [Function.comp_apply,LinearIsometryEquiv.trans_apply]
 rw [native_taste Y H V G a c j (p+q1), pitches_sum j p k q1 k',(S₀ z).time, ContinuousLinearMap.comp_apply, arcs_move, native_taste,native_taste]
 exact congrArg (X₀ x) (Subtype.ext (cover_plus ..))

omit k h k' h₁
lemma transport_origin (x:A) : transportT Y H V G a c j 0 x x (le_refl _) (leading_zero ..)= LinearIsometryEquiv.refl ℂ (H₀ x) :=by
 apply DFunLike.coe_injective; apply (attains_full_axis Y H V G a j c x).equalizer (LinearIsometryEquiv.continuous _) continuous_id
 funext f; have h:= native_taste Y H V G a c j 0 x x (le_refl _) (leading_zero ..) f; rw [show pitches Λ j 0=0 from Real.toNNReal_zero, OS.Semigroup.eZero] at h; exact h.trans (congrArg (X₀ x) (Subtype.ext (constell_zero ..)))
variable (v: marks (dainty Λ))(p0:0≤v)
include p0
lemma even_native : leader Y H V G a c (eject j (accept Λ v)) x=x ∧ ∀ T' : (W (eject j (accept Λ v)) x)=x,
    transportT Y H V G a c j (eject j (accept Λ v)) x x (by rw [eject_at]; exact p0) T'=LinearIsometryEquiv.refl ℂ (H₀ x):=by
 refine ⟨by rw [star_leading,no_even], fun T'=>?_⟩
 let q:= eject j (accept Λ v); let p:0≤q j:=by unfold q; rw [eject_at]; exact p0
 apply DFunLike.coe_injective; apply (escapes Y H V G a c j q x).equalizer (LinearIsometryEquiv.continuous _) continuous_id
 funext f; dsimp only [Function.comp_apply]; rw [native_taste]
 change (X₀ x) _=(S₀ x).E (px q) ((X₀ x) f)
 rw [show px q=Real.toNNReal (v:ℝ) from (by unfold pitches q; rw [eject_at]; rfl)]
 change (X₀ x) _=(S₀ x).E (Real.toNNReal (v:ℝ)) ((X₀ x) f); rw [time_even Y H V G a c x j v p0]; apply congrArg (X₀ x); exact Subtype.ext ((cover_solo ..).trans (DFunLike.congr_fun (advance_even ..) f.val))
omit p0
lemma even_speaks (i:Trans j)(v:perch Λ) : leader Y H V G a c (eject i.val (accept Λ v)) x=x ∧ ∀ T' : (W (eject i.val (accept Λ v)) x)=x,
    (transportT Y H V G a c j (eject i.val (accept Λ v)) x x (by rw [eject_away i.val _ _ i.property.symm]) T').toLinearIsometry.toContinuousLinearMap = U x i v:=by
 refine ⟨by rw [star_leading,no_even], fun T'=>?_⟩
 let q:= eject i.val (accept Λ v); let hp:q j=0:=eject_away i.val _ _ i.property.symm
 let Z:= transportT Y H V G a c j q x x (ge_of_eq hp) T'
 apply DFunLike.coe_injective; apply (attains_full_axis Y H V G a j c x).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
 funext f; dsimp only [Function.comp_apply]; rw [owns_play]; have he:= native_taste Y H V G a c j q x x (ge_of_eq hp) T' f; rw [show pitches Λ j q=0 from (by unfold pitches; rw [hp]; exact Real.toNNReal_zero),OS.Semigroup.eZero] at he; exact he.trans (congrArg (X₀ x) (Subtype.ext ((cover_solo ..).trans (DFunLike.congr_fun (advance_even ..) f.val))))
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
