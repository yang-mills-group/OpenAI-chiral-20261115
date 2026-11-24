import YM.SU5.Reconstruction.Pitch.Exit
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
local notation "Hp"=> ((H₀ x).space × (H₀ y).space)
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
variable (v: weft Λ)(v₀:0≤v)
variable (Vx : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)))
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
local notation "uY" f:max=> nearer Y H G j r u f
local notation "θ'"=> flipMark j K
open LightBudget
open Schedule
-- sequential decomposition with positive time. ACCOUNT all dense positions and epochs. Use Schedule.route on true purchase.
private lemma road_sum {B:Hilbert} (S': OS.Semigroup B j) (u v:RSpace)(x:u j≥0)(h:v j≥0) : Schedule.route S' (u+v)= (Schedule.route S' u).comp (Schedule.route S' v):=by
 let p:= @diameter j; have ht:p (u+v)=p u+p v:=by apply map_add (OS.Semigroup.SEP j) (WithLp.toLp 2 u) (WithLp.toLp 2 v)
 ext1 b; simp only [Schedule.route,Pi.add_apply, Real.toNNReal_add x h,ContinuousLinearMap.comp_apply]
 rw [show diameter (a:=j) (u+v)=_ from ht,S'.space,S'.time]
 simp only [ContinuousLinearMap.comp_apply]; exact congrArg (S'.E ((u j).toNNReal)) (DFunLike.congr_fun (S'.independent ((v j).toNNReal) (p u)) (S'.U (p v) b))
lemma road_space {B:Hilbert}(S':OS.Semigroup B j)(u:ℝ)(i:Axis)(h:i≠j): Schedule.route S' (eject i u)= S'.U (u • transversal j i h):=by
 unfold Schedule.route; rw [eject_away i _ _ h.symm, Real.toNNReal_zero, S'.eZero, show @diameter j (eject i u)= u • transversal j i h from ?_]; rfl
 apply Subtype.ext; ext x; by_cases p:x=j; · subst x; rw [show (diameter (a:=j) _).val j = 0 from (diameter (a:=j) _).property]; simp [h.symm,transversal]
 rw [diameter_at _ x p]; by_cases v:x=i <;> simp [v,transversal]
lemma road_time {B:Hilbert}(S':OS.Semigroup B j)(u:ℝ): Schedule.route S' (eject j u)= S'.E u.toNNReal:=by
 unfold Schedule.route; rw [eject_at, show @diameter j (eject j u)=0 from ?_,S'.uZero]; rfl
 apply Subtype.ext; ext x; by_cases v:x=j; · subst x; rw [show (diameter (a:=j) _).val j = 0 from (diameter (a:=j) _).property]; rfl
 rw [diameter_at _ x v]; simp [v]
private lemma step_point (q:Δ): coverPoint (p+q)=coverPoint p+coverPoint q:=rfl
lemma pitch_eject : coverPoint (eject j v)=eject j (v:ℝ):=by funext i; by_cases t:i=j<;> simp [t,coverPoint]

private noncomputable def summing (t:List Axis): Atlas Λ:=(t.map fun i=> eject i (p i)).sum
private lemma sums (t:List Axis)(e:t.Nodup) : summing p t j= if j∈t then p j else 0:=by induction t with
 | nil=> simp [summing]
 | cons i t ih=>
   rw [show summing p (i::t)=eject i (p i)+summing p t from rfl,Pi.add_apply,ih (List.nodup_cons.mp e).2]; by_cases v:j=i
   · subst i; simp [(List.nodup_cons.mp e).1];
   simp [v]

variable (TC: saunters Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))= ⊤)
 (TF: ConePrice.Forward (peninsula Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))))
 (HA:∀ j:Axis, Absent Y H V G a c j x)
local notation "St"=> peninsula Y H V G.history G.clipped j false (c j) (Vf x)
local notation "Ft"=> fort Y H V G.history G.clipped j false (c j) (Vf x)
local notation "pu"=> coreOs Y H V G j (c j) (Vf x)
include HA
lemma global_here : W p x = x:=by
 unfold leader; generalize ordinate=y; induction y with
 | nil=>rfl
 | cons i t ih=> change meritStyle Y H V G p t a c (wagerUp Y H V G a c i (p i) x)=x; rw [← star_leading,alwaysAt Y H V G a c i x (p i) (HA i),ih]
include TF TC
private lemma pace_at (f g:Domain Y H G false (flank j 0))(i:Axis) (p:Atlas Λ)(v1:0≤p j)(u:g.val=trek K i (p i) f.val): pu g=Schedule.route St (eject i ((p i):ℝ)) (pu f):=by
 by_cases e:i=j; swap
 · rw [road_space _ _ _ _ e]; exact (congrArg pu (Subtype.ext u: g=bystander Y H G j (p i) ⟨i,e⟩ f)).trans (actual_real_space Y H V G a c j x (p i) TC TF ⟨i,e⟩ (HA i) f)
 subst i; rw [road_time]; apply Subtype.ext
 rw [show (((St).E (Real.toNNReal ↑(p j)) (pu f):Ft).val:H₀ x)= (S₀ x).E _ (pu f).val from rfl,voice_full Y H V G j (c j) (Vf x) TC,voice_full Y H V G j (c j) (Vf x) TC]; exact (congrArg (X₀ x) (Subtype.ext u: g=prepareTurn Y H G j (p j) f v1)).trans (spent_clock Y H V G a c j x (p j) v1 f (HA j))
include k
lemma roll_every (f: Domain Y H G false (flank j 0)) : coreOs Y H V G j (c j) (Vf x) (promenadeFront Y H G j p f k)= Schedule.route (peninsula Y H V G.history G.clipped j false (c j) (Vf x)) (coverPoint p) (pu f):=by
 let p1 := (fun t:List Axis => summing p t);
 have he : ∀ t:List Axis,t.Nodup→∀ q:Atlas Λ,summing p t = q →∀ v:0≤q j, pu (promenadeFront Y H G j q f v)= Schedule.route (St) (coverPoint q) (pu f) :=by
    intro t h; induction t with
    | nil=>
       intro q v n; change (0:Δ)=_ at v; subst q;
       rw [show coverPoint (0:Δ)=eject j (0:ℝ) from (funext fun i=>by change 0=eject j (0:ℝ) i; by_cases v:i=j<;>simp [v]),road_time, Real.toNNReal_zero, OS.Semigroup.eZero]; exact congrArg pu (Subtype.ext (constell_zero ..))
    | cons i t ih=>
       intro q v n; subst q
       let g:= eject i (p i); let z:= promenadeFront Y H G j; let n':t.Nodup:= (List.nodup_cons.mp h).2; have hx:0≤ summing p t j:=by rw [sums _ _ t n']; split; exact k; exact le_refl _
       let f':= promenadeFront Y H G j (summing p t) f hx
       have hu: 0≤g j:=by
          unfold g; by_cases v:j=i; · subst i; rwa [eject_at]
          rw [eject_away i _ _ v] --indentation
       let y:= z (g+summing p t) f n
       change pu y= Schedule.route (St) (coverPoint (g+summing p t)) (pu f); rw [step_point,road_sum j (St) _ _ hu hx, ContinuousLinearMap.comp_apply, ← ih n' (summing p t) rfl hx, show coverPoint g=eject i ((p i):ℝ) from pitch_eject ..]; apply pace_at Y H V G a c j x TC TF HA _ _ i p k
       change constellation (g+summing p t) _ _ = _; rw [←cover_plus]; exact cover_solo .. -- ] -- tune
 refine he ordinate ordinate_one p (funext fun i=> (sums i p ordinate ordinate_one).trans (if_pos (ordinates i))) k
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
