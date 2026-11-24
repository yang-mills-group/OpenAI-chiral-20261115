import YM.SU5.Reconstruction.Pitch.Stem
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
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

local notation "τ"=> marks (loomD Λ)
variable (a:Axis) (c:∀ j, Arena Y H G.history.circuit j 0 false)
abbrev Warden : Type 0 := (displayAlgebra Y H V G.history G.clipped a false (c a)) →⋆ₐ[ℂ] ℂ
local notation "χ'" a:max => Warden Y H V G a c
variable (χ : Warden Y H V G a c)
local notation "Ω" a:max p:max=> osValue Y H V G a (c a) p
local notation "Ψ" p:max=> oneAt Y H V G a (c a) p
local notation "F'" s:max=> display Y H V s G.history G.clipped a false (c a)
local notation "D₀"=> (displayAlgebra Y H V G.history G.clipped a false (c a))
local notation "B"=> instrument Y H V G.history G.clipped a false (c a)
lemma ward_unique (c' : Warden Y H V G a c) (p : (Ω a c')=(Ω a χ)): χ=c':=by
 have he (s:ℕ)(x:Dome (tent Y H)): oneAt Y H V G a (c a) χ s x = oneAt Y H V G a (c a) c' s x:=by
    let y:= (⟨ticket Y H G s x,ticket_loose ..⟩: D false Set.univ)
    exact (os_ticket Y H V G a (c a) χ s x).symm.trans ((DFunLike.congr_fun p.symm y).trans (os_ticket Y H V G a (c a) c' s x))
 let R₀:= StarAlgebra.adjoin ℂ (Set.range (instrument Y H V G.history G.clipped a false (c a)))
 refine StarAlgHom.ext_topologicalClosure (S:=R₀) (star_cont χ) (star_cont c') ?_
 refine StarAlgHom.ext_adjoin (s:=Set.range (instrument Y H V G.history G.clipped a false (c a))) ?_
 intro x v; obtain ⟨⟨s,w⟩,q⟩:= v
 let r:= StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure R₀)
 change χ (r x)=c' (r x)
 rw [show r x= (F' s) w from Subtype.ext q.symm] -- parser may need (F' s)
 exact he s ⟨w.val,w.property.1⟩ -- defin lift
where star_cont (χ : displayAlgebra Y H V G.history G.clipped a false (c a) →⋆ₐ[ℂ] ℂ) : Continuous χ := map_continuous χ

local notation "A"=> Warden Y H V G a c
variable (j:Axis)
local notation "δ" i:max χ₁:max => displacement Y H V G.history G.clipped a false (c a) χ₁ i (c i)
lemma eye_reads (u:Trans a) (s:ℕ)(x:Dome (tent Y H)) : oneAt Y H V G a (c a) (χ.comp (turn_cap Y H V G a (c a) u)) s x = (Ψ χ) s (cruise u.val K ((Λ.R.L.val:ℤ)^s) x):=by
 change χ (turn_cap Y H V G a (c a) u ((F' s) (asLoose K x)))=_; rw [turn_takes Y H V G a (c a) u s (asLoose K x)]; rfl
lemma turns_value (u:Trans a) : osValue Y H V G a (c a) (χ.comp (turn_cap Y H V G a (c a) u))= (Ω a χ).comp (plusLaw Y H G u.val (eyeD Λ)) :=by
 ext1 x; obtain ⟨s,x,rfl⟩:= (eventually_enclosed Y H G x).exists
 let f:=cruise u.val (tent Y H) ((Λ.R.L.val:ℤ)^s) x.val
 rw [os_enclose,eye_reads,LinearMap.comp_apply, show plusLaw Y H G u.val (eyeD Λ) (enclose Y H G Set.univ false s x)=(⟨ticket Y H G s f,ticket_loose ..⟩:D false Set.univ) from Subtype.ext (trek_mark Y H G u.val (eyeD Λ) s ((Λ.R.L.val:ℤ)^s) eyeD_at.symm x.val), os_ticket]

variable (p:weft Λ)
-- $Θ_{j,p}$-mobility relation. Zero loops. Defines without presumption this on same fingerprint; future restoration test needed to show unbroken.
def Neighbor (χ χ'₀:Warden Y H V G a c):Prop:= osValue Y H V G a (c a) χ'₀ = (osValue Y H V G a (c a) χ).comp (plusLaw Y H G j p)
local notation "T" j:max t:max => Neighbor Y H V G a c j t
lemma move_zero_at : (T j 0) χ χ:= LinearMap.ext fun _=> congrArg (Ω a χ) (Subtype.ext (trek_zero ..)).symm
lemma successive {χ₀ χ₁ χ₂:A} {p q:τ} (x:(T j p) χ₀ χ₁)(y:(T j q) χ₁ χ₂) : (T j (p+q)) χ₀ χ₂ :=by
 unfold Neighbor at *; rw [y,x]; ext1 f; simp only [LinearMap.comp_apply]; exact congrArg (Ω a χ₀) (Subtype.ext (trek_add ..))
lemma even_branch (p: marks (dainty Λ)) : (T j (accept Λ p)) χ χ := by
 refine LinearMap.ext (fun f=> Eq.trans (Nymph.column_cost Y H V G a c χ j p f).symm (congrArg (Ω a χ) ?_)); apply Subtype.ext; change stride (tent Y H) j p f.val=trek K j (accept Λ p) f.val; rw [advance_even]
lemma eye_branch : ∃ χ'₀:A,(T j (eyeD Λ)) χ χ'₀ :=by
 obtain ⟨d,hd⟩:= exists_ne j; let u:Trans d:=⟨j,hd.symm⟩
 let χD:= displacement Y H V G.history G.clipped a false (c a) χ d (c d); let χN := χD.comp (turn_cap Y H V G d (c d) u)
 refine ⟨displacement Y H V G.history G.clipped d false (c d) χN a (c a),?_⟩
 unfold Neighbor; rw [os_across, show osValue Y H V G d (c d) χN = (Ω d χD).comp (plusLaw Y H G j (eyeD Λ)) from turns_value Y H V G d c χD u]; unfold χD; rw [os_across]
lemma neighbor_exists : ∃! χN:A,(T j p) χ χN:=by
 obtain ⟨y,h⟩ : ∃ x:A,(T j p) χ x := by
    obtain ⟨t,e|rfl⟩:= couple p; · rw [e]; exact ⟨χ,even_branch Y H V G a c χ j t⟩
    obtain ⟨x,v⟩:= eye_branch Y H V G a c χ j; exact ⟨x,successive Y H V G a c j v (even_branch Y H V G a c x j t)⟩
 exact ⟨y,h,fun z w=> ward_unique Y H V G a c z y (Eq.trans h (Eq.symm w))⟩
noncomputable def wagerUp (χ:Warden Y H V G a c) := (neighbor_exists Y H V G a c χ j p).exists.choose
local notation "Pz" j:max p:max χ₁:max => wagerUp Y H V G a c j p χ₁
lemma neighbor_wager : (T j p) χ (Pz j p χ) := (neighbor_exists Y H V G a c χ j p).exists.choose_spec
lemma neighbor_commits (f:A) (u: Neighbor Y H V G a c j p χ f) : Pz j p χ= f:= (neighbor_exists Y H V G a c χ j p).unique (neighbor_wager ..) u
lemma commit_mem (f:A) : (T j p) χ f ↔ Pz j p χ=f:= ⟨neighbor_commits Y H V G a c χ j p f, fun u=> u ▸ neighbor_wager ..⟩
@[simp] lemma no_step : wagerUp Y H V G a c j 0 χ=χ:= neighbor_commits Y H V G a c χ j _ _ (move_zero_at ..)
lemma push_add (q:τ) : wagerUp Y H V G a c j q (wagerUp Y H V G a c j p χ)=Pz j (p+q) χ:= (neighbor_commits Y H V G a c χ j (p+q) _ (successive Y H V G a c j (neighbor_wager ..) (neighbor_wager ..))).symm
lemma no_even (t: marks (dainty Λ)) : Pz j (accept Λ t) χ=χ:=neighbor_commits Y H V G a c χ j _ _ (even_branch ..)
lemma push_duo : Pz j p (Pz j p χ)=χ:=by obtain ⟨h,x⟩:=duo p; rw [push_add,←x,no_even]
lemma nearby_two : Pz j p χ=χ ∨ Pz j p χ=Pz j (eyeD Λ) χ := by
 obtain ⟨t,h|rfl⟩:=couple p; · rw [h,no_even]; exact Or.inl rfl
 rw [←push_add,no_even]; exact Or.inr rfl
lemma near_back : Pz j (-p) χ=Pz j p χ:=by nth_rw 1 [← push_duo Y H V G a c χ j p]; rw [push_add,add_neg_cancel,no_step]
lemma push_swap (i:Axis)(t:τ): wagerUp Y H V G a c i t (wagerUp Y H V G a c j p χ)=wagerUp Y H V G a c j p (wagerUp Y H V G a c i t χ):=by
 apply ward_unique; have h (a':Axis)(x:A) (p:τ) : (Ω a (Pz a' p x)) = (Ω a x).comp (plusLaw Y H G a' p):= neighbor_wager ..
 rw [h,h,h,h]; ext1 f; simp only [LinearMap.comp_apply]; exact congrArg (Ω a χ) (Subtype.ext (trek_cross ..))
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
