import YM.SU5.Reconstruction.AllGrades.Ancient
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
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
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open SelectionAnalysis Germ
open Nymph
local notation "M"=>timeMesh Λ
local notation "K₀"=>Works Y H V G D a b P
variable (A: Impetus Y H V G D a b P)
local notation "Wq" n:max=> walkC Y H a b n
local notation "E★" t:max k:max=> older Y H V G D a b t P A k
local notation "Ξ"=>dainty Λ
noncomputable def widerWheel (Λ:Preparation): Mesh:= ⟨(dainty Λ).L,(dainty Λ).Llarge,4,by norm_num⟩
local notation "Ξ₀"=> widerWheel Λ
include A in
lemma near_ages : Dense (⋃ i:ℕ, range (fun x:Works Y H V G D a b P => (E★ i 2) x)):=by
 apply (badges_roll Y H V G D a b 0 P).mono; intro v h; obtain ⟨i,h⟩:= Set.mem_iUnion.mp h; obtain ⟨x,rfl⟩:=h; exact old_registers Y H V G D a b _ P A x
noncomputable def atlasTimes : Many (widerWheel Λ) (Works Y H V G D a b P) where
 move s i:= E★ s i
 source s:= old_zero ..
 add s i j:= old_add ..
 close s i:= old_close ..
 refines s t i p:= old_grow Y H V G D a b s P A i t p
 small s i:= old_cost ..
 early:= near_ages Y H V G D a b P A
local notation "δ"=> atlasTimes Y H V G D a b P A
noncomputable def wheelTimes : OS.Semigroup (Works Y H V G D a b P) a:= (δ).monoAxis a
local notation "σ"=> wheelTimes Y H V G D a b P A
private lemma clockwise(s i:ℕ): (whenly Ξ s i) + (whenly Ξ s i)= whenly Ξ₀ s i :=by
 unfold whenly dainty widerWheel mill; change (i:ℝ≥0)*(2/_)+(i:ℝ≥0)*(2/_)=i*(4/((timeMesh Λ).L:ℝ≥0)^s); ring
include A in
lemma ages_track(n:ℕ):(σ).E (whenly (dainty Λ) s n) = E★ s n:=by
 let p:=σ; let i:= whenly (dainty Λ) s n; let z:= (E★ s n); let Q:= (clockwise (Λ:=Λ) s n); let o:= (E★ s (2*n))
 have t:o=p.E (whenly Ξ₀ s n):= ((δ).track_even s n).symm
 refine rooted (d:=o) (by nth_rw 1 [t]; exact (clockwise (Λ:=Λ) s n) ▸ (p.time i i).symm) ?_ ?_ (old_n ..)
 · unfold o; rw [two_mul n]; exact old_add ..
 · have h': i=i/2+i/2:= (add_halves i).symm
   change 0 ≤ p.E i; rw [h', p.time]; let V':= p.E (i/2); have ht: star V'= V':= p.sym _; change 0 ≤ V'* V'; have v2:= star_mul_self_nonneg V'; rwa [ht] at v2 -- tune cause i dependent h'
where
 rooted {T:Hilbert} {a b d:T→L[ℂ] T}(p:a*a=d)(q:b*b=d)(h:0≤a)(t:0≤b):a=b:=(CFC.sqrt_unique p h).symm.trans (CFC.sqrt_unique q t)
lemma ages_pose(n:ℕ)(x: Sc) : (σ).E (whenly (dainty Λ) s n) ((Bp s) x)= (Bp s) ((Wq n) x):=by rw [ages_track,old_now]
-- Front matter all even pitch includes CP1 stamps, and time CONT plus full analytic vertical spectrum energy.
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.ages_track
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.ages_pose
