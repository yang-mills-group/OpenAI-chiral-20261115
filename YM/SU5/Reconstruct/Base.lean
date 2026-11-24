import YM.SU5.Reconstruct.Avenue
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

section film
/-!
# The wide-screen chart, algebraic calculation

Separate marks on the same clock. Film computes in ANY Hilbert room in
this orientation, once cast chosen. Opens at base moment BEFORE paying price
for turns, end mark includes paid temporal weight. Left endpoint u is
arbitrary in VEV (thermal clock on negative times is clamped (!) and still
leaves Ω fixed there as elsewhere). In obtaining ALL grid identities with
actual supported marks we work at safe u, never claim future-relay apart
when times run backwards. -/

variable {σ A':Type} (low wide:σ→ A') [AddGroup A'] (v:σ→ A')
variable {B':Hilbert} (Op:σ→ B'.Op) (blank:A'→B'.Op) (ready:B')
-- generic film for reuse (avoid definitional explosions around Entry)
def parkFilm : List σ → A' → B'
| [],_=>ready
| i::z,u=> blank (low i + v i - u) (Op i (parkFilm z (low i +wide i+ v i)))
lemma film_step (z:List σ)(i:σ)(u:A') : parkFilm low wide v Op blank ready (i::z) u= blank (low i+v i-u) (Op i (parkFilm low wide v Op blank ready z (low i+wide i+ v i))) := rfl
end film
section here
variable (C : ∀ i: Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
variable {s:ℕ}{j:Axis}{σ:Type} {U:σ→ Set RSpace}{x:∀ i,Pol Y H (U i)}
variable (F:Board Y H D s j U x)
local notation "M"=> timeMesh Λ
local notation "Rr" i:max=> inAxis Y H D G C c i
local notation "L₀" i:max => indoor Y H V Q Qt i false (C i) (Rr i)
local notation "Op" a:max => procession Y H V Q Qt j false (C j) (Rr j) a
local notation "p₀" i:max=> doorstep Y H V Q Qt i false (C i) (Rr i)
open StripCard
abbrev bottomPlay (i:σ) := StripCard.fromBase Y H D (F i)
abbrev widthPlaying (i:σ) := breadthOn Y H D (F i)
def hallCall (i:σ) := entrance Y H D.univ_ s G.history G.clipped j false (C j) (composer Y H s j (F i).cargo) (F i).paidH
-- store drive B not Π yet
lemma hall_higher (i:σ)(u:ℕ)(v:s≤u): hallCall Y H D G C (finer Y H D G F u v) i=hallCall Y H D G C F i:= by
 apply Subtype.ext; exact (refined_box Y H V s Q Qt j false (C j) (F i).span (composer Y H s j (F i).cargo) (F i).paidH u v).symm
local notation "Ω̂"=> placement Λ
local notation "ζ₀" i:max z:max=> atEstate Y H V Q Qt i false (C i) (Rr i) z
local notation "B₀"=>hallCall Y H D G C F
local notation "μ"=>physPos Λ
lemma bottom_extend (u:ℕ)(p:s ≤ u): bottomPlay Y H D (finer Y H D G F u p)=bottomPlay Y H D F:=funext fun i=> first_h Y H D G _ u p
lemma width_extend (u:ℕ)(p:s ≤ u) : widthPlaying Y H D (finer Y H D G F u p)=widthPlaying Y H D F:=funext fun i=>broad_h Y H D G _ u p
noncomputable def navFilm (v:σ→ placement Λ) : List σ → Ω̂ → L₀ j:= parkFilm (bottomPlay Y H D F) (widthPlaying Y H D F) v (fun i=>procession Y H V Q Qt j false (C j) (Rr j) (hallCall Y H D G C F i)) (atEstate Y H V Q Qt j false (C j) (Rr j)) (doorstep Y H V Q Qt j false (C j) (Rr j)) -- syntax
local notation "pF"=>navFilm Y H D G C c F
lemma nav_higher(v:σ→ placement Λ) (u:ℕ)(w:s≤u) : navFilm Y H D G C c (finer Y H D G F u w) v=pF v:=by
 unfold navFilm; rw [bottom_extend,width_extend]; simp_rw [hall_higher]
-- ambient invariance. Use upgrades to prove stack directly.
section
variable (j:Axis)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (C j) (inAxis Y H D G C c j)
local notation "S"=>turnstile Y H V Q Qt j false (C j) (Rr j)
local notation "E₁"=>ride Y H V Q Qt j false (C j) (Rr j)
lemma ground_pad (u:placement Λ)(y: Ρ): inner ℂ (p₀ j) ((ζ₀ j u) y)=inner ℂ (p₀ j) y:=by
 have h (u:ℝ≥0) : (E₁).E u (p₀ j)=p₀ j:= ride_affordable Y H V Q Qt j false (C j) (Rr j) (fun s n=>hinges Y H V s Q Qt j false (C j) (Rr j) n) _
 have hz (l:List (Trans j)): inner ℂ (p₀ j) ((S).raw l (fun i=>u i.val) y)=inner ℂ (p₀ j) y:=by
    have hv (i:Trans j)(p:marks M): ((S).crew i).play p (p₀ j)=p₀ j:= jamb Y H V Q Qt j false (C j) (Rr j) _ _
    induction l with
    | nil=> rfl
    | cons i l ih=>
       rw [Germ.Alliance.raw_step,ContinuousLinearMap.comp_apply]; let v:= (S).crew i; let z:= (S).raw l (fun i=>u i.val) y
       change inner ℂ _ (v.play _ z)=_; rw [←ContinuousLinearMap.adjoint_inner_left,Germ.Players.neg_adjoint,hv]; exact ih -- name type orientation?
 unfold atEstate; rw [ContinuousLinearMap.comp_apply]; rw [←ContinuousLinearMap.adjoint_inner_left, (E₁).sym,h]; exact hz _
end
lemma nav_before (v:σ→ placement Λ) (z:List σ) (u d:placement Λ): inner ℂ (doorstep Y H V Q Qt j false (C j) (Rr j)) (pF v z u) = inner ℂ (doorstep Y H V Q Qt j false (C j) (Rr j)) (pF v z d) := by
 cases z with | nil=>rfl | cons i z=> unfold navFilm; rw [film_step, film_step, ground_pad,ground_pad]
local notation "m₀"=>meshPos Λ s
local notation "Z₀"=> Marks (tent Y H) false
local notation "η₀" v:max=> relocateWorld Y H false v
lemma cad_one_by (u:Axis)(x':Marks K false)(i:ℤ): relocateWorld Y H false (i • step u) x'= moveMark Y H u false i x':=by
 apply Subtype.ext; rw [world_val]; refine (chart_piece K u _ (marksSpec false x').1).trans ?_
 let v:Cover:=i • step u
 have h(z:List (Trans u)): cad K (spare u z) (i • step u) x'.val = x'.val:=by
    rw [transverse_eq _ _ _ _ (fun _ => 0) (by intro j; simp [j.property])]
    have he: gaea u (fun _=>0)=0:= funext fun j=> by unfold gaea; split <;> rfl
    rw [he]; exact cad_zero K _ (marksSpec false x').1
 rw [h]; change relocate K u (v u) _ = relocate K u i _; rw [show v u=i by simp [v]]
lemma world_prod (v:Cover)(L':List (Marks K false)) : (η₀ v) L'.prod=(L'.map (η₀ v)).prod:= by
 induction L' with
 | nil => exact (marchOut Y H v (x:=1)).symm.trans (by rw [map_one]; rfl)
 | cons i z ih=>
   rw [List.map_cons,List.prod_cons,List.prod_cons,←ih]; apply Subtype.ext; rw [world_val]; change chart K v (i.val*z.prod.val)=((η₀ v) i).val*_ -- notation parse
   rw [world_val]; exact (cad_prod K _ v).trans (congrArg _ (world_val Y H false v _).symm) -- rw directions tune

end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
