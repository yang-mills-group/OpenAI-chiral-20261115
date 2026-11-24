import YM.SU5.Selected.Affinity
/-! # Multi-compare regardless of order and viewpoints. Includes proof of real-locale readings
 on APPLICABLE chart points, not continuation outside of windows. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal
variable {I : Type*}{a:Axis}{M:Mesh}{H:Hilbert} (X: Repertoire I a M H)
namespace Repertoire
local notation "V"=> Axis → ℝ
local notation "P"=> X.sky.track
local notation "Ω" => X.light
local notation "E" i:max=> X.sea.E i
local notation "B"=> {b:Axis//b ≠ a}
local notation "A" i:max => X.op i
local notation "U" i:max v:max=> (X.sky.track.crew i).play v
local notation "Γ"=> marks M
local notation "K"=> X.sky.list
local notation "π" i:max=> ((P).stackS i)
local notation "Λ"=> (Axis→ Γ)
local notation "ρ" x:max=> ((x:marks M):ℝ)
local notation "ι" t:max=> show Axis→ℝ from fun i=> ρ (t i)
open Filming
local notation "Γ'"=> marks M
local notation "Ω'"=> X.light
local notation "W" x:max p:max j:max=> Function.update x (p:B).val (j+x (p:B).val)

local notation "P₀" => ((P).aviator K).orthogonalProjectionOnto
local notation "L" => (P).Realm K
local notation "Ξ"=> glass X.sky (daylight M) X.sea X.glides
/-! # Repertoire shifts across ALL spatial continuum translations on this read. -/
lemma diamond_add (a:Axis) (u v:V):diameter (a:=a) (u+v)=diameter (a:=a) u+diameter (a:=a) v:=by
 unfold diameter; exact map_add ..
lemma diamond_zero (a: Axis): diameter (a:=a) 0 = 0:= by unfold diameter; exact map_zero _
local notation "Ζ" z:max=> (Ξ).U (diameter z)
lemma front_add (u v:V)(i:I): X.frontend (u+v) i=X.frontend u i+v a:=by unfold frontend; rw [Pi.add_apply]; abel
lemma end_add (u v:V)(i:I): X.endline (u+v) i=X.endline u i+v a:=by unfold endline; rw [front_add]; abel
lemma room_add (l:List I)(v:I→V)(t:V) : (fun i=> v i+t) ∈ X.planeOK l ↔ v∈ X.planeOK l:=by
 suffices h:∀ b:Option ℝ,X.Correct l (Pages false) (fun i=>v i+t) (b.map (fun u:ℝ=> u+t a)) ↔ X.Correct l (Pages false) v b from h (none:Option ℝ)
 intro b; induction l generalizing b with
 | nil=>rfl
 | cons i l ih=>rw [Correct,Correct]; apply and_congr ?_ ?_
                · rcases b with _|v'; all_goals simp [Pages,front_add] -- tune
                rw [end_add]; exact ih (some (X.endline (v i) i))
lemma trajectory (x:Option ℝ)(i:I)(p t:V) : (X.gliding (x.map fun x=> x+t a) i (p+t)).comp (Ζ t)=(Ζ t).comp (X.gliding x i p):=by
 let S:=Ξ; have he : X.sep (x.map fun x=> x+t a) i (p+t)=X.sep x i p:=by rcases x with _|v; rfl; simp [sep,front_add] -- tune
 unfold gliding; rw [he]; have hm:(Ζ (p+t))=(Ζ t).comp (Ζ p):= by rw [add_comm,diamond_add,S.space]
 have hu:(Ζ (-(p+t))).comp (Ζ t)= Ζ (-p):=by rw [← S.space, ← diamond_add]; congr 2; abel
 rw [hm]; ext1 y; change (S.E _) ((Ζ t) ((Ζ p) (X.rack i ((Ζ (-(p+t))) ((Ζ t) y)))))=(Ζ t) (S.E _ _); rw [← ContinuousLinearMap.comp_apply (Ζ (-(p+t))), hu, ←ContinuousLinearMap.comp_apply (S.E _), S.independent]; rfl -- local S use rw
variable (h: ∀ t:OS.Cross a,(glass X.sky (daylight M) X.sea X.glides).U t X.origin=X.origin)
include h
lemma homogeneous (l:List I)(x:I→V)(t:V): X.reading l (fun i=>x i+t)= X.reading l x:=by
 have he(b:Option ℝ): X.roadList l (fun i=>x i+t) (b.map fun v=> v+t a)= (Ζ t) (X.roadList l x b):=by
    induction l generalizing b with
    | nil=> exact (h _).symm
    | cons i l ih=> rw [roadList,roadList,X.end_add,(show X.roadList l (fun i=> x i+t) (some _)= _ from ih (some (X.endline (x i) i))),←ContinuousLinearMap.comp_apply,X.trajectory]; rfl
 unfold reading; rw [(show X.roadList l _ none= (Ζ t) (X.roadList l x none) from he none)]; nth_rw 1 [← h (diameter t)]; exact LinearIsometry.inner_map_map (𝕜:=ℂ) (show L →ₗᵢ[ℂ] L from { (Ζ t).toLinearMap with norm_map':=(Ξ).unitary _}) _ _
end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.homogeneous
