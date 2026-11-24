import YM.SU5.Reconstruction.Sleet.Cornice
import YM.SU5.Reconstruction.Sleet.Quiet
import YM.SU5.Reconstruction.Trap.Castle
/-! # Actual postures x-reading. Spectrum only charged by such polls, using THEIR AP budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)

local notation "Ω"=> osValue Y H V G a (C a) χ
-- 0 off ANY unlicensed Sky. All our queries get explicit budget.
def whiff (x:Sky (tent Y H)):ℂ:= if p:x∈ Domain Y H G false Set.univ then (Ω) ⟨x,p⟩ else 0
local notation "Ω'"=> whiff Y H V G C a χ
variable (j:Axis)

noncomputable def terrainK (x y:Axis)(p q: marks (timeMesh Λ)): placement Λ:= Function.update (Function.update 0 x p) y q
@[simp] lemma terrain_time {x y:Axis}(h:y≠x)(p q: marks (timeMesh Λ)) : terrainK x y p q x=p:= by unfold terrainK; rw [Function.update_of_ne h.symm,Function.update_self]
@[simp] lemma terrain_space (x y:Axis)(p q: marks (timeMesh Λ)): terrainK x y p q y=q:= by unfold terrainK; rw [Function.update_self]
lemma terrain_other (x y k:Axis)(p q: marks (timeMesh Λ))(h:k≠x)(t:k≠y): terrainK x y p q k=0:= by unfold terrainK; rw [Function.update_of_ne t,Function.update_of_ne h]; rfl
lemma terrain_reverse {x y:Axis}(h:y≠x)(p q: marks (timeMesh Λ)): terrainK x y p q =terrainK y x q p:= Function.update_comm h.symm _ _ _ -- tune
lemma terrain_sum {x y:Axis}(h:y≠x)(p q r t: marks (timeMesh Λ)): terrainK x y p q + terrainK x y r t = terrainK x y (p+r) (q+t):=by
 funext z; by_cases hv:z=x; subst z; simp [Pi.add_apply,h]
 by_cases hu:z=y; subst z; simp
 simp [Pi.add_apply,terrain_other _ _ _ _ _ hv hu]

lemma reversed_fit(q:Bool)(t:ℝ){x: Sky (tent Y H)}(e:x∈ Domain Y H G q (lowland j (-t))): (θ j) x∈ Domain Y H G q (flank j t):=by
 apply domain_mono Y H G ?_ (mirror_support Y H G j x e)
 rintro _ ⟨v,h,rfl⟩; change t≤ mirrorE j 0 v j; rw [mirrorE,if_pos rfl]; linarith [show v j≤ -t from h]
lemma frontLow {x: Sky (tent Y H)} {q:Bool} (t:ℝ)(p:x∈ Domain Y H G q (flank j t)): (θ j) x∈ Domain Y H G q (lowland j (-t)):= by
 apply domain_mono Y H G ?_ (mirror_support Y H G j x p); rintro _ ⟨v,h,rfl⟩; change mirrorE j 0 v j ≤ -t; rw [mirrorE,if_pos rfl]; linarith [show v j≥t from h]

lemma whiff_turn(x:Sky (tent Y H))(h:x∈D univ): whiff Y H V G C a χ x=osValue Y H V G j (C j) (wk j) ⟨x,h⟩:=by rw [whiff,dif_pos h, os_across Y H V G a (C a) χ j]
include V
lemma time_ordered{q:Bool}{x y:Sky (tent Y H)}(e:(θ j) x∈Domain Y H G q (flank j 0))(p:y∈Domain Y H G q (flank j 0))(u:placement Λ)(t:0≤ (u j).val): x*move K u y∈ Domain Y H G q Set.univ:= by
 have hv:= paired_forever Y H G j _ _ e (later_frame Y H V G j y u p t); rwa [mirror_twice] at hv
lemma measure_dials{u z:Sky (tent Y H)} (h:(θ j) u∈D (N j))(p:z∈D (N j)) {b:Axis}(q:b≠j) (v t:Gt)(e:0≤ v.val) :
    whiff Y H V G C a χ (u * move K (terrainK j b v t) z) =
    let y:= OSvector Y H V G j (C j) (wk j) ⟨z,p⟩
    let x:= OSvector Y H V G j (C j) (wk j) ⟨(θ j) u,h⟩
    inner ℂ x ((A₀ j).E (Real.toNNReal v.val) (((U₀ j).track.crew ⟨b,q⟩).play t y)):= by
 let s:= terrainK j b v t; have he:0≤(s j).val:=by unfold s; rw [terrain_time q]; exact e
 dsimp only; rw [whiff_turn Y H V G C a χ j _ (time_ordered Y H V G j h p s he)]
 let Ω₀:=(⟨move K s z,later_frame Y H V G j z s p he⟩ : D (flank j 0)); let X:=(⟨(θ j) u,h⟩: D (flank j 0)); have hx:= registered_pair Y H V G j (C j) (wk j) X Ω₀; have hv:(θ j) X.val* Ω₀.val=u*move K (terrainK j b v t) z:=congrArg (· * Ω₀.val) (mirror_twice j u) -- sig
 apply Eq.trans (congrArg (osValue Y H V G j (C j) (wk j)) (show (⟨u* move K s z,_⟩:D univ)= ⟨_,paired_forever Y H G j _ _ X.property Ω₀.property⟩ from Subtype.ext hv.symm))
 rw [←hx, show (Os j) Ω₀= _ from transported_ket Y H V G j (C j) (wk j) z p s he Ω₀.property]
 let i:Trans j:=⟨b,q⟩
 change inner ℂ _ ((A₀ j).E _ (transverse_play (U₀ j) s _))=_
 rw [show transverse_play (U₀ j) s= ((U₀ j).track.crew i).play t from (spotlight2 (U₀ j) v i t).2.2] -- remaining time
 unfold s; rw [terrain_time q]

lemma whiff_move{z: Sky (tent Y H)}(p:z∈ D univ)(v:placement Λ): whiff Y H V G C a χ (move K v z)=whiff Y H V G C a χ z:=by
 let h:move K v z∈ D univ:= domain_mono Y H G (subset_univ _) (moving Y H V G v z p); rw [whiff,dif_pos h, whiff,dif_pos p, moving_value]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
