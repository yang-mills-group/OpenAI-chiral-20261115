import YM.SU5.Reconstruction.Oblique.WindRose
import YM.SU5.Reconstruction.Sleet.Yak
/-! # fields actually within the diagonal true station. Currency of support & positivity question. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
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
local notation "D" => Domain Y H G
variable (P:Ramp) {J: Calibration}
open Stormwatch ConePrice Germ SelectionAnalysis
open YM.ConePrice.Storm
variable {f:Sky (tent Y H)}
local notation "Gt" => marks (timeMesh Λ)
local notation "Au" => placement Λ
-- upper positive strict half. glyph age all
noncomputable def landN (P:Ramp) : RSpace→ₗ[ℝ] ℝ where
 toFun x:= x P.a+x P.b
 map_add' x y:=by simp only [Pi.add_apply]; abel
 map_smul' z x:=by simp [mul_add]
noncomputable def hoursN (P:Ramp) : placement Λ →+ marks (timeMesh Λ) where
 toFun x:= x P.a+x P.b
 map_zero':=zero_add _
 map_add' x y:=by simp only [Pi.add_apply]; abel
lemma hour_age (p:placement Λ): landN P (coordinates Λ p)=(hoursN P p).val:=rfl
lemma landNp(P:Ramp): Continuous (landN P):= (show Continuous fun x:RSpace=>x P.a+x P.b from by fun_prop)
lemma land_turn(v:RSpace): landN P (P.s.act v)= -(landN P v):= by change P.s.act v P.a + P.s.act v P.b = -(v P.a+v P.b); rw [P.move_a,P.move_b]; abel
noncomputable def northD (P:Ramp):Set RSpace := {v:RSpace| 0 < landN P v}
noncomputable def southD (P:Ramp):Set RSpace := {v:RSpace| landN P v<0}
lemma tilted_N : P.s.act '' northD P⊆ southD P:=by
 rintro _ ⟨v,z,rfl⟩; change landN P (P.s.act v)<0; rw [land_turn]; exact neg_lt_zero.mpr z
lemma tilted_S : P.s.act '' southD P ⊆ northD P:=by rintro _ ⟨v,z,rfl⟩; change 0<landN P (P.s.act v); rw [land_turn]; exact Left.neg_pos_iff.mpr z
lemma N_disjoint(P:Ramp): Disjoint (southD P) (northD P):= Set.disjoint_left.mpr (fun _ e k=> not_le.mpr (show landN P _ <0 from e) (le_of_lt k))
local notation "Π" => Domain Y H G false (northD P)
local notation "S" => Domain Y H G false (southD P)
local notation "µ" => Domain Y H G false Set.univ
include V
lemma glides_S (v:f∈ S): gust P K f∈ Π := domain_mono Y H G (tilted_S P) (shelters Y H V G P v)
lemma glides_N (v:f∈ Π): gust P K f∈ S:= domain_mono Y H G (tilted_N P) (shelters Y H V G P v)
lemma on_Cover {f g:Sky (tent Y H)}(p:f∈ Π)(v:g∈ Π): gust P K f * g∈ µ:= domain_mult_to Y H G (glides_N Y H V G P p) v (N_disjoint P) (subset_univ _) (subset_univ _)
omit V
abbrev stretchD (P:Ramp) := @terrainK Λ P.a P.b
lemma hourMark(v t:Gt): hoursN P (stretchD P v t) = v+t:=by
 change terrainK _ _ v t P.a+terrainK _ _ v t P.b=_; rw [terrain_time P.cross,terrain_space]
lemma mark_zero (Λ:Preparation):stretchD (Λ:=Λ) P 0 0=0 := by funext i; simp [stretchD,terrainK,Function.update]
lemma stretch_down(v t:Gt): -stretchD P v t= stretchD P (-v) (-t):= by
 apply add_right_cancel (a:= -stretchD P v t) (show -stretchD P v t+stretchD P v t=stretchD P (-v) (-t)+stretchD P v t from by simp only [stretchD,terrain_sum P.cross,neg_add_cancel]; exact (mark_zero P _).symm) -- tune
lemma stretch_add(w x y z:Gt): stretchD P w x+stretchD P y z=stretchD P (w+y) (x+z):= terrain_sum P.cross ..
lemma stretch_turn(t u:Gt): P.s.act (stretchD P t u) = stretchD P (-u) (-t) := by
 unfold stretchD; funext i; by_cases h:i=P.a; · subst i; rw [P.move_a,terrain_time P.cross,terrain_space]
 by_cases e:i=P.b; · subst i; rw [P.move_b,terrain_time P.cross,terrain_space]
 rw [P.move_h _ h e,terrain_other _ _ _ _ _ h e,terrain_other _ _ _ _ _ h e]
include V
lemma advanceN(p:placement Λ)(v:0≤ (hoursN P p).val) (u:f∈Π): move K p f∈ Π:=by
 apply domain_mono Y H G ?_ (moving Y H V G p f u)
 rintro _ ⟨y,z,rfl⟩; show 0 < landN P _ ; rw [map_add,hour_age]; exact add_pos_of_pos_of_nonneg z v
noncomputable def sails (p:placement Λ)(h:0≤ (hoursN P p).val) : (Π)→ₗ[ℂ] (Π) := ((move K p).comp (Π).subtype).codRestrict Π (fun x=>advanceN Y H V G P p h x.property)
lemma issue_add (v t:placement Λ) (x y s)(f:Π) : sails Y H V G P v x (sails Y H V G P t y f)=sails Y H V G P (v+t) s f:=Subtype.ext (move_sum ..)
lemma pump_x(p:f∈ Domain Y H G false Set.univ): ∃ M:ℝ, ∀ t:placement Λ,M<(hoursN P t).val→ move K t f∈ Domain Y H G false (northD P):=by
 obtain ⟨A,B,C,d⟩:=(compact_domain Y H G).1 p
 obtain ⟨c,e⟩:= (B.image (landNp P)).bddBelow; refine ⟨-c,fun t h=> domain_mono Y H G ?_ (moving Y H V G t f d)⟩
 rintro _ ⟨x,y,rfl⟩; show 0<landN P (x+coordinates Λ t); rw [map_add,hour_age]; linarith [show c≤landN P x from e (Set.mem_image_of_mem _ y)]
lemma dump_x(p:f∈Domain Y H G false Set.univ): ∃ M:ℝ,∀ t:placement Λ,(hoursN P t).val< -M → move K t f ∈ Domain Y H G false (southD P):=by
 obtain ⟨A,B,C,d⟩:=(compact_domain Y H G).1 p
 obtain ⟨c,e⟩:= (B.image (landNp P)).bddAbove; refine ⟨c,fun t h=> domain_mono Y H G ?_ (moving Y H V G t f d)⟩
 rintro _ ⟨x,y,rfl⟩; show landN P (x+coordinates Λ t)<0; rw [map_add,hour_age]; linarith [show landN P x≤ c from e (Set.mem_image_of_mem _ y)]
omit V
lemma anywhere (Λ:Preparation)(r:ℝ): ∃ u:marks (timeMesh Λ),r<u.val:= by
 obtain ⟨u,x,z⟩:=(daylight (timeMesh Λ)).exists_mem_open isOpen_Ioi (nonempty_Ioi (a:=r)); exact ⟨⟨u,x⟩,z⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
