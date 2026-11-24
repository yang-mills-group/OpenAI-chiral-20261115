import YM.SU5.Reconstruction.PolarArchives.Lease
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
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
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)
local notation "A"=>Aurora Y H V G.history P.a false (C P.a)
local notation "Pc"=>album Y H V G C P.a
local notation "pay"=> LightBudget.prepaid Y H V G P.a (C P.a)
local notation "vc"=>seat0 Y H V G.history P.a false (C P.a)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank P.a 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject P.a t)
variable {q:Bool}{U:Set RSpace}

-- family of shifts including motion in both chronology-positive coordinates. Γ not thinned.
abbrev Tractor (Λ:Preparation)(P:Ramp) := {s: placement Λ // 0≤ s P.a ∧ 0 ≤ s P.b}
local notation "℘"=> Tractor Λ P
local notation "R"=> LightBudget.ruler Y H V G P.a (C P.a)
local notation "t₀"=> timeMesh Λ
local notation "S"=> ladder Y H V G.history.circuit P.a 0 false (C P.a)
local notation "Eₜ"=> advance Y H V G.history.circuit P.a 0 false (C P.a)
local notation "U" k:max=> ((S).crew k).play -- shadow U Set.. no actual use
local notation "α"=> Trans P.a
-- all stamps regardless TimeMesh purchase. paired motion includes all needed
private lemma near_ix (z:placement Λ)(v:α)(p:H₀): px ((U v) (z v.val) p)= px p:=by
 apply ext_inner_left ℂ; intro t; rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
   Players.shift_g _ _ _ t.val,show (U v) (-z v.val) (t.val:H₀)= t.val from PhaseChoice.shift_ground Y H V G P.a false (C P.a) v (-z v.val) t] -- scope
private lemma near_raw (z:placement Λ)(v:List α)(p:H₀): px ((S).raw v (fun i=> z i.val) p)=px p ∧ ‖(S).raw v (fun i=> z i.val) p‖≤ ‖p‖:=by
 induction v with
 | nil=>exact ⟨rfl,le_rfl⟩
 | cons i v ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply]; rw [near_ix Y H V G C P z i, Players.wins]; exact ih
lemma tractor_chip (z:placement Λ)(p:H₀): px (R z p)= px p ∧ ‖R z p‖≤‖p‖:=by
 unfold LightBudget.ruler
 rw [ContinuousLinearMap.comp_apply,← (px).comp_apply,behind]
 have h:=near_raw Y H V G C P z (look P.a) p
 exact ⟨h.1, (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (advance_small Y H V ..)).trans h.2)⟩
noncomputable def direct_ship (z:Axis)(t:Gt)(u:0≤t): Tractor Λ P:= ⟨eject z t,(by
 constructor
 · by_cases h:P.a=z
   · rw [h,eject_at]; exact u
   exact (eject_away z t P.a h).ge
 by_cases h:P.b=z
 · rw [h,eject_at]; exact u
 exact (eject_away z t P.b h).ge)⟩ -- exact .ge is desired? Eq .ge: rhs≤ lhs yes

lemma new_A (p:Gt): embarking P (eject P.a p)= eject P.b (-p):=by
 funext i; by_cases h:i=P.a
 · rw [h,embark_a,eject_away _ p P.b P.cross, eject_away _ _ P.a P.cross.symm]
 by_cases v:i=P.b
 · rw [v,embark_b,eject_at,eject_at]
 rw [embark_c _ P _ h v,eject_away _ _ _ h,eject_away _ _ _ v] -- argument order
lemma new_B (p:Gt): embarking P (eject P.b p)= eject P.a p:=by
 funext i; by_cases h:i=P.a
 · rw [h,embark_a,eject_at,eject_at]
 by_cases v:i=P.b
 · rw [v,embark_b,eject_away _ p P.a P.cross.symm, eject_away _ _ P.b P.cross,neg_zero]
 rw [embark_c _ P _ h v,eject_away _ _ _ v,eject_away _ _ _ h]
lemma new_other (p:Gt)(u:j≠P.a)(v:j≠P.b): embarking P (eject j p)= eject j p:=by
 funext i; by_cases h:i=P.a
 · rw [h,embark_a,eject_away _ p P.a u.symm, eject_away _ _ P.b v.symm]
 by_cases t:i=P.b
 · rw [t,embark_b,eject_away _ p P.a u.symm, eject_away _ _ P.b v.symm,neg_zero]
 exact embark_c _ P _ h t
lemma time_gen(t:Gt): R (eject P.a t)= Eₜ (Real.toNNReal (t:ℝ)) := by
 unfold LightBudget.ruler; rw [coordinates_eject,eject_at,show (fun i:Trans P.a=> eject P.a t i.val)=0 from funext (fun i=> by rw [eject_away _ _ _ i.property]; rfl), Germ.Alliance.raw_zero]; rfl
lemma space_gen (b : Trans P.a)(x:Gt): R (eject b.val x)= ((S).crew b).play x := by
 unfold LightBudget.ruler; rw [coord_at,eject_away _ x P.a b.property.symm]; change (Eₜ (Real.toNNReal (0:ℝ))).comp _=_; rw [Real.toNNReal_zero,advance_source]
 have he:(fun i:Trans P.a=> eject b.val x i.val)=Function.update (0:Trans P.a→marks (timeMesh Λ)) b x:=by
   funext i; by_cases h:i=b; · subst i; simp
   have h':i.val≠ b.val:=fun v=> h (Subtype.ext v); simp [h,h']
 rw [he, spotlight (S) _ (look_one P.a) (look_all P.a b)]; rfl

private lemma full_citizen(w:H₀)(p:∀ t:Gt,0≤t→ R (eject P.a t) w=w)(u:∀ (b:Trans P.a)(t:Gt),0≤t→ R (eject b.val t) w=w ∨ R (eject b.val (-t)) w=w): w∈ A:=by
 have h(b:Trans P.a) (t:Gt): (U b) t w=w :=by
    have mv(s:Gt): (U b) s w=w → (U b) (-s) w=w:=fun e=> by
       have z:=((S).crew b).returns (H₀) s w; rwa [e] at z
    have k(s:Gt)(v:0≤ s): (U b) s w=w:=by
       rcases u b s v with h|h
       · rw [space_gen Y H V G C P] at h; exact h
       rw [space_gen Y H V G C P] at h; simpa using mv (-s) h
    rcases le_total 0 t with a|a; exact k t a; simpa using mv (-t) (k (-t) (neg_nonneg.mpr a))
 apply (PhaseChoice.full_joint Y H V G P.a false (C P.a) w).2; refine ⟨?_,h⟩
 intro t; suffices v:(fun t=>Eₜ t w)=fun _:ℝ≥0=>w from congrFun v t
 apply (fills (timeMesh Λ)).denseRange_val.equalizer (advance_strong Y H V G.history.circuit P.a 0 false (C P.a) w).continuous continuous_const; funext s
 obtain ⟨s,n,v⟩:= MeshClock.split _ s.property; let t:Gt:= notch _ s n; dsimp only [Function.comp_apply]; rw [←v,← @Real.toNNReal_coe (whenly _ s n), ← Brazier.lantern_clock (Λ:=Λ),← time_gen Y H V G C P]
 exact p _ (show 0≤ Brazier.lantern Λ s n from (show 0≤ (Brazier.lantern Λ s n:ℝ) from by rw [Brazier.lantern_clock]; exact (whenly _ s n).property)) -- tune var rename
lemma tractor_first(p : H₀)(u:∀ v:Tractor Λ P,R v.val p=p): p∈ A:=
 full_citizen Y H V G C P p (fun b v=>u (direct_ship P P.a b v)) fun i b h=> Or.inl (u (direct_ship P i.val b h))
lemma tractor_second(p:H₀)(u:∀ v:Tractor Λ P,R (embarking P v.val) p=p): p∈ A:=by
 apply full_citizen Y H V G C P p
 · intro b hb; rw [←new_B]; exact u (direct_ship P P.b b hb)
 intro i b hb; by_cases h:i.val=P.b
 · right; rw [h,← new_A]; exact u (direct_ship P P.a b hb)
 left; rw [←new_other i.val P b i.property h]; exact u (direct_ship P i.val b hb)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
