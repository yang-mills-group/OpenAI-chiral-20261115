import YM.SU5.Selected.Affinity
/-! # Single chart domains include genuine weak-clause configurations in closure. -/
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
lemma ordered_length (l : List I) [DecidableEq I] (h:l.Nodup) : ∃ (p:I→ ℕ), l.Pairwise (fun i j=>p i < p j):=by
 induction l with
 | nil=> exact ⟨(0:I→ℕ),List.Pairwise.nil⟩
 | cons i l ih=>
     obtain ⟨ih0,v⟩:= List.nodup_cons.mp h
     obtain ⟨p,v⟩:=ih v; let q : I→ℕ:= update (fun i=>p i+1) i 0; refine ⟨q,List.pairwise_cons.mpr ⟨?_,?_⟩⟩
     · intro j q0; have hp:j≠i:=fun u=>ih0 (u ▸ q0); simp [q,hp]
     refine v.imp_of_mem ?_; intro a b ha hb e; have he(j:I)(h:j∈l): q j=p j+1:= update_of_ne (show j≠i from fun v=> ih0 (v ▸ h)) ..; simpa [he _ ha, he _ hb] using e -- signature
variable [DecidableEq I]
lemma circle_increases (l:List I)(u:I→V)(p:u∈ X.planeOK l)(n:I→ℕ)(g:l.Pairwise (fun i j=> n i<n j)) (ε:ℝ)(h:0<ε): (fun i=> Function.update (u i) a (u i a+ε*n i)) ∈ X.highway l:=by
 let F(i:I):= Function.update (u i) a (u i a+ ε*n i)
 have he(i:I): X.frontend (F i) i= X.frontend (u i) i+ε*n i:=by unfold F frontend; rw [Function.update_self]; abel
 have hz(i:I): X.endline (F i) i= X.endline (u i) i+ε*n i:=by unfold endline; rw [he]; abel
 have hl (b:Option (ℝ × ℝ)) (v: ∀ t, b=some t→ ∀ i∈ l,t.2 < ε*n i) (hm: X.Correct l (Pages false) u (b.map Prod.fst)) : X.Correct l (Pages true) F (b.map fun m=> m.1+m.2):=by
    clear p; induction l generalizing b with
    | nil=> trivial
    | cons i l ih=>
        have hp(z:ℝ)(p : (b.map fun t=>t.1+t.2)=some z) : z < X.frontend (F i) i:=by
           rcases b with _|t; · simp at p
           obtain ⟨u',v'⟩:= t; rw [←(Option.some.inj (by simpa only [Option.map_some] using p : some (u'+v')=some z)), he]; apply add_lt_add_of_le_of_lt (hm.1 u' rfl) (v _ rfl _ List.mem_cons_self)
        refine ⟨hp,?_⟩
        rw [hz]; have he' := List.pairwise_cons.mp g
        exact ih he'.2 (some (X.endline (u i) i, ε * n i)) (by intro t p v hv; rw [← Option.some.inj p]; exact mul_lt_mul_of_pos_left (by exact_mod_cast he'.1 v hv) h) hm.2
 exact hl none (by simp) p
lemma gap_area (l:List I)(h:l.Nodup) : X.planeOK l ⊆ closure (X.highway l):= by
 intro u p; obtain ⟨v,hv⟩:= ordered_length l h; let x(t:ℝ): I→V := fun i=> update (u i) a (u i a + t * v i)
 have ht: Continuous x:=continuous_pi (fun i=> continuous_pi (fun k=> by
    by_cases h:k=a; · subst k; unfold x; simp_rw [Function.update_self]; fun_prop
    unfold x; simp_rw [Function.update_of_ne h]; exact continuous_const))
 have he: x 0=u:=funext (fun i=> by unfold x; rw [zero_mul,add_zero,Function.update_eq_self])
 apply mem_closure_of_tendsto ((he ▸ ht.tendsto 0 : Tendsto x (𝓝 (0:ℝ)) (𝓝 u)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0)))
 filter_upwards [self_mem_nhdsWithin] with i p'; exact (circle_increases X l u p v hv _ p')
-- left margin condition: end preserved, start strictly improved from bigger to smaller footprint
variable (Y:Repertoire I a M H)
lemma encloses (he:∀ i u,X.endline u i= Y.endline u i)(hp:∀ i u,X.frontend u i< Y.frontend u i)(l:List I) : X.planeOK l ⊆ Y.highway l:=by
 intro x p; have ht(b:Option ℝ)(h:X.Correct l (Pages false) x b): Y.Correct l (Pages true) x b:=by
    clear p; induction l generalizing b with
    | nil=>trivial
    | cons i t ih=> exact ⟨fun i' e=> show i'<Y.frontend (x i) i from lt_of_le_of_lt (h.1 i' e) (hp i _), ih _ (he i (x i) ▸ h.2)⟩
 exact ht none p
end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.gap_area
