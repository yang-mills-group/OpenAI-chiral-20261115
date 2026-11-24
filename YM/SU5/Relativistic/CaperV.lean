import YM.SU5.Selected.SpatialCard
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric
open CF.Buffered.Afterglow.Tower MeshClock Germ
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} {Γ : AddSubgroup ℝ} {I : Type*} [DecidableEq I] {j:I}
local notation "D₀"=> {x:I // x ≠ j}
variable (X : Sunbelt j Γ H) (d : Dense (Γ:Set ℝ)) (x y:H)
local notation "P₁"=> X.track
local notation "U" i:max a:max=> ((P₁).crew i).play a
lemma remembered (u:I→Γ)(i:D₀)(l:List (D₀))(q:ContinuousAt (fun a:Γ=>X.playback x y (Function.update u i.val a) l) (u i.val)) : X.playback x y u (i::l)=X.playback x y u l:=by
 let w:= u i.val; let E:H→L[ℂ]ℂ:= (innerSL ℂ x).comp (X.plane (Function.update u i.val 0)); let y':= X.track.stackS l y; let P:= (P₁).crew i
 have h(a:Γ): E (P.play a y')= X.playback x y (Function.update u i.val a) l := (X.playback_zero ..).symm
 have he:(fun a=> E (P.play a y'))= (fun a:Γ=> X.playback x y (Function.update u i.val a) l):=funext h
 have hg:= P.retains_at E y' w (show ContinuousAt _ w from he.symm ▸ q)
 have ht: Function.update u i.val w=u:= Function.update_eq_self ..
 rw [←ht, X.playback_step, X.playback_zero]
 exact hg
variable (R:{x:I // x≠j} → Set ℝ)(O:∀i, IsOpen (R i))
def Passport (R:{x:I//x≠j}→Set ℝ)(u:I→Γ):=0≤ (u j).val ∧ ∀ i:{x:I//x≠j}, (u i.val).val∈ R i
include O
lemma passport_cont (i:D₀)(u:I→Γ)(p:Passport R u): ∀ᶠ a:Γ in nhds (u i.val), Passport R (Function.update u i.val a):=by
 filter_upwards [(continuous_subtype_val.tendsto _).eventually ((O i).mem_nhds (p.2 i))] with a ha
 have hx: Function.update u i.val a j=u j:= update_of_ne (Ne.symm i.property) ..
 refine ⟨?_,fun b=>?_⟩; · rw [hx]; exact p.1
 by_cases h:i=b; · subst b; rw [Function.update_self]; exact ha
 rw [Function.update_of_ne (show b.val≠i.val from fun q=>h (Subtype.ext q.symm))]; exact p.2 b
lemma album_r (u:I→ Γ)(p:Passport R u)(l:List D₀)(q:∀v,Passport R v→∀i∈l, ContinuousAt (fun a:Γ=> X.playback x y (Function.update v i.val a) []) (v i.val)): X.playback x y u l=X.playback x y u [] :=by
 induction l generalizing u with
 | nil=>rfl
 | cons i l ih=>
    have h(v:I→Γ)(p:Passport R v): X.playback x y v l=X.playback x y v []:= ih v p (fun v w t x=> q v w t (List.Mem.tail i x))
    rw [remembered X x y u i l, h u p]
    have ht := q u p _ List.mem_cons_self
    apply ht.congr
    filter_upwards [passport_cont R O i u p] with a ha; exact (h _ ha).symm -- congr type
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.album_r
