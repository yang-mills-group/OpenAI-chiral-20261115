import GaugeFieldConstruction.PointAction
import GaugeFieldConstruction.Flavor

/-!
# U1. The (62) free calibration symbol spaces

Unit and the three row types with generation copies; use *all* lower degrees
through each expenditure. Complex spaces. On-shell spatial cost definition.
Use `Carries` to rotate below jump interfaces. Work on a common system through
grade five.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Cauchy Row Record Conj U1 LabelAction Raw
open Matter (Generation FlavorIndex)
namespace Calibration
inductive Floor where | three | four | five
open Floor
def SG : Floor → Submodule ℂ (J Row.g)  |  three=> ⊥  | four=>gFour | five=>gFive
def SF : Floor → Submodule ℂ (J f) | three=>fThree | four=>fFour | five=>fFive
def SX : Floor → Submodule ℂ (J x) |  three => ⊥ | four=>⊥ | five=>xFive
abbrev UG (i) := ↥(SG i)
abbrev UF (i) := ↥(SF i)
abbrev UX (i) := ↥(SX i)
abbrev Fragment (s : Type*) := FlavorIndex → s
abbrev UV (i : Floor) := (ℂ × (UG i × (Fragment (UF i) × Fragment (UX i))))
variable {α β : Type*}

/-- motion/c structure compatible with the quotient. -/
structure Grade (R : Record α β) (F : Flip α) (Q : Submodule ℂ (J α)) extends Carries R Q where
  way (x : Q) : F x.val∈Q
  star (s) (x y : Q) (e : y.val=F x.val) : F (moves s x).val=(moves s y).val
  fin : FiniteDimensional ℂ Q
namespace Grade
variable (R : Record α β) (F : Flip α)
private theorem blank : (Record.space (fun i : Empty => (Empty.elim i : J α)))=⊥ := by
  unfold space
  rw [Fintype.range_linearCombination,Set.range_eq_empty,Submodule.span_empty]

def cert {γ : Type*} [Fintype γ] (A : Labels γ) (q : γ→ J α) (h : R.Reading A q) (e : ∀ i,F (q i)=q i) : Grade R F (space q) where
  toCarries:=Carries.basic A q h
  way i:= Carries.converts q F e i.property
  star s x y u:= Carries.c_pres A q h F e _ _ _ u s
  fin:= by unfold space; rw [Fintype.range_linearCombination]; exact FiniteDimensional.span_of_finite ℂ (Set.finite_range q)
-- Prop Nonempty so can rewrite
lemma bottom : Nonempty (Grade R F ⊥) := by
  let q (i : Empty) := Empty.elim (C:=J α) i -- fix
  have h :space q=⊥ := blank
  rw [← h]; exact ⟨cert R F (Labels.unitL Empty) q ⟨fun _ _ _ _ i=> Empty.elim i⟩ (fun i=>Empty.elim i)⟩

end Grade
private lemma gaugeP (i : Floor) : Nonempty (Grade recG cG (SG i)) := by
  cases i with
  | three => exact Grade.bottom ..
  | four => exact ⟨Grade.cert _ _ _ _ readingTg g_tr⟩ -- tune dots
  | five =>
    change Nonempty (Grade _ _ (space evalTg ⊔ space evalG)); rw [← space_sum]
    exact ⟨Grade.cert recG cG _ _ (reading_add readingTg readingG)
      (fun i => Sum.rec (fun j => by simpa only [Sum.elim_inl] using g_tr j) (fun j=>by simpa only [Sum.elim_inr] using g5_tr j) i)⟩
private lemma matterP (i : Floor) : Nonempty (Grade ph cF (SF i)) := by
  let Z := Sum.elim B evalTf
  have he (i) : cF (Z i) = Z i := by cases i with
                                        | inl i=>exact f3_tr i
                                        | inr j=> exact f4_tr j
  cases i
  · exact ⟨Grade.cert _ _ _ _ readingB f3_tr⟩
  · change Nonempty (Grade _ _ (space B⊔space evalTf)); rw [← space_sum]; exact ⟨Grade.cert _ _ _ Z (reading_add readingB readingTf) he⟩
  change Nonempty (Grade _ _ ((space B⊔space evalTf)⊔space evalF)); rw [← space_sum, ← space_sum]
  exact ⟨Grade.cert _ _ _ _ (reading_add (reading_add readingB readingTf) readingF) (fun i=>by
    cases i with
    | inl j=> exact he j
    | inr k=> exact f5_tr k)⟩
private lemma mixedP (i : Floor) : Nonempty (Grade recX cX (SX i)) := by
  cases i with
  | five => exact ⟨Grade.cert _ _ _ _ readingX x5_tr⟩
  | _ => exact Grade.bottom ..
def gauge (i) := Classical.choice (gaugeP i)
def matter (i) := Classical.choice (matterP i)
def mixed (i) := Classical.choice (mixedP i)

instance (i : Floor) : FiniteDimensional ℂ (UG i) := (gauge i).fin
instance (i : Floor) : FiniteDimensional ℂ (UF i) := (matter i).fin
instance (i : Floor) : FiniteDimensional ℂ (UX i) := (mixed i).fin
set_option synthInstance.maxSize 5000 in
instance (i : Floor) : FiniteDimensional ℂ (UV i) := inferInstanceAs (FiniteDimensional ℂ (Prod _ _))

theorem belowg (i) : SG i≤SG five := by cases i with
                                        | three => exact bot_le
                                        | four => exact le_sup_left
                                        | five => exact le_rfl
theorem belowf (i) : SF i ≤ SF five := by cases i with
                                       | three => exact le_trans (show fThree≤fFour from le_sup_left) le_sup_left
                                       | four => exact le_sup_left
                                       | five=> exact le_rfl
theorem belowx (i) : SX i ≤ SX five := by cases i with
                                        | five=> exact le_rfl
                                        | _ => exact bot_le
set_option synthInstance.maxSize 8000

def lift (i) : UV i →ₗ[ℂ] UV five where
  toFun u:= (u.1,⟨_,belowg i u.2.1.property⟩,(fun j=>⟨_,belowf i (u.2.2.1 j).property⟩),(fun j=>⟨_,belowx i (u.2.2.2 j).property⟩))
  map_add' u v:= rfl; map_smul' z v:= rfl
lemma inject (i : Floor) : Injective (lift i) := by
  intro u v h
  obtain ⟨h, k⟩:= Prod.mk.inj h; obtain ⟨i,j⟩:= Prod.mk.inj k
  obtain ⟨j,l⟩:= Prod.mk.inj j
  exact Prod.ext h (Prod.ext (Subtype.ext <| Subtype.mk.inj i) (Prod.ext
    (funext fun p=>Subtype.ext (Subtype.mk.inj (congr_fun j p)))
    (funext fun p=>Subtype.ext (Subtype.mk.inj (congr_fun l p)))))
end Calibration
end YM.GaugeFieldConstruction
