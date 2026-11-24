import YM.SU5.Reconstruction.Cross.Slot
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/-!
# Whole words. CPB Atlas at lattice dense-group points, *absolute slot positions* and arbitrary compatible
ordering. Use actual normalized selected readings at the indicated common higher level.
-/
variable {L:Type*}
variable (f : L → Marks (tent Y H) false) (g : ∀ x, Gate Y H s j (f x))
local notation "X" x:max=> Gate Y H s j (f x)
local notation "O" a:max=> indoorOp Y H V Q Qt s j C c a
-- without V
noncomputable def orderWord (t:ℕ) (l': List L) (v:L→ Cover) : Marks (tent Y H) false := (l'.map (fun x=>relocateWorld Y H false (v x) (upGrade Y H s Q false (f x) t))).prod
local notation "W" t:max => orderWord Y H Q s f t
-- layout
-- typeclass issue Recursive def binder records Carry. `include` makes explicit arguments in prop
inductive Leaves (g : ∀ x, Gate Y H s j (f x)) : ℤ → List L → Prop
| blank (lo:ℤ) : Leaves g lo []
| append {x t l'} (p : (g x).start=t) (h:Leaves g (t+(g x).full) l') : Leaves g t (x::l')

def rawProduct (t:List L) (u : L→seeMesh (timeMesh Λ)) : (indoor Y H V Q Qt j false C c).Op := (t.map (fun i=> (O (g i)) (u i))).prod
local notation "Ξ" => rawProduct Y H V Q Qt s j C c f g
def rawTrace (t:List L) (u : L→seeMesh (timeMesh Λ)) := inner ℂ Ω (Ξ t u Ω)
local notation "δ" f:max t:max => upGrade Y H s Q false f t
local notation "g₀" s:max v:max => grid Μ s v
local notation "GU" s:max v:max => toR (M:=Μ) (grid Μ s v)
local notation "R" v:max => SlabMark.relocate K j v
-- consume widths from start. RP book carried jointly.
lemma gate_product_train (t:ℕ) (p : s ≤ t) (v : L → Cover) (ts: List L) (a₀:ℤ)
    (h : Leaves Y H s j f g a₀ ts) (q : ∀ x∈ts,(g x).admits (GU t (v x))) :
      ∃ z : Tower.Field Y H t j 0 false,
        (Ξ ts (grid Μ t ∘ v)) Ω=(T t) z ∧ z.val = (R (-castor Μ s t a₀)) (((W t) ts v) : Marks K false).val := by
  induction h with
  | blank lo=>
     refine ⟨unity Y H j 0 false t, (Selected.root Y H V t Q Qt j false C c).symm, (relocate_unit K j _).symm⟩
  | @append x n ts i h ih=>
    obtain ⟨z,e,a⟩ := ih (fun i u=> q i (List.Mem.tail _ u))
    rw [rawProduct,List.map_cons,List.prod_cons,mul_apply_eq_comp]; change ∃ y : Tower.Field Y H t j 0 false, (O (g x)) (g₀ t (v x)) ((Ξ ts _) Ω)=_ ∧ _
    rw [e]
    obtain ⟨y,ht,hy⟩:= gate_bud Y H V Q Qt s j C c (g x) t p (v x) z (q _ (List.mem_cons_self))
    let A₀:= (W t) ts v
    let L₁:=relocateWorld Y H false (v x) (δ (f x) t)
    have he: (((W t) (x::ts) v):Marks K false).val= L₁.val*A₀.val := by
       unfold orderWord L₁ A₀; rw [List.map_cons,List.prod_cons]; rfl -- may identical
    refine ⟨y,ht,?_⟩; rw [hy,a,he,relocate_mul,relocate_sums K j _ _ (marksSpec false A₀).1,i]
    -- now offsets
    rw [castor_add,castor_nat]; congr 2; abel

lemma train_lattice (t:ℕ) (p : s ≤ t) (v : L → Cover) (ts: List L) (a₀:ℤ)
    (h : Leaves Y H s j f g a₀ ts) (q : ∀ x∈ts,(g x).admits (GU t (v x))) :
     rawTrace Y H V Q Qt s j C c f g ts ((grid Μ t) ∘ v) = (Eχ t) (orderWord Y H Q s f t ts v) := by
  obtain ⟨x,v,a⟩:= gate_product_train Y H V Q Qt s j C c f g t p v ts a₀ h q -- shadow
  unfold rawTrace; rw [v, Selected.call]
  refine (_root_.Eq.trans ?_ (Selected.all_waiting Y H V t Q Qt j false C c _ (-castor Μ s t a₀) j))
  exact congrArg (Eχ t) (Subtype.ext a)

lemma order_word_perm (t:ℕ) {x y:List L}(p:x.Perm y)(v : L→ Cover) : orderWord Y H Q s f t x v=orderWord Y H Q s f t y v := by
 apply (p.map _).prod_eq'
 have he (t':List (Marks (tent Y H) false)) : t'.Pairwise Commute := by
    induction t' with
    | nil=> exact List.Pairwise.nil
    | cons i t ih=>
      constructor; swap; exact ih
      intro b h; exact Subtype.ext (even_tests K (marksSpec false i).1 (marksSpec false b).1)
 exact he _

lemma open_window (x:List L): IsOpen {u : L→Axis→ℝ| ∀ a∈x,(g a).within_ (u a)}:=by
  induction x with
  | nil=>simp
  | cons i t ih=>
    have h : {u : L→Axis→ℝ| ∀ a∈i::t,(g a).within_ (u a)} = (fun u : L→Axis→ℝ=>u i) ⁻¹' {v | (g i).within_ v} ∩ {u : L→Axis→ℝ| ∀ a∈t,(g a).within_ (u a)} := by ext; simp
    rw [h]; exact ((g i).open_gate.preimage (continuous_apply i)).inter ih

section
-- different axes (or same) and/or slot data, explicitly same response. all compatibles.
variable {j':Axis} (C' : Arena Y H Q.circuit j' 0 false) (c' : (displayAlgebra Y H V Q Qt j' false C') →⋆ₐ[ℂ] ℂ)
variable (g' : ∀ x, Gate Y H s j' (f x))
local notation "Mx" t:max => Selected.response Y H V t Q Qt j' false C' c'
lemma raw_agree [Finite L] {lo lz:ℤ} {x y:List L} (p:x.Perm y) (h : Leaves Y H s j f g lo x) (q : Leaves Y H s j' f g' lz y)
    (he : ∀ t (f : Marks (tent Y H) false), (Eχ t) f=(Mx t) f) (v : L→ seeMesh (timeMesh Λ))
    (A : ∀ i∈x,(g i).admits (toR (M:=timeMesh Λ) (v i))) (B : ∀ i∈y,(g' i).admits (toR (M:=timeMesh Λ) (v i))) :
    rawTrace Y H V Q Qt s j C c f g x v=rawTrace Y H V Q Qt s j' C' c' f g' y v:=by
  obtain ⟨t,ht,u⟩:= ((eventually_ge_atTop s).and (eventually_all.mpr (fun i : L=> grid_higher Μ (v i)))).exists
  choose w hw using u
  have hh:v=grid Μ t ∘ w:=(funext hw).symm
  rw [hh] at A B ⊢
  rw [train_lattice Y H V Q Qt s j C c f g t ht w _ _ h A, train_lattice Y H V Q Qt s j' C' c' f g' t ht w _ _ q B, he,order_word_perm Y H Q s f t p]
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.raw_agree
