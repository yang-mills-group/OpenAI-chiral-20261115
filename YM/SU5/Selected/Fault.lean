import YM.SU5.Selected.Order
import YM.Compact.State

/-!
# Characterizing ergodic *vacua* in the compressed systems

With an actual commutative C⋆ algebra `A` holding all the compressed moments and
`W` cyclic on the *uncompressed* normed slab algebra B. Does not require
compactness of the joint ground representation. `Fixed` here will mean for
all elements of `steps` (both heat and dense-grid spatial translations in
application; NOT including a distinguished projection onto the old ground).
Character alone is a possibly insufficient test. Prove the following escape
criterion instead: for each b, subtract elements in the span of `(u-1)c` at
translated boxes and **arbitrary** c. Their images test exactly off-ground
evaluation, both before and after selection.

Total-length convergence in the original H gives integral convergence via common
spectrum probability. Selection will require only **vanishing infimum** of a
character evaluation at given b. No exchange of operator-norm limit and pointwise
limits, no unexamined spectrum topology. Use actual positivity at `χ` to show the
pointwise defect can thus be made arbitrarily small for a.e. χ by Markov's inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
open Function Filter Set Topology NormedSpace MeasureTheory Measure ContinuousMap WeakDual
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ComplexOrder
variable {A B W : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {D:Submodule ℂ W} [CompleteSpace D]

-- GNS notation. Prefer transfer from a bound to ensure inherit operators.
variable (X : B →ₚ[ℂ] ℂ)
noncomputable def implement : B →⋆ₐ[ℂ] (X.GNS →L[ℂ] X.GNS) := X.gnsStarAlgHom
noncomputable def vector : X.GNS := (X.toPreGNS 1 : X.PreGNS)
noncomputable def vectorForm : B →L[ℂ] X.GNS :=
  ((((ContinuousLinearMap.apply ℂ X.GNS (vector X)).toLinearMap).comp
    ((implement X).toAlgHom.toLinearMap))).mkContinuousOfExistsBound (by
      refine ⟨‖vector X‖,fun b=>?_⟩
      change ‖implement X b (vector X)‖ ≤ _
      apply ((implement X b).le_opNorm _).trans
      rw [mul_comm ‖vector X‖]; exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le (implement X) b) (norm_nonneg _)) -- name
lemma vectorForm_gns (b : B) : vectorForm X b = ((X.toPreGNS b : X.PreGNS) : X.GNS) := by
  change (X.leftMulMapPreGNS b).completion _ = _
  unfold vector -- tune
  rw [ContinuousLinearMap.completion_apply_coe]; congr 1
  change X.toPreGNS (b*1)= _; rw [mul_one]
lemma vector_unit : vectorForm X 1=vector X := vectorForm_gns ..
lemma frequency : DenseRange (vectorForm X) := by
  apply UniformSpace.Completion.denseRange_coe.mono
  rintro p ⟨x,rfl⟩
  obtain ⟨v,rfl⟩:= X.toPreGNS.surjective x
  exact ⟨v,vectorForm_gns X v⟩
lemma form_is (b c : B) : inner ℂ (vectorForm X b) (vectorForm X c)= X (star b*c) := by
  rw [vectorForm_gns,vectorForm_gns,UniformSpace.Completion.inner_coe]; rfl
lemma read_is (b:B) : inner ℂ (vector X) (implement X b (vector X))=X b := by
  change inner ℂ _ (vectorForm X b)= _
  rw [←vector_unit X,form_is,star_one,one_mul]

variable (D)
-- S.station already concrete. A character need not be normal!
structure Transaction (A B : Type*) [CommCStarAlgebra A] [CStarAlgebra B] (D : Submodule ℂ W)
    [CompleteSpace D] where
  station : B →⋆ₐ[ℂ] (W →L[ℂ] W)
  corner : A →⋆ₐ[ℂ] (D→L[ℂ]D)
  mono_ : Injective corner
  mark : B →ₗ[ℂ] A
  match_P (b) : corner (mark b) = D.orthogonalProjectionOnto.comp ((station b).comp D.subtypeL)
  original : D
  unit : ‖original‖=1
  searches : DenseRange fun b => station b original.val
  steps : Set B
  star_move (b:B) (h:b∈steps) : star b∈steps
  grounds (x : W) : x∈D ↔ ∀ a∈steps, station a x=x

namespace Transaction
variable {D} (Q : Transaction A B D)

lemma nonnegative {b:B}(p:0≤b):0≤ Q.mark b := by
  refine (reflects_pos (A:= D→L[ℂ]D) (B:=A) Q.corner Q.mono_ (Q.mark b)).2 ?_
  rw [Q.match_P]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 (((ContinuousLinearMap.nonneg_iff_isPositive _).1
    (map_nonneg Q.station p)).orthogonalProjectionOnto_comp D)

lemma one_mark : Q.mark 1=1 := by
  apply Q.mono_
  rw [Q.match_P,map_one,map_one]
  ext1 b
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self b
end Transaction

variable {D}
-- characters
abbrev Resident (A : Type*) [CommCStarAlgebra A] := ↥(WeakDual.characterSpace ℂ A)
local notation "X₀"=> Resident A
noncomputable def eye (x:X₀) : A→⋆ₐ[ℂ] ℂ :=
  (ContinuousMap.evalStarAlgHom ℂ ℂ x).comp (gelfandStarTransform A : A →⋆ₐ[ℂ] C(X₀,ℂ))
lemma eyeline (x:A): Continuous (fun y:X₀=> eye y x) := (gelfandStarTransform A x).continuous
namespace Transaction
variable (T:Transaction A B D) (x:Resident A)
noncomputable def selected : B →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (((eye x).toAlgHom.toLinearMap).comp T.mark)
  (fun _ p=> map_nonneg (eye x) (T.nonnegative p))
lemma selected_look (b : B) : T.selected x b= eye x (T.mark b):=rfl
lemma selected_one : T.selected x 1=1 := by rw [selected_look,T.one_mark,map_one]
local notation "S"=> T.station
local notation "sω"=> T.original
local notation "t"=> T.corner

lemma matchVal (b:B) (x:D) : t (T.mark b) x=D.orthogonalProjectionOnto (S b x.val):= by rw [match_P]; rfl
lemma match_norm (b:B) (x:D) : ‖S b x.val‖^2 = (inner ℂ x (t (T.mark (star b*b)) x)).re := by
  rw [matchVal,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,map_mul,map_star]
  change _= (inner ℂ (x.val:W) ((ContinuousLinearMap.adjoint (S b)) (S b x.val))).re
  rw [ContinuousLinearMap.adjoint_inner_right]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
lemma fixed_value (b:B) (x:B) (h:x∈T.steps) : T.mark (x*b)=T.mark b ∧ T.mark (b*x)=T.mark b := by
  have he(x:B)(p:x∈T.steps)(u:D): S x u.val=u.val := (T.grounds _).1 u.property x p
  constructor
  · apply T.mono_; ext1 c; apply ext_inner_left ℂ; intro d
    rw [matchVal,matchVal,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      map_mul]
    change inner ℂ _ (S x _) = _
    have hz:ContinuousLinearMap.adjoint (S (star x))=S x:=by rw [map_star]; exact star_star _
    rw [←hz,ContinuousLinearMap.adjoint_inner_right,he _ (T.star_move _ h) d]; rfl -- maybe closed?
  apply T.mono_; ext1 c; rw [matchVal,matchVal,map_mul]; exact congrArg (fun a=> D.orthogonalProjectionOnto (S b a)) (he x h c)

def FixedPhase : Prop := ∀ w : (T.selected x).GNS, (∀ u ∈ T.steps, implement (T.selected x) u w=w) →
  ∃ c:ℂ,w=c • vector (T.selected x)
lemma fixed_Ω (u:B)(h:u∈T.steps) : implement (T.selected x) u (vector (T.selected x))=vector (T.selected x):= by
  let L:=T.selected x; change vectorForm L u= vector L
  apply (frequency L).eq_of_inner_right ℂ; intro i; rw [←vector_unit,form_is,form_is,mul_one]; unfold L; rw [selected_look,selected_look,(fixed_value T (star i) u h).2]
lemma unit_Ω : ‖vector (T.selected x)‖=1 := by
  let L:=T.selected x; let v:=vector L
  have hx : inner ℂ v v=1:= by unfold v; rw [←vector_unit,form_is,star_one,one_mul]; exact T.selected_one x
  have h:=congrArg Complex.re hx; change ‖v‖=1
  change RCLike.re (K:=ℂ) (inner ℂ v v)=1 at h; rw [inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v]

-- Allowed efforts to minimize measured joint invariant energy/momentum contribution
-- of the centered vector
noncomputable def effort := Submodule.span ℂ {f:B| ∃ x:B, x∈ T.steps ∧ ∃ d:B,f=x*d-d}
lemma unmarked (b : T.effort): T.mark b.val=0 := by
  rcases b with ⟨b,h⟩; dsimp; induction h using Submodule.span_induction with
  | mem x p=> obtain ⟨b,h,d,rfl⟩:=p; rw [map_sub,(T.fixed_value _ _ h).1,sub_self]
  | zero=> exact map_zero _
  | add _ _ _ _ a b=> rw [map_add,a,b,add_zero]
  | smul _ _ _ a=> rw [map_smul,a,smul_zero]

-- Test on phase and operator (X). Compress x-dependent *unselected*
-- centering b-M(b)Ω. Written as the actual element of A.
local notation "π"=>D.starProjection
local notation "Ψ"=>T.mark
abbrev off_square (b:B) := T.mark (star b*b) - star (T.mark b)*T.mark b
lemma price (b:B) : ‖S b (sω).val - π (S b (sω).val)‖^2 =
    (inner ℂ sω (t (T.off_square b) sω)).re := by
  let x:= S b (sω).val; let y:= π x; let v:= t (T.mark b) sω
  have hp : y=v.val:=by dsimp only [v]; rw [matchVal]; rfl
  have h := Submodule.starProjection_inner_eq_zero x y (D.starProjection_apply_mem _)
  unfold off_square; rw [map_sub,map_mul T.corner,map_star T.corner]
  change ‖x-y‖^2 = (inner ℂ sω (t _ sω-(t (T.mark b)).adjoint v)).re
  rw [inner_sub_right,Complex.sub_re, ← T.match_norm,ContinuousLinearMap.adjoint_inner_right]
  change _ = ‖x‖^2-(inner ℂ v v).re
  have hh(y:D): (inner ℂ y y).re=(inner ℂ y.val y.val).re:= rfl
  rw [hh,←hp,norm_sub_sq (𝕜:=ℂ),show RCLike.re (inner ℂ x y)= RCLike.re (inner ℂ y y) from congrArg _ (sub_eq_zero.mp (by rw [←inner_sub_left]; exact h)), show (inner ℂ y y).re=RCLike.re (inner ℂ y y) from rfl,inner_self_eq_norm_sq]; ring

lemma evaluate_price (b:B) : ‖vectorForm (T.selected x) b - T.selected x b • vector (T.selected x)‖^2 =
    (eye x (T.off_square b)).re := by
  let L:= T.selected x; let v:=vector L; let y:=vectorForm L b
  have h : ‖y‖^2=(L (star b*b)).re:=by rw [←form_is]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) y).symm
  have hv:inner ℂ v y = L b := read_is L b
  change ‖y-L b • v‖^2=_
  unfold off_square; rw [map_sub,map_mul (eye x),map_star (eye x),Complex.sub_re,←selected_look,←selected_look]; change _ = _-(starRingEnd ℂ (L b)*L b).re
  have hh: (L b * starRingEnd ℂ (L b)).re = ‖L b‖^2 := by rw [Complex.mul_conj]; rw [Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  rw [mul_comm (starRingEnd ℂ _), hh,norm_sub_sq (𝕜:=ℂ),h, inner_smul_right, ← inner_conj_symm y v,hv,norm_smul, T.unit_Ω, mul_one]
  change _ - 2 * (L b * starRingEnd ℂ (L b)).re + _ = _
  rw [hh]; ring

end Transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.price
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.evaluate_price
