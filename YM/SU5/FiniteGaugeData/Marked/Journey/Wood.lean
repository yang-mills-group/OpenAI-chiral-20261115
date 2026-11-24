import YM.SU5.FiniteGaugeData.Marked.Journey.Grants

/-!
# Cover-language calibration tied to the elected construction, for one
presentation of the direct resolution results using the very same Family etc
language. The `takes` field is irrelevant for these direct results (notably
the course has no requirement of even period parameters). This is NOT any
claim to constructing a `Conveyor`, paying a `Printed`, matching trajectories
or closing that other assignment's schedule obligations. All Histories uses
of those belong to the W-conditioned integration; this merely binds the terms
needed to refer to the inserted marks on the same signed frames over
`cell M Λ.block Λ.R.L 0`, whatever M (to be read at j observing with M =
the original `mesh ... j`; coherent shift of period label, does not touch
observable's cover spacing or words).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation

private lemma sides (q:Side) (n:ℕ):∃ m:Side, oddMultiple m q ∧ ∀ s:Side, oddMultiple s q→ s.val ≤ n→ oddMultiple m s:=by
  let P:Finset Side:=(((Iic n).image (fun x:ℕ=> (⟨x+1,by omega⟩:Side))).filter fun i:Side=>Odd i.val)
  let s:Side:= P.prod id
  have h(A:Finset Side)(p:A⊆P):Odd (A.prod id:Side).val:=by
    induction A using Finset.induction_on with
    | empty=>simpa using (odd_one (α:=ℕ))
    | @insert i A u ih=>
      rw [prod_insert u]
      exact Odd.mul ((mem_filter.mp (p (mem_insert_self ..))).2) (ih fun k v=> p (mem_insert_of_mem v))
  refine ⟨q*s,⟨s,h _ subset_rfl,rfl⟩,?_⟩
  rintro _ ⟨t,e,rfl⟩ v
  change q.val*t.val ≤ _ at v
  have hp:t∈ P:= mem_filter.mpr ⟨mem_image.mpr (by
    have hk:t.val-1+1=t.val:= Nat.sub_add_cancel (show 1≤t.val from t.property)
    exact ⟨t.val-1,mem_Iic.mpr ((Nat.sub_le _ _).trans ((Nat.le_mul_of_pos_left _ q.property).trans v)),Subtype.ext hk⟩),e⟩
  refine ⟨_,h _ (erase_subset t P),?_⟩
  rw [mul_assoc,show t * (∏ a∈P.erase t,id a)= s from mul_prod_erase P id hp]

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
private def widen:Side:=⟨Y.meter.q+Λ.J.h+61,by omega⟩
def alterations:Side:=Λ.M*((2:Side)*widen Y)
local notation "B₀"=> Λ.block
local notation "r"=> reserve Λ l
def inflect (Λ:Preparation)(l:ℕ):ℕ:=2*Λ.block.val*(reserve Λ l)+1
include Y
private lemma position: 2*(reserve Λ l) ≤ 4*(B₀).val*(inflect Λ l/(2*(B₀).val)):=by
  have he:0<(B₀).val:=(B₀).property
  apply le_trans _ (Nat.mul_le_mul_left (4*(B₀).val)
    ((Nat.le_div_iff_mul_le (x:=r) (y:=inflect Λ l) (mul_pos two_pos he)).mpr ?_))
  · exact Nat.mul_le_mul_right _ (by omega)
  unfold inflect; nlinarith
private lemma panel {m:Side}(a:oddMultiple m (alterations Y)) :
    (∃ s:Side,m=s*Λ.M ∧ Λ.J.h ≤ s.val) ∧ Y.meter.q ≤ m.val ∧ 61 ≤ m.val:=by
  obtain ⟨k,P,b⟩:=a
  let s:= (2:Side)*widen Y*k
  have he:m=s*Λ.M:= b.trans (by unfold alterations s; ac_rfl)
  have hp:(widen Y).val ≤ s.val:= by
    change _ ≤ (2:ℕ)*_ * k.val; exact (Nat.le_mul_of_pos_left _ two_pos).trans (Nat.le_mul_of_pos_right _ k.property)
  have hM:(widen Y).val ≤ m.val:=hp.trans ((Nat.le_mul_of_pos_right _ Λ.M.property).trans_eq (congrArg (fun x:Side=> x.val) he.symm))
  change Y.meter.q+Λ.J.h+61 ≤ _ at hp hM
  exact ⟨⟨s,he,by omega⟩,by omega,by omega⟩

/-- For the presentation without an upfront `Printed`; just on the election
above the corollary base cutoff. -/
def tent : Calibration where
  K:= Λ.K
  R:= Λ.R
  rJ:=Λ.rJ
  L:=Λ.L
  V:=Λ.V
  clip:=Λ.direct
  b₀:=Λ.b
  b_pos:=Λ.bp
  B:=B₀
  shape:=rfl
  e:=Λ.d
  P:=Λ.U
  W:=Λ.W
  M':=Λ.M
  J:=Λ.J
  η:= Chi.canonical
  x:=Λ.x
  a:=1
  p:=2
  i:=6
  N0:=Λ.N0
  base:=h
  T:=Y.meter
  h:=Λ.h
  positive_h:=Λ.height
  R0:=Λ.R0
  δ:=Λ.δ
  D:=aliasLaw Λ
  w:=distanceLaw l
  ℓ:=reserve Λ l
  legal:=legal Λ
  buffer:= by exact prepared Λ l
  vertex:=inflect Λ l
  positiveR:=Nat.le_add_left ..
  line:=position Y
  q:=alterations Y
  big:= (panel Y (show oddMultiple (alterations Y) _ from ⟨1,odd_one,(mul_one _).symm⟩)).2.2
  q_even:= (show Even (Λ.M.val*(2*(widen Y).val)) from (Even.mul_left ((even_two (α:=ℕ)).mul_right _) _))
  roofSize:=fun _ a=> (panel Y a).1
  monthSize:=fun _ a=> (panel Y a).2.1
  listTop:=fun i=> (sides (alterations Y) i).choose
  sides:= Eventually.of_forall fun i=> (sides (alterations Y) i).choose_spec

lemma terrain (m:Side)(j:ℕ): (tent Y h).c (mesh m Λ.R.L j)= Λ.Ctor m j:=by unfold Calibration.c Preparation.Ctor cell mesh; rw [pow_zero,mul_one]; rfl
end YM.CF.Buffered.Afterglow.Journey
