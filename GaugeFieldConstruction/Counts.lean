import GaugeFieldConstruction.MixedWeights

/-!
# Counts for all three generations and the actual Color norm
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Matter
open CF Function Set Matrix Finset
open scoped Topology Matrix Matrix.Norms.Frobenius Kronecker BigOperators InnerProductSpace
abbrev Generation := Fin 3
abbrev Link := Generation × Generation
abbrev FlavorIndex := Bool × Link  -- true Ten

def bra : Generation → Generation → Op Slot →ₗ[ℂ] U := fun i j => {
  toFun := fun A => Matrix.of (fun x y => A (i,x) (j,y))
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
}
abbrev ma (u : E) := (SU.matter u).val
lemma ma_left (u : E) (A : Op Slot) (i j) : bra i j (ma u*A)=blockRep u*bra i j A := by
  ext x y; simp [ma,bra,Matrix.mul_apply, SU.Slot, Fintype.sum_prod_type,SU.triple,blockRep,Matrix.one_apply]
lemma ma_right (u : E) (A : Op Slot) (i j): bra i j (A*ma u)=bra i j A*blockRep u := by
  ext x y; simp [ma,bra,Matrix.mul_apply, SU.Slot, Fintype.sum_prod_type,SU.triple,blockRep,Matrix.one_apply,ite_mul]

def coeffs (p : FlavorIndex → ℂ) : Op Slot := Matrix.of fun i j=>
  two (p (true,i.1,j.1)) (p (false,i.1,j.1)) i.2 j.2
def costing (p : FlavorIndex → ℂ) : C →ₗ[ℝ] Op Slot where
  toFun a:= Matrix.of fun i j=> tint (p (true,i.1,j.1)) (p (false,i.1,j.1)) a i.2 j.2
  map_add' a b := by ext i j; simp
  map_smul' t a := by ext i j; simp
lemma block_ext {A B : Op Slot} (h : ∀ i j,bra i j A=bra i j B) : A=B := Matrix.ext fun ⟨x,i⟩ ⟨y,j⟩ => Matrix.ext_iff.mpr (h x y) i j

def neutral (A : Op Slot) : Prop := ∀ u, ma u*A=A*ma u
def neutral_c (A : C→ₗ[ℝ]Op Slot) : Prop := ∀ u x, ma u*A x=A (adj u x)*ma u
lemma pint (x y : Generation) (p : FlavorIndex → ℂ) : bra x y (coeffs p)=two (p (true,x,y)) (p (false,x,y)) := rfl
lemma pint_c (x y : Generation) (p : FlavorIndex → ℂ) (a) : bra x y (costing p a)=tint (p (true,x,y)) (p (false,x,y)) a := rfl

lemma coeff_ok (p) : neutral (coeffs p) := fun i => block_ext (fun x y => by
  rw [ma_left,ma_right,pint]; exact (pure_singular _).mpr ⟨_,_,rfl⟩ i)
lemma cost_ok (p) : neutral_c (costing p) := fun i a=> block_ext (fun x y => by rw [ma_left,ma_right,pint_c,pint_c]; exact tints _ _ _ _)
lemma two_diag (x y : ℂ) : two x y (Sum.inl start) (Sum.inl start)=x ∧ two x y e₀ e₀=y := by simp [two,Join.both,e₀]
lemma co_earn : Injective coeffs := by
  intro a b h
  have H i j := congr_arg (bra i j) h
  funext ⟨s,x,y⟩; have eq:=H x y; rw [pint,pint] at eq
  cases s; rw [← (two_diag (a (true,x,y)) (a (false,x,y))).2,eq,(two_diag ..).2]
  rw [← (two_diag (a (true,x,y)) (a (false,x,y))).1,eq,(two_diag ..).1]
lemma cost_earn : Injective costing := by
  intro a b h
  funext i
  obtain ⟨s,x,y⟩:=i
  have e : tint (a (true,x,y)) (a (false,x,y))=tint (b (true,x,y)) (b (false,x,y)) := by
    ext1 r; rw [← pint_c,← pint_c,h]
  cases s; exact (tint_faith e).2; exact (tint_faith e).1

theorem species (W : Op Slot) : neutral W ↔ ∃! p:FlavorIndex→ℂ,W=coeffs p := by
  constructor; swap
  · rintro ⟨p,rfl,H⟩; exact coeff_ok _
  intro h
  have ht (i j) : pure (bra i j W) := fun u => by rw [←ma_left,←ma_right,h u]
  choose a b H using (fun i j=> (pure_singular _).mp (ht i j))
  let p : FlavorIndex → ℂ := fun i=> if i.1 then a i.2.1 i.2.2 else b i.2.1 i.2.2
  have hr : W=coeffs p:=block_ext (fun i j=> by rw [pint]; exact H i j)
  exact ⟨p,hr, fun i v=> co_earn (Eq.trans (Eq.symm v) hr)⟩

theorem species_c (W : C→ₗ[ℝ]Op Slot) : neutral_c W ↔ ∃! p:FlavorIndex→ℂ,W=costing p := by
  constructor; swap
  · rintro ⟨p,rfl,H⟩; exact cost_ok _
  intro h
  let A (i j:Generation) := LinearMap.comp ((bra i j).restrictScalars ℝ) W
  have ht (i j) : action (A i j) := by intro u x; change _*bra i j (W x)=bra i j (W (adj u x))*_ ; rw [← ma_left,←ma_right,h u x]
  choose a b H using fun i j=> (tinted _).mp (ht i j)
  let p : FlavorIndex → ℂ := fun i=> if i.1 then a i.2.1 i.2.2 else b i.2.1 i.2.2
  have hr : W=costing p := LinearMap.ext fun r=> block_ext fun i j=> by rw [pint_c]; exact DFunLike.congr_fun (H i j) r
  exact ⟨p,hr,fun i v=> cost_earn (Eq.trans (Eq.symm v) hr)⟩

theorem real_price (x y : C) : -Matrix.trace (H x * H y) = (5:ℂ) * ↑(inner ℝ x y) := by
  apply Complex.ext
  · have hp:=G.trace_color x y; rw [show (G.repDim:ℝ)=5 from by rw [show G.repDim=5 from rfl]; norm_num] at hp -- dependent?
    simp
    exact hp
  have h := G.trace_color_real x y
  simp
  exact h
theorem color_form (B : C →ₗ[ℝ] C →ₗ[ℝ] ℂ) (h : ∀ u x y,B (adj u x) (adj u y)=B x y) :
    ∃ c:ℂ,∀ x y, B x y=c * ↑(inner ℝ x y) := YM.Push.Loops.scalar_complex CF.Thera.yet_one B h
end YM.GaugeFieldConstruction.Matter
