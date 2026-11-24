import SatinStress.Internal.Root
/-!
# Matrix Slot costs for three generations

Color input = SU.group.Color (true project), representation = `SU.matter`, Spin
suppressed. For Mixed, `Mixed T` asks for equivariance on the **real** color
space with complex coefficients allowed for T. Equivalently one may extend complex
linearly in the Color input. Use `scheme` for a block, evaluated on the embedded
Color: on real C (unit coefficients both) it's U1's $T$ of that sector, the
actual infinitesimal `sheetD`. The subclaims also give uniqueness over the
complex parameter space, prior to any centroid or Flavor covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open Gauge SU Function Matrix Finset
open scoped Matrix Kronecker Topology BigOperators
open Complex (I)

def selected (a b : ℂ) : Col →ₗ[ℝ] SheetEnd := ((scheme a b).restrictScalars ℝ).comp embedC
lemma selected_at (a b) (x : Col) : selected a b x = scheme a b (embedC x) := rfl
lemma selected_generator (x : Col) : selected 1 1 x=sheetD (embedC x) := real_generator (embedC_mem x)

def Focus (t : Col →ₗ[ℝ] SheetEnd) : Prop :=
  ∀ x (g : E), t (SU.group.adjoint g x) * mat g = mat g * t x
lemma selected_focus (a b) : Focus (selected a b) := by
  intro x g; rw [selected_at,moved,selected_at]; exact sector_scheme a b g (embedC x) (trace_clear x)

-- identification of actual real generators, not requiring the real proof argument to use all
-- of complexified ones.
lemma extension_price (f : Fund →ₗ[ℂ] SheetEnd) {X : Fund} (h : trace X=0) :
    extend ((f.restrictScalars ℝ).comp embedC) X=f X := by
  unfold extend; simp only [LinearMap.coe_mk,AddHom.coe_mk, plain_self h, spread, LinearMap.comp_apply, LinearMap.coe_restrictScalars,embedC_project_self (axis1_mem h),embedC_project_self (axis2_mem h)]
  rw [← map_smul,← map_add,two_axes]
lemma focus_selected {t : Col →ₗ[ℝ] SheetEnd} (h : Focus t) :
    let x := extend t (element 0 4)
    t = selected (-x (poleTop 1) (poleBot 1)) (-x (.inr 4) (.inr 0)) := by
  intro x
  have ht : AdjS (extend t) := by
    intro g A _; apply commute_to (firstU _); exact extend_carries t (fun x g => commute_from (firstU g) (h x g)) g A
  ext1 i; rw [selected_at,← extend_starts t i]; exact follows _ ht _ _ (neg_neg _).symm (neg_neg _).symm (trace_clear _)
lemma locate {a b c d : ℂ} (h : selected a b = selected c d) : a=c ∧ b=d := by
  have he := LinearMap.congr_fun (congr_arg extend h) (element 0 4)
  unfold selected at he
  simp only [extension_price _ (rooted_zero (show (0:F)≠4 by decide))] at he
  exact ⟨neg_inj.mp (((coefficients a b).1.symm.trans (Matrix.ext_iff.mpr he _ _)).trans (coefficients c d).1),
    neg_inj.mp (((coefficients a b).2.symm.trans (Matrix.ext_iff.mpr he _ _)).trans (coefficients c d).2)⟩
lemma locate_id {a b c d : ℂ} (h : sheetId a b = sheetId c d) : a=c ∧ b=d := by
  constructor
  · simpa [sheetId,Join.both] using Matrix.ext_iff.mpr h (.inl origin) (.inl origin)
  simpa [sheetId,Join.both] using Matrix.ext_iff.mpr h (.inr 0) (.inr 0)
lemma focus_iff (t : Col →ₗ[ℝ] SheetEnd) : Focus t ↔ ∃ a b, t = selected a b := by
  refine ⟨fun h => ⟨_,_,focus_selected h⟩,?_⟩
  rintro ⟨a,b,rfl⟩; exact selected_focus a b
@[simp] lemma selected_zero : selected 0 0=0 := by ext1 c; change scheme 0 0 _ = 0; simp [scheme,Join.both]
@[simp] lemma sheetId_zero : sheetId 0 0=0 := by simp [sheetId,Join.both]

abbrev Piece := Op Slot
abbrev Age := Fin 3

def part (g h : Age) : Piece →ₗ[ℂ] SheetEnd :=
 { toFun x := x.submatrix (g,·) (h,·)
   map_add' _ _ := rfl
   map_smul' _ _ := rfl }
@[simp] lemma part_at (T g h i j) : part g h T i j = T (g,i) (h,j) := rfl
lemma parts_ext {A B : Piece} (h : ∀ g u, part g u A=part g u B) : A=B := by
  apply Matrix.ext; rintro ⟨i,j⟩ ⟨a,b⟩; exact Matrix.ext_iff.mpr (h i a) j b

def all (f : Age → Age → SheetEnd) : Piece := Matrix.of fun x y => f x.1 y.1 x.2 y.2
@[simp] lemma part_all (f) (i j) : part i j (all f)=f i j := rfl

lemma part_one (i j : Age) : part i j 1 = (1:Op Age) i j • 1 := by
  apply Matrix.ext; intro x y; by_cases t:i=j <;> simp [one_apply,t]
lemma part_tensor (p : Op Age) (q : SheetEnd) (i j : Age) : part i j (p⊗ₖq) = p i j • q := by apply Matrix.ext; intro x y; rfl
lemma part_mul (f g : Piece) (i j : Age) : part i j (f*g)=∑ k, part i k f * part k j g := by
  apply Matrix.ext; intro x y; simp [mul_apply, Matrix.sum_apply, Slot,Fintype.sum_prod_type]
lemma part_left (f : Piece) (p : SheetEnd) (i j : Age) : part i j (((1:Op Age)⊗ₖp)*f) = p*part i j f := by
  rw [part_mul, Finset.sum_eq_single i (fun b _ t => by rw [part_tensor,one_apply_ne (Ne.symm t),zero_smul,zero_mul]) (by simp),part_tensor,one_apply_eq,one_smul]
lemma part_right (f : Piece) (p : SheetEnd) (i j : Age) : part i j (f*((1:Op Age)⊗ₖp)) = part i j f*p := by
  rw [part_mul, Finset.sum_eq_single j (fun b _ t => by rw [part_tensor,one_apply_ne t,zero_smul,mul_zero]) (by simp),part_tensor,one_apply_eq,one_smul]

def Pure (T : Piece) := ∀ u : E, (matter u).val * T = T * (matter u).val
def pool (a b : Op Age) : Piece := all (fun g h => sheetId (a g h) (b g h))
lemma pure_iff (T : Piece) : Pure T ↔ ∀ a b, FixedS (part a b T) := by
  constructor
  · intro h a b u; unfold holds; rw [← part_left,← part_right]; exact congr_arg (part a b) (h u)
  intro h u; apply parts_ext; intro a b; change part a b (( (1:Op Age)⊗ₖmat u)*T)=part a b (T*((1:Op Age)⊗ₖmat u)); rw [part_left,part_right]; exact h a b u
lemma pure_pool (a b) : Pure (pool a b) := (pure_iff _).mpr (fun i j => sheetId_fixed (a i j) (b i j))
lemma pool_injective {a b c d} (h : pool a b=pool c d) : a=c ∧ b=d := by
  have he(i j: Age) : a i j=c i j ∧ b i j=d i j:= locate_id (congr_arg (part i j) h)
  exact ⟨Matrix.ext (fun _ _=> (he _ _).1),Matrix.ext (fun _ _=> (he _ _).2)⟩
theorem purity (T : Piece) : Pure T ↔ ∃ a b, T=pool a b := by
  classical
  constructor
  · intro h; choose A B he using (fun i j => (fixed_iff _).mp (((pure_iff _).mp h) i j))
    exact ⟨Matrix.of A, Matrix.of B,parts_ext he⟩
  rintro ⟨a,b,rfl⟩; exact pure_pool a b

def sectionOf (T : Col →ₗ[ℝ] Piece) (i j : Age) := ((part i j).restrictScalars ℝ).comp T
def Mixed (T : Col →ₗ[ℝ] Piece) := ∀ x (u : E), T (group.adjoint u x)*(matter u).val = (matter u).val * T x
def ocean (a b : Op Age) : Col →ₗ[ℝ] Piece where
  toFun x := all fun i j => selected (a i j) (b i j) x
  map_add' _ _ := parts_ext (by simp)
  map_smul' _ _ := parts_ext (by intro i j; have ht(x:ℝ)(z:Piece) : part i j (x • z)= x • part i j z := map_smul ((part i j).restrictScalars ℝ) x _; simp [ht])
@[simp] lemma section_price (T : Col →ₗ[ℝ] Piece) (i j : Age) (x : Col) : sectionOf T i j x = part i j (T x) := rfl
@[simp] lemma section_ocean (a b : Op Age) (i j) : sectionOf (ocean a b) i j=selected (a i j) (b i j) := by ext1; simp [ocean]

lemma mixed_iff (T : Col →ₗ[ℝ] Piece) : Mixed T ↔ ∀ a b, Focus (sectionOf T a b) := by
  constructor
  · intro h a b x u; rw [section_price,section_price,← part_left,← part_right]; exact congr_arg (part a b) (h x u)
  intro h x u; apply parts_ext; intro a b; change part a b ( _*((1: Op Age)⊗ₖmat u))=part a b (((1:Op Age)⊗ₖmat u)*_); rw [part_left,part_right]; exact h a b x u
lemma ocean_mixed (a b) : Mixed (ocean a b) := (mixed_iff _).mpr (by intro i j; rw [section_ocean]; exact selected_focus _ _)
lemma ocean_injective {a b c d : Op Age} (h : ocean a b = ocean c d) : a=c ∧ b=d := by
  have he i j : a i j=c i j ∧ b i j=d i j := locate (by rw [← section_ocean,← section_ocean,h])
  exact ⟨Matrix.ext (fun _ _ => (he _ _).1), Matrix.ext (fun _ _ => (he _ _).2)⟩
theorem mixed_pool (T : Col →ₗ[ℝ] Piece) : Mixed T ↔ ∃ a b, T=ocean a b := by
  constructor
  · intro h; choose A B he using (fun i j => (focus_iff _).mp (((mixed_iff _).mp h) i j))
    refine ⟨Matrix.of A, Matrix.of B,?_⟩; ext1 x; apply parts_ext; intro i j
    exact LinearMap.congr_fun (he i j) x
  rintro ⟨a,b,rfl⟩; exact ocean_mixed a b
end YM.CF.SatinStressData
