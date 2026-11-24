import YM.SU5.Intrinsic.Coil.Merger
import YM.CF.Sour.Millet

/- Credit Sour/Penny for mask projection and matrix economy; use actual
  $Y^*>$ kernels from all input programs and Buster beam, as linear maps
  on WHOLE belt. Note Sector b=false here; actual Marks even.
  In polar-gap applications need not use on arguments not in Cipher. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side}
variable (A: FC (Dwell n)) {X:Finset (Seat n)}
variable (p:Fock.Sector (camp X) false A)

def assignM (A: FC (Dwell n))(p:Fock.Sector (camp (n:=n) X) false A): Cipher n →ₗ[ℂ] Cipher n where
 toFun e := ⟨Sault.rind (A*e.val),light_e ((lift_v p (subset_univ _)).mul (life (fineShape e)))⟩
 map_add' x y := Subtype.ext (by change Sault.rind (A*(x.val+y.val))=_; rw [mul_add]; exact map_add (cane _).eval ..)
 map_smul' i x := Subtype.ext (by change Sault.rind (A*(i • x.val))= i • Sault.rind _; rw [Matrix.mul_smul]; exact map_smul (cane _).eval ..)
-- label-linear projection of economic carrier
include p
lemma near_assign(X':Finset (Seat n))(e:Cipher n)(h:X ⊆ X')(q:Flour (camp X') e.val): Flour (camp X') (assignM A p e).val:= light_e ((lift_v p (fun i u=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp u).2⟩)).mul (life q))
lemma far_assign(X':Finset (Seat n))(e f:Cipher n)(h:Disjoint X X')(q:Flour (camp X') f.val): assignM A p (e*f)= assignM A p e*f:=by
 rw [mul_comm e f,mul_comm _ f]; apply Subtype.ext; exact pert p q (Finset.disjoint_left.mpr (fun i u t=> Finset.disjoint_left.mp h ((mem_filter.mp u).2) ((mem_filter.mp t).2))) _
omit p

/- Glyph_X borne here. -/
variable (B: Chart I (Seat n)) (δ:ℕ) (P:BudgetPoint)(H:ℝ)
local notation "Ω"=>Seat n
local notation "Υ"=> Support (More n)
local notation "𝒞"=>Firing n
local notation "Λ"=> Orbit n
namespace Chart

def ridge (B:Chart I (Seat n))(i:I):Vow.Aura n:=⟨B.space i, B.anchor i,B.here i⟩
local notation "mast" i:max=> ridge B i
structure Stoke (V : I→ Firing n)(a:I→ℝ):Prop where
 rate:0≤a
 grain(i:I)(x:Orbit n): Fock.Sector (camp (B.space i)) false (V i x)
 verge(i:I)(X:Vow.Aura n)(D:Support (More n))(hx:B.space i⊆ X.val)(d:D⊆X.val)(u:halo δ D ⊆ X.val): Marque P X (ridge B i) D (V i) H (a i)
 roof(i:I)(X:Vow.Aura n)(V':Pane n)(y u : Ids n):B.space i ⊆ X.val →V'∈σX P X ∅ → V i (V',y)=V i (V',u)
-- Slight overpricing vise. smul in actor NOT scalar z here, will do polynomial to
-- keep definite translations and duplicate-free monitor.
namespace Stoke
variable {B P H δ}{a:I→ℝ}{V:I→ Firing n}(C:B.Stoke δ P H V a)
def gives (T:Orbit n)(i:I) : Cipher n →ₗ[ℂ] Cipher n:=assignM (V i T) (C.grain i T)
include C
lemma modest (v:Orbit n): B.Mild (C.gives v):=⟨fun i _ x h=>near_assign _ (C.grain i v) _ _ h,fun i _ e f h=>far_assign _ (C.grain i v) _ _ _ h⟩
-- Applicator valid for all h via its Marque, economics with inputs charged
-- INCLUDING flags. Use at final footprint chosen. 
variable (S: Aura n)(D: Support (More n))(b:D⊆ S.val) (hσ:halo δ D ⊆ S.val)
def housing (i:I)(hx:B.space i⊆S.val)(F:Copy n):Copy n:= (C.verge i S D hx b hσ).toCrate.motion F
lemma housing_toll (h:0≤ H)(u:3 ≤ P.B)(i:I)(hx:B.space i⊆S.val)(F:Copy n)(c:ℝ)(p:Fray P H δ S D F c) : Fray P H δ S D (C.housing S D b hσ i hx F) (a i*c):= Marque.book (C.verge i S D hx b hσ) p u hx h (C.rate i)
lemma houses (i:I)(hx:B.space i⊆S.val)(F:Copy n)(V':Orbit n)(q: V'.1∈σX P S D): C.housing S D b hσ i hx F V'= C.gives V' i (F V'):=by
 apply Subtype.ext; change Sault.rind (coll_T P S D (V i) _*_)=_; rw [ (C.verge i S D hx b hσ).toCrate.pointV V' q]; rfl
lemma houseVoid (i:I)(hx:B.space i⊆S.val)(F:Copy n)(V':Orbit n)(τ:Ids n)
 (q:F V'=F (V'.1,τ))(s:D=∅) : C.housing S D b hσ i hx F V'= C.housing S D b hσ i hx F (V'.1,τ):=by
 subst s
 apply Subtype.ext; let v:= V'.1; have ht: coll_T P S ∅ (V i) V'= coll_T P S ∅ (V i) (v,τ):=by
    unfold coll_T; change (if Rue.Gates (σX P S ∅) S.val v then _ else _)=(if Rue.Gates (σX P S ∅) S.val v then _ else _); split
    next h=> exact C.roof i S _ _ _ hx ((Rue.pillar S.val (Rue.open_l P.threshold S.val ∅)).choose_spec.2 _ |>.2 h)
    rfl
 change Sault.rind (coll_T P S ∅ (V i) V'*(F V').val)= Sault.rind (coll_T P S ∅ (V i) (v,τ)*(F (v,τ)).val); rw [ht,q]

end Stoke
end Chart
end YM.CF.Coil
open YM.CF.Coil
#print axioms assignM
#print axioms Chart.Stoke.houseVoid
