import SatinStress.Internal.Turntable
/-!
# Exact flavor-invariant PH and Mixed Slot ranks

This is a bridge for the *class inputs* to U1 with the given matter definitions.
Constant gauge here (Color actually the project's tangent space), suppress the Spin and spacetime
indices; before imposing any null polynomial equations. The classification for the full Slot
basis (including all three generations of each species) and flavor condition.
This does not, for example, assert that R4 with this flavor group obtains *on the chosen P*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open SU Gauge Matrix Finset Function
open Complex (I)
open scoped Matrix Kronecker Topology BigOperators

-- Algebra with **independent matrices** on generations, one for each species.
lemma id_add (a b u v:ℂ) : sheetId (a+u) (b+v) = sheetId a b + sheetId u v := by
  simp only [sheetId, Join.both, fromBlocks_add, add_smul, add_zero]; -- direction?
lemma id_scaled (a b u:ℂ) : sheetId (u*a) (u*b)=u • sheetId a b := by unfold sheetId Join.both; simp [fromBlocks_smul, mul_smul]
lemma id_times (a b u v:ℂ) : sheetId (a*u) (b*v)=sheetId a b * sheetId u v := by unfold sheetId; rw [Join.both_mul]; simp [mul_smul,smul_comm a u,smul_comm b v]
lemma adj_add (a b u v : ℂ)(x) : selected (a+u) (b+v) x=selected a b x + selected u v x := by
  simp [selected_at,scheme, Join.both, Matrix.fromBlocks_add,add_smul]
lemma adj_scaled (a b u:ℂ)(x) : selected (u*a) (u*b) x=u • selected a b x := by
  simp [selected_at,scheme, Join.both, Matrix.fromBlocks_smul,mul_smul]
lemma adj_times (a b u v:ℂ)(x) : sheetId a b * selected u v x=selected (a*u) (b*v) x := by
  simp [sheetId,selected_at,scheme, Join.both_mul, mul_smul,smul_comm a u,smul_comm b v]
lemma times_adj (a b u v:ℂ)(x) : selected u v x * sheetId a b=selected (u*a) (v*b) x := by
  simp [sheetId,selected_at,scheme, Join.both_mul, mul_smul,smul_comm a u,smul_comm b v]
lemma id_star (a b:ℂ) : sheetId (star a) (star b)=star (sheetId a b) := by
  simp only [sheetId,Join.star_both,star_smul,star_one]
lemma id_cc (a b : ℂ) : cc (sheetId a b)=sheetId (star a) (star b) := by
  apply Matrix.ext; rintro (x|x) (y|y) <;> simp [sheetId,Join.both, Matrix.one_apply,apply_ite (star:ℂ→ℂ)]

lemma pool_one : pool 1 1=1 := by apply parts_ext; intro i j; by_cases t:i=j <;> simp [pool,sheetId,part_one,t,one_apply,Join.both]
lemma pool_add (a b u v:Op Age) : pool (a+u) (b+v)=pool a b + pool u v := by apply parts_ext; intro i j; simp [pool,id_add]
lemma pool_smul (a b : Op Age) (v:ℂ) : pool (v • a) (v • b)=v • pool a b := by apply parts_ext; intro i j; simp [pool,id_scaled]
lemma ocean_add (a b u v:Op Age) : ocean (a+u) (b+v)=ocean a b + ocean u v := by
  apply LinearMap.ext; intro x; apply parts_ext; intro i j; simp [ocean,adj_add]
lemma ocean_smul (a b:Op Age) (v:ℂ) : ocean (v • a) (v • b)=v • ocean a b := by
  apply LinearMap.ext; intro x; apply parts_ext; intro i j; simp [ocean,adj_scaled]

private lemma age (x y : Age → ℂ) : sheetId (∑ i, x i) (∑ i, y i) = ∑ i, sheetId (x i) (y i) := by simp [Age,Fin.sum_univ_succ,id_add]
private lemma total_adj (x y : Age → ℂ) (p) : selected (∑ i, x i) (∑ i, y i) p=∑ i, selected (x i) (y i) p := by simp [Age,Fin.sum_univ_succ,adj_add]

lemma pool_mul (a b u v:Op Age) : pool (a*u) (b*v)=pool a b * pool u v := by
  apply parts_ext; intro i j; rw [part_mul]; simp only [pool,part_all,mul_apply,age,id_times]; -- maybe simp mul recursion
lemma ocean_times (a b u v:Op Age) (p) : ocean (a*u) (b*v) p = ocean a b p * pool u v := by
  apply parts_ext; intro i j; rw [part_mul]; simp only [pool,ocean,LinearMap.coe_mk,AddHom.coe_mk,part_all,mul_apply,total_adj,times_adj]
lemma times_ocean (a b u v:Op Age) (p) : ocean (a*u) (b*v) p = pool a b * ocean u v p := by
  apply parts_ext; intro i j; rw [part_mul]; simp only [pool,ocean,LinearMap.coe_mk,AddHom.coe_mk,part_all,mul_apply,total_adj,adj_times]
lemma pool_star (a b: Op Age) : pool (star a) (star b)=star (pool a b) := by
  apply parts_ext; intro i j; change sheetId (star (a j i)) (star (b j i)) = star (sheetId (a j i) (b j i)); exact id_star ..
lemma pool_cc (a b : Op Age) : cc (pool a b)=pool (cc a) (cc b) := by
  apply parts_ext; intro i j; change cc (sheetId (a i j) (b i j)) = sheetId (star (a i j)) (star (b i j)); exact id_cc ..

open Menu (Pos Proper pose)
abbrev Flavor := Pos × Pos
instance : Fintype Menu.Pos := Fintype.ofFinite _
example : Fintype Flavor := by infer_instance
abbrev turn (q : Flavor) := pool (pose q.1.val) (pose q.2.val)

@[simp] lemma turn_mul (q r : Flavor) : turn (q*r)=turn q*turn r := by unfold turn; simp [pool_mul]
@[simp] lemma turn_cc (q : Flavor) : cc (turn q)=turn q := by simp [turn,pool_cc]
@[simp] lemma turn_one : turn 1=1 := by change pool (pose 1) (pose 1)=_; rw [Menu.posed_one,pool_one]
lemma turn_star (q : Flavor) : star (turn q)=turn q⁻¹ := by rw [turn, ← pool_star, Menu.star_pose,Menu.star_pose]; rfl
lemma unit_turn (q : Flavor) : turn q∈unitary Piece := by constructor <;> rw [turn_star, ← turn_mul] <;> simp
lemma turn_pure (q : Flavor) : Pure (turn q) := pure_pool _ _

-- PH and Mixed flavor invariance
-- trace & complex phase to be checked further on MOMENTUM kernel; this statement only internal index.
def FixedFlavor (T : Piece) := ∀ g : Flavor, T * turn g = turn g * T
lemma shapeP {T : Piece} (h : Pure T) (f : FixedFlavor T) : ∃ x y : ℂ, T=pool (x • 1) (y • 1) := by
  obtain ⟨a,b,rfl⟩ := (purity T).mp h
  have e (m : Pos) : a*pose m.val=pose m.val * a ∧ b * pose m.val=pose m.val * b := by
    have he := f ((m,m):Flavor); unfold turn at he; rw [← pool_mul,← pool_mul] at he
    exact pool_injective he
  exact ⟨a 0 0,b 0 0,congr_arg₂ pool (Menu.proper_commuting a (fun m => (e m).1)) (Menu.proper_commuting b (fun m => (e m).2))⟩
lemma shapeM {T : Col →ₗ[ℝ] Piece} (h : Mixed T) (f : ∀ i, FixedFlavor (T i)) : ∃ x y : ℂ, T=ocean (x • 1) (y • 1) := by
  obtain ⟨a,b,rfl⟩ := (mixed_pool T).mp h
  have e (m : Pos) : a*pose m.val=pose m.val * a ∧ b * pose m.val=pose m.val * b := by
    apply ocean_injective; ext1 i; rw [ocean_times,times_ocean]; exact f i (m,m)
  exact ⟨a 0 0,b 0 0,congr_arg₂ ocean (Menu.proper_commuting a (fun m => (e m).1)) (Menu.proper_commuting b (fun m => (e m).2))⟩

lemma invariantP (T : Piece) : Pure T ∧ FixedFlavor T ↔ ∃ x y : ℂ, T=pool (x • 1) (y • 1) := by
  refine ⟨fun h=> shapeP h.1 h.2,?_⟩
  rintro ⟨x,y,rfl⟩; refine ⟨pure_pool _ _, fun g => ?_⟩; unfold turn; rw [← pool_mul,← pool_mul]; simp
lemma invariantM (T : Col →ₗ[ℝ] Piece) : Mixed T ∧ (∀ i, FixedFlavor (T i)) ↔ ∃ x y : ℂ, T=ocean (x • 1) (y • 1) := by
  refine ⟨fun h => shapeM h.1 h.2, ?_⟩
  rintro ⟨x,y,rfl⟩; refine ⟨ocean_mixed _ _, fun i g => ?_⟩; unfold turn; rw [← times_ocean,← ocean_times]; simp
end YM.CF.SatinStressData
