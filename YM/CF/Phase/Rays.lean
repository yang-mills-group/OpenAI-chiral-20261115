import YM.CF.Phase.Root

/-!
# Discrete log transport on a prism simplex

Use complex rather than radial logarithm already now, for locality. The
integers in the transport are fixed by a continuous lift over the simplex.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Finset
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def rad (m B : Side) (c : Part m B) (U : Skin m B) (s : ArrayF m) (x y : Sq) (j : ℕ) :=
  spark (lens m B c U) (bow m B U s (increment B j x y)) (bow m B U s (increment B (j+1) x y))
def ray (m B : Side) (c : Part m B) (U : Skin m B) (s : ArrayF m) (x y : Sq) := ∑ j∈range (way B), rad m B c U s x y j

def banner (m B : Side) (e : ℝ) (r : Zone) := {t:Skin m B×ArrayF m | Guard t.1 e ∧ Verified m B margin t.1 t.2 r}
variable (c : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B} (h : Guard U e) {s : ArrayF m} {r : Zone} (V : Verified m B margin U s r)
include b
abbrev AxisY (m B : Side) := (Skin m B×ArrayF m)×Sq×Sq
def plate (m B : Side) (k : ℕ) (t : AxisY m B) := bow m B t.1.1 t.1.2 (increment B k t.2.1 t.2.2)
lemma plate_cont (k : ℕ) (g : k ≤ way B) : ContinuousOn (plate m B k) ((banner m B e r) ×ˢ ((zone r) ×ˢ (zone r))) := by
  rintro ⟨⟨W,F⟩,x,y⟩ ⟨⟨h,H⟩,p,q⟩; let i := ((W,F),x,y)
  let f := fun t : (Skin m B × ArrayF m) × Sq × Sq => (t.1.1, t.1.2,increment B k t.2.1 t.2.2)
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt ((fun u : Skin m B×ArrayF m×Sq=>bow m B u.1 u.2.1 u.2.2) ∘ f) i
  apply ContinuousAt.comp
  · exact bow_at b h H (inc_in p q B g)
  unfold f increment; dsimp only; fun_prop
lemma screen : ContinuousOn (fun t : AxisY m B=>lens m B c t.1.1) ((banner m B e r) ×ˢ ((zone r) ×ˢ (zone r))) := by
  apply ContinuousOn.comp (lens_cont c b) (f:=fun t : AxisY m B=>t.1.1) (continuous_fst.comp continuous_fst).continuousOn _
  exact fun t a=> a.1.1
omit b in
lemma spark_run {X I : Type*} [Fintype I] [DecidableEq I] [TopologicalSpace X] (L J K : X → Op I) (Y : Set X)
    (h : ContinuousOn L Y) (u : ContinuousOn J Y) (v : ContinuousOn K Y) (g : ∀ x∈Y, IsUnit (stage (L x) (J x)))
    (r : ∀ x∈Y, ‖relay (L x) (J x) (K x)-1‖<1) : ContinuousOn (fun t=>spark (L t) (J t) (K t)) Y := by
  let f t := (L t,J t,K t)
  have H : ContinuousOn f Y := h.prodMk (u.prodMk v)
  intro x hx; change ContinuousWithinAt ((fun u : Op I × Op I×Op I=> spark u.1 u.2.1 u.2.2) ∘ f) _ x
  exact ContinuousAt.comp_continuousWithinAt (spark_contAt (g x hx) (r x hx)) (H x hx)
lemma rad_cont (j : ℕ) (hj : j < way B) : ContinuousOn (fun t : (Skin m B×ArrayF m)×Sq×Sq=>rad m B c t.1.1 t.1.2 t.2.1 t.2.2 j) ((banner m B e r) ×ˢ ((zone r) ×ˢ (zone r))) := by
  let Y := (banner m B e r) ×ˢ ((zone r) ×ˢ (zone r))
  let L (t : AxisY m B) := lens m B c t.1.1
  change ContinuousOn (fun t=>spark (L t) (plate m B j t) (plate m B (j+1) t)) Y
  refine spark_run L _ _ Y (screen c b) (plate_cont b j hj.le) (plate_cont b (j+1) hj) ?_ ?_
  · rintro ⟨⟨W,F⟩,x,y⟩ ⟨⟨h,H⟩,p,q⟩
    exact (bow_ok c b h H (inc_in p q B hj.le)).2
  rintro ⟨⟨W,F⟩,x,y⟩ ⟨⟨h,H⟩,p,q⟩
  exact short c b h H (inc_in p q B hj.le) (inc_in p q B hj) (inc_gap p q B j)
lemma rays_cont : ContinuousOn (fun t : (Skin m B×ArrayF m)×Sq×Sq=>ray m B c t.1.1 t.1.2 t.2.1 t.2.2) ((banner m B e r) ×ˢ ((zone r) ×ˢ (zone r))) := by
  unfold ray; exact continuousOn_finsetSum _ (fun j hj=>rad_cont c b j (mem_range.mp hj))
include h V
variable {x y z : Sq}
lemma ray_contzone (u : x∈zone r) : ContinuousOn (ray m B c U s x) (zone r) := by
  let f := fun t:Sq=> ((U,s),x,t)
  let F := fun t : (Skin m B×ArrayF m)×Sq×Sq=>ray m B c t.1.1 t.1.2 t.2.1 t.2.2
  change ContinuousOn (F ∘ f) _
  apply ContinuousOn.comp (rays_cont c b)
  · exact (show Continuous f from continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
  exact fun t g => ⟨⟨h,V⟩,u,g⟩
lemma point_log (o : UNI (Mind m B)) (S : Finset (Mind m B)) (e : lens m B c U=twist o (cutM S)) (k : x∈zone r) (q : y∈zone r) :
    Complex.exp (ray m B c U s x y)*stratum o S (bow m B U s x)=stratum o S (bow m B U s y) := by
  let f y := ray m B c U s x y; let C y := stratum o S (bow m B U s y); let P := lens m B c U
  have hx y (hy : y∈zone r) : C y≠0 := by
    have hg := bow_full c b h V hy; rw [e] at hg; exact strata_gap _ _ _ hg
  have ht : ContinuousOn f (zone r) := ray_contzone c b h V k
  have hf : ContinuousOn C (zone r) := by
    intro v hv; apply ContinuousAt.continuousWithinAt; unfold C stratum
    let A := fun y:Sq=>(U,s,y)
    have ha : Continuous A := continuous_const.prodMk (continuous_const.prodMk continuous_id)
    let Y := fun i : Skin m B × ArrayF m×Sq=> bow m B i.1 i.2.1 i.2.2
    have he : ContinuousAt (Y ∘ A) v := (show ContinuousAt Y (A v) from bow_at b h V hv).comp ha.continuousAt
    have hk : ContinuousAt (pairWave (n:=Mind m B) ∘ Y ∘ A) v := pairWave_cont.continuousAt.comp he
    exact (continuousAt_const (y:=(wedge _ _))).inner hk
  let g' := fun y=> Complex.exp (f y)*C x
  have hg' : ContinuousOn g' (zone r) := (Complex.continuous_exp.comp_continuousOn ht).mul continuousOn_const
  have hu : g' x=C x := by
    unfold g' f ray rad; simp_rw [inc_same,spark_equal (lensP c b h) (bow_ok c b h V k).2]; simp
  apply stalk (cube_path r).isPreconnected hg' hf x k _ hx hu y q
  intro v hv; let Z := increment B; unfold g'; rw [mul_pow]; unfold f ray
  suffices H : ∀ j≤way B, Complex.exp (∑ i∈range j, rad m B c U s x v i)^2*C x^2=C (Z j x v)^2 by
    have hi := H (way B) le_rfl; simpa only [Z,inc_last] using hi
  intro j g
  induction j with
  | zero => rw [range_zero,sum_empty,Complex.exp_zero,one_pow,one_mul, show Z 0 x v=x from inc_zero ..]
  | succ j ih =>
    have he := ih (by omega); have g₁ := inc_in k hv B (show j≤way B by omega); have g₂ := inc_in k hv B g
    have hk := bow_val c b h V g₁; have hz := bow_val c b h V g₂
    have hw := (bow_ok c b h V g₁).2; have hl := short c b h V g₁ g₂ (inc_gap k hv B j)
    rw [sum_range_succ,add_comm _ (rad _ _ _ _ _ _ _ _),Complex.exp_add,mul_pow,mul_assoc,he,rad,e]; rw [e] at hw hl
    exact spark_sq _ _ hk.2.1 hz.2.1 hw hl
lemma ray_add (u : x∈zone r) (v : y∈zone r) (w : z∈zone r) : ray m B c U s x z=ray m B c U s x y+ray m B c U s y z := by
  let f := ray m B c U s
  apply carry_log (cube_path r).isPreconnected (ray_contzone c b h V u) (continuousOn_const.add (ray_contzone c b h V v)) y v (w:=fun i=>f x y+f y i) _ _ z w
  · intro t ht
    obtain ⟨o,S,e⟩ := spot_projection _ (lensP c b h)
    let A i := stratum o S (bow m B U s i)
    have hx : A x≠0 := strata_gap _ _ _ (by rw [←e]; exact bow_full c b h V u)
    apply mul_right_cancel₀ hx
    change _=Complex.exp (f x y+f y t)*A x
    rw [show Complex.exp (ray m B c U s x t)*A x=A t from point_log _ b h V _ _ e u ht, add_comm, Complex.exp_add,mul_assoc]
    rw [show Complex.exp (f x y)*A x=A y from point_log _ b h V _ _ e u v]; exact (point_log c b h V _ _ e v ht).symm
  have hu : f y y=0 := by
    unfold f ray rad; simp_rw [inc_same,spark_equal (lensP c b h) (bow_ok c b h V v).2,sum_const_zero]
  rw [hu,add_zero]
lemma ray_g (u : x∈zone r) (v : y∈zone r) (g : Site (Domain m B) → E) : ray m B c (gauge g U) (onF g s) x y=ray m B c U s x y := by
  unfold ray; apply sum_congr rfl; intro i hi; have ht := mem_range.mp hi
  have he := inc_in u v B ht.le; have hf := inc_in u v B ht
  rw [rad,bow_g,bow_g,lens_g c b h, spark_turn (bow_ok c b h V he).2 (short c b h V he hf (inc_gap u v B i))]
  rfl
lemma ray_filled (u : x∈zone r) (v : y∈zone r) :
    Complex.exp (ray m B c U s x y) • filled (lens m B c U) (bow m B U s x)=filled (lens m B c U) (bow m B U s y) := by
  obtain ⟨o,S,e⟩ := spot_projection _ (lensP c b h)
  rw [e,placed,placed,smul_smul,point_log c b h V _ _ e u v]
end YM.CF.Phase
