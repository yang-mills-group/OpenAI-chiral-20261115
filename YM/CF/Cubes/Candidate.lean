import YM.CF.Cubes.Nest

/-!
# Sphere avoidance with a uniform margin
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU
open scoped Matrix.Norms.L2Operator MatrixOrder Topology InnerProductSpace
attribute [local instance] opCStarAlgebra

def ren (x : Vect) := ‖x‖⁻¹ • x
lemma ren_norm (x : Vect) (h : x ≠ 0) : ‖ren x‖=1 := by simp [ren,norm_smul,h]
lemma ren_cont (x : Vect) (h : x≠0) : ContinuousAt ren x := by unfold ren; fun_prop (disch:=simp [h])
def Sphere := Metric.sphere (0:Vect) 1
abbrev Ballot := ↥Sphere
lemma vote_unit (x : Ballot) : ‖x.val‖=1 := by simpa [Sphere] using x.property
instance : Nonempty Ballot := ⟨⟨basisKet 0, by simp [Sphere,basisKet]⟩⟩
instance : CompactSpace Ballot := isCompact_iff_compactSpace.mp (isCompact_sphere ..)
def spinV (g : E) : Vect →ₗᵢ[ℝ] Vect := { ((acts (fund g)).restrictScalars ℝ).toLinearMap with
  toFun := turn g, norm_map' := fun x => turn_norm g x }
lemma spinV_i (g : E) (x y : Vect) : inner ℝ (turn g x) (turn g y)=inner ℝ x y := (spinV g).inner_map_map ..
def scaledV (g : E) (x : Ballot) : Ballot :=
  ⟨turn g x.val, by simp [Sphere,turn_norm,vote_unit]⟩
lemma scaled_cont : Continuous (fun t:E×Ballot => scaledV t.1 t.2) := Continuous.subtype_mk (turn_cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
lemma turn_mul (g : E) (x : Vect) (c : ℝ) : turn g (c • x)=c • turn g x := (spinV g).map_smul _ _
lemma dim_vect : Module.finrank ℝ Vect=10 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ,Complex.finrank_real_complex]; simp [Vect,Ket,F]
lemma normal (l : List Vect) (h : l.length < 10) : ∃ x : Ballot, ∀ z∈l, inner ℝ x.val z=0 := by
  classical
  let s := l.toFinset; let T := Submodule.span ℝ (s : Set Vect)
  have hz : Module.finrank ℝ T ≤ s.card := by simpa [T] using finrank_span_le_card (R:=ℝ) (s : Set Vect)
  have he : Tᗮ ≠ ⊥ := by
    intro g; rw [Submodule.orthogonal_eq_bot_iff] at g
    have ht : Module.finrank ℝ T < 10 := lt_of_le_of_lt (hz.trans (List.toFinset_card_le l)) h
    rw [g, finrank_top,dim_vect] at ht; omega
  obtain ⟨x,hx,g⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
  refine ⟨⟨ren x, by simp [Sphere,ren_norm x g]⟩,?_⟩; intro z hk
  apply (Submodule.mem_orthogonal' T (ren x)).mp (Tᗮ.smul_mem _ hx) z
  exact Submodule.subset_span (by simpa [s])
section
variable {I : Type*}
lemma miss (s : Finset I) (v : I → Ballot) : ∃ w : Ballot, ∀ i∈s, inner ℝ w.val (v i).val≠0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary Ballot,by simp⟩
  | insert i s e ih =>
    obtain ⟨w,hw⟩ := ih
    let z (c : ℝ) := w.val+c • (v i).val; let a j := inner ℝ w.val (v j).val; let b j := inner ℝ (v i).val (v j).val
    obtain ⟨c,hc⟩ := Infinite.exists_notMem_finset ((insert i s).image (fun j => -a j/b j))
    have he j (hj : j∈ insert i s) : inner ℝ (z c) (v j).val≠0 := by
      intro g; rw [show z c=w.val+c • (v i).val from rfl,inner_add_left, real_inner_smul_left] at g; change a j+c*b j=0 at g
      by_cases ge:b j=0
      · by_cases h : j=i
        · subst j; simp [b,real_inner_self_eq_norm_sq,vote_unit] at ge
        apply hw _ ((Finset.mem_insert.mp hj).resolve_left h); change a j=0; simpa [ge] using g
      apply hc; apply Finset.mem_image.mpr; exact ⟨j,hj,(div_eq_iff ge).mpr (by linarith)⟩
    have k : z c ≠ 0 := by intro hy; have h := he i (Finset.mem_insert_self ..); rw [hy, inner_zero_left] at h; exact h rfl
    refine ⟨⟨ren (z c),by simp [Sphere,ren_norm _ k]⟩,?_⟩
    intro j hj; change inner ℝ (‖z c‖⁻¹ • z c) _≠0; rw [real_inner_smul_left]; exact mul_ne_zero (by simp [k]) (he _ hj)
lemma sm_min (s : Finset I) (a : I → ℝ) (h : ∀ i∈s, 0 < a i) : ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t < a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert i s g ih =>
    obtain ⟨x,hx,q⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)); obtain ⟨y,hy,k⟩ := exists_between (h i (by simp))
    refine ⟨min x y, lt_min hx hy,?_⟩; intro j hj; rcases Finset.mem_insert.mp hj with l|l
    · subst j; exact lt_of_le_of_lt (min_le_right ..) k
    exact lt_of_le_of_lt (min_le_left ..) (q _ l)
end
open Finset
lemma sphereMargin (k : ℕ) : ∃ t : ℝ, 0<t ∧ ∀ v : Fin k → Ballot, ∃ w : Ballot, ∀ i, t < |inner ℝ w.val (v i).val| := by
  have h (v : Fin k → Ballot) : ∃ w : Ballot, ∃ t:ℝ, 0<t ∧ ∀ i, t < |inner ℝ w.val (v i).val| := by
    obtain ⟨w,h⟩ := miss univ v
    obtain ⟨t,k,H⟩ := sm_min univ _ (show ∀ i∈univ, 0 < |inner ℝ w.val (v i).val| from fun i hi=> abs_pos.mpr (h i hi))
    exact ⟨w,t,k,fun i => H i (mem_univ i)⟩
  choose w a ha h using h
  let U := fun v => ⋂ i, {u : Fin k → Ballot | a v < |inner ℝ (w v).val (u i).val|}
  have he v : IsOpen (U v) := isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ((continuous_const.inner (continuous_subtype_val.comp (continuous_apply i))).abs)
  obtain ⟨s,H⟩ := isCompact_univ.elim_finite_subcover U he (fun v _ => Set.mem_iUnion.mpr ⟨v,Set.mem_iInter.mpr (h v)⟩)
  obtain ⟨t,k,Ht⟩ := sm_min s a (fun i _=>ha i); refine ⟨t,k,?_⟩; intro u; obtain ⟨v,hv,g⟩ := Set.mem_iUnion₂.mp (H (Set.mem_univ u))
  exact ⟨w v,fun i => (Ht v hv).trans (Set.mem_iInter.mp g i)⟩
lemma uniform_miss (k : ℕ) : ∃ t : ℝ, 0<t ∧ ∀ (I : Type) (s : Finset I), s.card≤k →
    ∀ v:s → Ballot, ∃ w : Ballot, ∀ i, t < |inner ℝ w.val (v i).val| := by
  choose t ht h using sphereMargin
  obtain ⟨b,hb,H⟩ := sm_min (range (k+1)) t (fun i _=>ht i); refine ⟨b,hb,?_⟩; intro I s g v
  let e := Fintype.equivFin ↥s
  obtain ⟨w,h⟩ := h _ (v ∘ e.symm); refine ⟨w,?_⟩; intro i
  exact (H _ (by simpa using (show Fintype.card s≤k from by simpa using g) |>.trans_lt (Nat.lt_succ_self k))).trans (by simpa using h (e i))
end YM.CF.Cube
