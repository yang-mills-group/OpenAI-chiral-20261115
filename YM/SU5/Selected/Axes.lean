import YM.SU5.Selected.Gauge
/-!
# Compatibility of adjoints in the common compressed algebra

Without this, e.g., one could not conclude equal norms from between_axes
(the two experiments compute identical ordinary *moments*, not starred
moments computed with the respective adjoints unless this is separately
justified!). Two commuting real structures; anti-eigenspace of their
composition dies by positivity at the two axes.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 310000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
variable (j' : Axis)
section mirror
private lemma join_plane : joinX (plane j 0) (plane j' 0) = joinX (plane j' 0) (plane j 0) := by
  have h : Signed.mirror j * Signed.mirror j' = Signed.mirror j' * Signed.mirror j := by
    apply Signed.ext
    · rfl
    funext b; exact Bool.xor_comm _ _
  simp [joinX, plane, h]

-- use signs on actual pin lift to the torus and corresponding theta.
-- spin and sector computation as in Buffered/Flips, here on these reflections.
private lemma other_car {n : Side} (h : j ≠ j') :
    (carR j 0 n).val * (carR j' 0 n).val = -((carR j' 0 n).val * (carR j 0 n).val) := by
  change (carR j _ _ * carR j' _ _).val = -(carR j' _ _ * carR j _ _).val
  unfold carR; rw [kio,kio,join_plane j j']
  have hp : pin j*pin j' = -(pin j'*pin j) := by
    unfold pin; simp only [←mul_assoc]
    rw [mul_assoc (gammaOp j), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap j j' h,
      neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j') grading, gradingSwap, mul_neg,
      neg_mul, neg_neg, mul_assoc]; simp only [mul_assoc]
  have he : (pinLift j * pinLift j').val = (-1:ℂ) • (pinLift j' * pinLift j).val := by
    rw [neg_one_smul]; exact hp
  rw [Ygs _ _ _ he, neg_one_smul]

private lemma anti_theta {n : Side} (h : j ≠ j') {S : Finset (Single n)} {p : Bool}
    {A : FC (Single n)} (v : Sector S p A) :
    theta (carR j 0 n) (theta (carR j' 0 n) A) = (if p then (-1:ℂ) else 1) •
      theta (carR j' 0 n) (theta (carR j 0 n) A) := by
  have he (i j : Axis) (x : Ket (Single n)) :
      theta (carR i 0 n) (theta (carR j 0 n) (create x)) =
        -create (acts (carR i 0 n).val (acts (carR j 0 n).val x)) := by
    rw [theta_upV,theta_smul,theta_downV]; simp [smul_smul]
  have hz (x) : acts (carR j 0 n).val (acts (carR j' 0 n).val x) =
      -acts (carR j' 0 n).val (acts (carR j 0 n).val x) := by
    rw [←act_mul, ←act_mul, other_car j j' h, act_neg]
  induction v with
  | zero => simp only [theta_zero,smul_zero]
  | one => rw [theta_one,theta_one,theta_one]; simp
  | up k _ => rw [←create_put,he,he,hz,map_neg]; simp
  | down k _ => rw [takeF,theta_star,theta_star,theta_star,theta_star,← create_put,he,he,hz,map_neg]; simp
  | add _ _ p q => rw [theta_add,theta_add,theta_add,theta_add,p,q,smul_add]
  | scale _ z p => rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,p,smul_comm]
  | @mul a b _ _ x y h p => rw [theta_mul,theta_mul,theta_mul,theta_mul,h,p]; cases a <;> cases b <;> simp

lemma dual_commute (x : observable K strict) :
    dual Y H j strict (dual Y H j' strict x) = dual Y H j' strict (dual Y H j strict x) := by
  by_cases p : j=j'; · subst j'; rfl
  apply Subtype.ext; funext n v
  obtain ⟨S,t⟩ := x.property.1.paid
  let f (j : Axis) := fling j 0 ((K).c n)
  let F := (v.1,v.2); let T (j : Axis) := Prod.map (f j) (f j)
  have he : T j (T j' v) = T j' (T j v) := by
    unfold T f fling; dsimp only [Prod.map]; rw [←kor, ←kor, ←kor, ←kor, join_plane j j']
  change theta _ (theta _ (x.val n (T j' (T j v)))) = theta _ (theta _ (x.val n (T j (T j' v))))
  rw [he]; simpa only [Bool.false_eq_true,ite_false,one_smul] using anti_theta j j' p ((t.support n).allV (T j' (T j v))|>.sector)
end mirror

local notation "R" u:max U:max => groundRoom Y H V Q u strict U
local notation "𝔄" u:max U:max => displayAlgebra Y H V Q Qt u strict U
local notation "X" => Marks (tent Y H) strict
local notation "Ω" u:max U:max => seat0 Y H V Q u strict U
local notation "θ" i:max => dual Y H i strict
local notation "T" i:max => reflectOn Y H i strict
local notation "P" u:max U:max s:max => located Y H V s Q Qt u strict U
local notation "𝒫" u:max U:max => instrument Y H V Q Qt u strict U
variable (C' : Arena Y H Q.circuit j' 0 strict)

noncomputable def mirrorInMarks (x : X) : X := dual Y H j strict x
local notation "θM" i:max => mirrorInMarks Y H i strict
lemma mirrorInMarks_sub (x y : X) : (θM j) (x-y) = (θM j) x - (θM j) y := by
  apply Subtype.ext; change mirror K j 0 (x.val-y.val) = _
  rw [sub_eq_add_neg x.val, ←neg_one_smul ℂ y.val, mirror_plus, mirror_scale,
    star_neg,star_one, neg_one_smul, ←sub_eq_add_neg]
  rfl
lemma mirIn_square (x : X) : (θM j) ((θM j) x) = x :=
  Subtype.ext (mirror_invert K j 0 (marksSpec strict x).1)
lemma mir_preserves_adjoint (x : X) : (P j C s) ((θM j) x) = star ((P j C s) x) :=
  mirror_display Y H V s Q Qt j strict C x

-- all finite meetings of compressed moments **up to 3** needed below. Again, repeat
-- inputs may be used without restriction. Allow SAME axis but different Arena.
private lemma parallel {S : Type*} [Fintype S] (x : S → Beacon K strict)
    (p : List S) (h : p.Nodup) : heavies Y H V Q Qt j strict C x p =
      heavies Y H V Q Qt j' strict C' x p := by
  by_cases k : j=j'
  · subst j'; obtain ⟨a,ha⟩ := exists_ne j
    let d := Classical.choice (voyage_H Y H V Q.circuit a 0 strict)
    exact (between_axes Y H V Q Qt j strict C x a d ha.symm p p h (.refl _)).trans
      (between_axes Y H V Q Qt j strict C' x a d ha.symm p p h (.refl _)).symm
  exact between_axes Y H V Q Qt j strict C x j' C' k p p h (.refl _)

private lemma two (x y : Beacon K strict) :
    inner ℂ (Ω j C) (((𝒫 j C) x * (𝒫 j C) y) (Ω j C)) =
      inner ℂ (Ω j' C') (((𝒫 j' C') x * (𝒫 j' C') y) (Ω j' C')) :=
  parallel Y H V Q Qt j strict C j' C' (![x,y] : Fin 2 → Beacon K strict) [0,1] (by decide)
private lemma three (x y z : Beacon K strict) :
    inner ℂ (Ω j C) (((𝒫 j C) x * (𝒫 j C) y * (𝒫 j C) z) (Ω j C)) =
      inner ℂ (Ω j' C') (((𝒫 j' C') x * (𝒫 j' C') y * (𝒫 j' C') z) (Ω j' C')) :=
  parallel Y H V Q Qt j strict C j' C' (![x,y,z] : Fin 3 → Beacon K strict) [0,1,2] (by decide)

/-- Anti-part dies as an operator, not just in one-point mean. -/
private lemma detectRealStructures (x : X) (h : (θM j') x = -(θM j) x) :
    (P j C s) x=0 ∧ (P j' C' s) x=0 := by
  let a := ((P j C s) x); let b := ((P j' C' s) x)
  have k := two Y H V Q Qt j strict C j' C' (s,(θM j) x) (s,x)
  have ht : (P j' C' s) ((θM j) x) = - star b := by
    unfold b
    rw [←mir_preserves_adjoint,h,map_neg,neg_neg]
  change inner ℂ (Ω j C) ((((P j C s) ((θM j) x))*a).val (Ω j C)) =
    inner ℂ (Ω j' C') ((((P j' C' s) ((θM j) x))*b).val (Ω j' C')) at k
  rw [ht,mir_preserves_adjoint, neg_mul] at k
  let A' := a.val (Ω j C); let B' := b.val (Ω j' C')
  change inner ℂ (Ω j C) (a.val.adjoint A') = inner ℂ (Ω j' C') (-(b.val.adjoint B')) at k
  rw [inner_neg_right,ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right] at k
  change inner ℂ A' A'= -(inner ℂ B' B') at k
  have hq : 0 ≤ inner ℂ A' A':= by rw [inner_self_eq_norm_sq_to_K]; positivity
  have hk : 0 ≤ inner ℂ B' B':= by rw [inner_self_eq_norm_sq_to_K]; positivity
  have ha0 : inner ℂ A' A'=0 := le_antisymm (k.trans_le (neg_nonpos.mpr hk)) hq
  rw [ha0,eq_neg_iff_add_eq_zero, zero_add] at k -- check lemma
  exact ⟨display_faithful Y H V Q Qt j strict C (show A'=0 from inner_self_eq_zero.mp ha0),
    display_faithful Y H V Q Qt j' strict C' (show B'=0 from inner_self_eq_zero.mp k)⟩

include C' in
theorem real_structure (x : Beacon K strict) :
    (𝒫 j C) ((T j') x) = star ((𝒫 j C) x) := by
  let v : X := x.2; let a := (θM j') v; let b := (θM j) v
  have he : (θM j) ((θM j') v) = (θM j') ((θM j) v) := dual_commute Y H j strict j' v
  have ht : (θM j') (a-b) = -(θM j) (a-b) := by
    unfold a b; rw [mirrorInMarks_sub, mirrorInMarks_sub, he, mirIn_square, mirIn_square, neg_sub]
  have h := (detectRealStructures Y H V x.1 Q Qt j strict C j' C' _ ht).1
  rw [map_sub, sub_eq_zero] at h
  rw [← mat_star]; exact congrArg (fun z : (𝔄 j C) => z.val) h


local notation "M" x:max => (𝒫 j C) x
local notation "M'" x:max => (𝒫 j' C') x

private lemma grams (x y : Beacon K strict) :
    inner ℂ ((M x) (Ω j C)) ((M y) (Ω j C)) =
      inner ℂ ((M' x) (Ω j' C')) ((M' y) (Ω j' C')) := by
  have h := two Y H V Q Qt j strict C j' C' ((T j) x) y
  rw [mat_star, real_structure Y H V Q Qt j' strict C' j C] at h
  rw [←ContinuousLinearMap.adjoint_inner_right, ←ContinuousLinearMap.adjoint_inner_right (M' x)]; exact h

private lemma triples (x y z : Beacon K strict) :
    inner ℂ ((M x) (Ω j C)) (((M y)*(M z)) (Ω j C)) =
      inner ℂ ((M' x) (Ω j' C')) (((M' y)*(M' z)) (Ω j' C')) := by
  have h := three Y H V Q Qt j strict C j' C' ((T j) x) y z
  rw [mat_star, real_structure Y H V Q Qt j' strict C' j C] at h
  rw [←ContinuousLinearMap.adjoint_inner_right, ←ContinuousLinearMap.adjoint_inner_right (M' x)]; exact h

-- can use the dense-range UPColl here instead of finitary price. Keeping Hilbert
-- universes here for YM Gram constructions.
open _root_.YM.Kernel
lemma gram_impl {A B : Hilbert} {X' : Type} {f : X' → A} {g : X' → B}
    (p : DenseRange f) (q : DenseRange g)
    (m : ∀ i j : X', inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) :
    ∃ U : A ≃ₗᵢ[ℂ] B, ∀ i, U (f i)=g i := by
  let G : Gram (fun i j : X' => inner ℂ (f i) (f j)) := ⟨A,f,p.mono (Submodule.subset_span),fun _ _ => rfl⟩
  let f' := G.stems; let g' := Finsupp.linearCombination ℂ g
  have he (x y : X' →₀ ℂ) : inner ℂ (f' x) (f' y) = inner ℂ (g' x) (g' y) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p q u v => simp only [map_add,inner_add_left,u,v]
    | single i a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add p q u v => simp only [map_add,inner_add_right,u,v]
      | single j b => simp [f',G,Gram.stems,g',m]
  obtain ⟨U,h,Uf⟩ := G.by_bound g 1 zero_le_one (fun x => by
    have ht := congrArg (RCLike.re («K»:=ℂ)) (he x x)
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at ht; rw [one_mul]
    change ‖g' x‖ ≤ ‖f' x‖; nlinarith [norm_nonneg (f' x),norm_nonneg (g' x)])
  change ∀ i, U (f i)=g i at Uf
  -- G.H may need annotation
  let u : A →L[ℂ] B := U
  have hu : ∀ x:A, ‖u x‖=‖x‖ := congr_fun (p.equalizer (u.continuous.norm) continuous_norm (funext fun i => by
    change ‖U (f i)‖=‖f i‖; rw [Uf]; have ht := congrArg (RCLike.re («K»:=ℂ)) (m i i); rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at ht; nlinarith [norm_nonneg (f i), norm_nonneg (g i)]))
  let s : A →ₗᵢ[ℂ] B := { u.toLinearMap with norm_map' := hu }
  have hp (y:B) : y ∈ Set.range s := closure_minimal (t:=Set.range s) (by rintro _ ⟨i,rfl⟩; exact ⟨f i,Uf i⟩) s.isometry.isClosedEmbedding.isClosed_range (q y)
  exact ⟨LinearIsometryEquiv.ofSurjective s hp,Uf⟩

noncomputable def adjust : (R j C) ≃ₗᵢ[ℂ] (R j' C') :=
  (gram_impl (A:=groundRoom Y H V Q j strict C) (B:=groundRoom Y H V Q j' strict C')
    (compressed_dense Y H V Q Qt j strict C) (compressed_dense Y H V Q Qt j' strict C') (grams Y H V Q Qt j strict C j' C')).choose

local notation "W" => adjust Y H V Q Qt j strict C j' C'
lemma adjusts (x : Beacon K strict) : W ((M x) (Ω j C)) = (M' x) (Ω j' C') :=
  (gram_impl (A:=groundRoom Y H V Q j strict C) (B:=groundRoom Y H V Q j' strict C')
    (compressed_dense Y H V Q Qt j strict C) (compressed_dense Y H V Q Qt j' strict C') (grams Y H V Q Qt j strict C j' C')).choose_spec x
lemma adjust_symm : (W).symm = adjust Y H V Q Qt j' strict C' j C := by
  apply DFunLike.coe_injective; apply (compressed_dense Y H V Q Qt j' strict C').equalizer (W).symm.continuous (adjust Y H V Q Qt j' strict C' j C).continuous
  funext x; dsimp only [Function.comp_apply]; rw [adjusts,← adjusts Y H V Q Qt j strict C j' C',LinearIsometryEquiv.symm_apply_apply]
lemma adjust_exact (x : Beacon K strict) : (W).conjStarAlgEquiv (M x) = (M' x) := by
  apply DFunLike.coe_injective
  apply (compressed_dense Y H V Q Qt j' strict C').equalizer
    ((W).conjStarAlgEquiv (M x)).continuous ((M' x).continuous)
  funext z; apply (compressed_dense Y H V Q Qt j' strict C').eq_of_inner_right ℂ
  intro y; have he := triples Y H V Q Qt j strict C j' C' y x z
  change inner ℂ ((M' y) _) (W ((M x) ((W).symm ((M' z) _)))) = _
  apply Eq.trans _ he
  rw [← adjusts Y H V Q Qt j strict C j' C', ← adjusts Y H V Q Qt j strict C j' C',
    LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]
  rfl
lemma adjust_vac : W (Ω j C) = Ω j' C' := by
  have he := adjusts Y H V Q Qt j strict C j' C' (0,(1:X))
  change W (((P j C 0) 1).val (Ω j C)) = ((P j' C' 0) 1).val (Ω j' C') at he
  rw [located_one,located_one] at he; exact he

lemma adjustment_mem (x : 𝔄 j C) : (W).conjStarAlgEquiv x.val ∈ 𝔄 j' C' := by
  let e : (R j C).Op →⋆ₐ[ℂ] (R j' C').Op := (W).conjStarAlgEquiv.toStarAlgHom
  let S := (𝔄 j' C').comap e
  change x.val ∈ S
  have h : IsClosed (S : Set (R j C).Op) := (displayClosed Y H V Q Qt j' strict C').preimage (show Continuous e from open CStarAlgebra in map_continuous e)
  apply (StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le (s:=Set.range (𝒫 j C)) ?_) h) x.property
  rintro _ ⟨x,rfl⟩
  change (W).conjStarAlgEquiv ((𝒫 j C) x) ∈ 𝔄 j' C'
  rw [adjust_exact]; exact cap_displayed Y H V x.1 Q Qt j' strict C' x.2

/-- One adjustment of the entire ground C*-algebra, even though on the whole space the axes have
not been identified, nor the continuum geometry attained. -/
noncomputable def adjustment : (𝔄 j C) ≃⋆ₐ[ℂ] (𝔄 j' C') := by
  let f : (R j C).Op →⋆ₐ[ℂ] (R j' C').Op := (W).conjStarAlgEquiv.toStarAlgHom
  let e := (f.comp (𝔄 j C).subtype).codRestrict _ (adjustment_mem Y H V Q Qt j strict C j' C')
  refine StarAlgEquiv.ofBijective e ⟨fun i jZ h => ?_, fun u => ?_⟩
  · exact Subtype.ext ((W).conjStarAlgEquiv.injective (congrArg Subtype.val h)) -- j shadow
  have h : (W).conjStarAlgEquiv.symm u.val ∈ 𝔄 j C := by
    rw [LinearIsometryEquiv.symm_conjStarAlgEquiv, adjust_symm]; exact adjustment_mem Y H V Q Qt j' strict C' j C u
  exact ⟨⟨_,h⟩,Subtype.ext ((W).conjStarAlgEquiv.apply_symm_apply _)⟩

local notation "W'" => adjustment Y H V Q Qt j strict C j' C'
lemma adjust_action (x : 𝔄 j C) : (W' x).val = (W).conjStarAlgEquiv x.val := rfl
lemma adjust_adj (x : X) : W' ((P j C s) x) = (P j' C' s) x := Subtype.ext (adjust_exact Y H V Q Qt j strict C j' C' (s,x))
lemma adjust_mean (x : 𝔄 j C) : inner ℂ (Ω j' C') ((W' x).val (Ω j' C')) = inner ℂ (Ω j C) (x.val (Ω j C)) := by
  rw [← adjust_vac Y H V Q Qt j strict C j' C', adjust_action,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply]; exact (W).inner_map_map .. -- tune

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.dual_commute
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.real_structure
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.adjustment
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.adjust_mean
