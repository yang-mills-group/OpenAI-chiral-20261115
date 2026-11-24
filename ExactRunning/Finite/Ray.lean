import YM.Next.STATIONARY.Loops.Syntax

/-! # Finite matrix helpers -/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

lemma approached_inj : Function.Injective (@approached α β) := by
  intro A B h; ext a b; simpa [approached] using congr_fun (congr_fun h a) b

lemma approach_one (α : Type) [DecidableEq α] : approached (1:Matrix α α ℝ) = 1 := by
  ext a b; by_cases h : a=b <;> simp [approached, Matrix.one_apply,h]

lemma rotations_unit (m : Side) (α : Type) [DecidableEq α] [Fintype α] :
    IsUnit (rotations m α).det := by
  let B := ((m.val : ℂ)^4)⁻¹ • star (rotations m α)
  have e : rotations m α * B = 1 := by
    rw [show B = _ from rfl, Matrix.mul_smul,rotations_gram,smul_smul,
        inv_mul_cancel₀ (pow_ne_zero _ (side_ne _)),one_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_,_,e,mul_eq_one_comm.mp e⟩,rfl⟩

lemma mat_ext_on_tune {A B : Matrix ι (Co m α) ℂ}
    (h : ∀ p v, A *ᵥ tune p v = B *ᵥ tune p v) : A = B := by
  ext a b
  have k : A a = B a := by
    apply ray_book; intro p v
    rw [dotProduct_comm, dotProduct_comm _ (B a)]; exact congr_fun (h p v) a
  exact congr_fun k b

lemma tune_smul (p : Site m) (v : Phase ι) (z : ℂ) :
    tune p (z • v) = z • tune p v := by
  ext; simp [tune,mul_left_comm]

lemma tune_sum (p : Site m) (s : Finset α) (v : α → Phase ι) :
    tune p (∑ i∈s, v i) = ∑ i∈s, tune p (v i) := by
  ext; simp [tune, Finset.mul_sum]

/-- Static operator for a grid symbol. -/
lemma exists_circ (m : Side) (W : Site m → CompM α β) :
    ∃ K : CircM m α β, ∀ p (v : Phase β), K *ᵥ tune p v = tune p (W p *ᵥ v) := by
  let R := rotations m β
  let A : CircM m α β := of fun i j => tune j.1 (W j.1 *ᵥ Pi.single j.2 1) i
  let K := A*R⁻¹
  refine ⟨K, fun p v => ?_⟩
  have he (x : β) : K *ᵥ tune p (Pi.single x 1) = tune p (W p *ᵥ Pi.single x 1) := by
    have hk : K * R = A := Matrix.nonsing_inv_mul_cancel_right R A (rotations_unit m β)
    funext i
    have t := congr_fun (congr_fun hk i) (p,x)
    change ∑ j, K i j * tune p (Pi.single x 1) j = _
    rw [← (show (fun j => R j (p,x)) = tune p (Pi.single x 1) from funext fun j => coef_wave ..)]
    exact t
  have w : v = ∑ i, v i • Pi.single i (1:ℂ) := by ext; simp [Pi.single_apply]

  rw [w]
  simp only [tune_sum,Matrix.mulVec_sum,tune_smul,Matrix.mulVec_smul,he]

lemma exists_jaunt (m : Side) (w : Momentum → CompM α β)
    (h : ∀ p q, rolls (mon (n:=m) p) q → w (mon p) = w q) :
    ∃ K : CircM m α β, Jaunt K w 0 := by
  obtain ⟨K,hK⟩ := exists_circ m (w ∘ mon)
  exact ⟨K,fun p q hp v => by rw [← h p q hp,add_zero]; exact hK p v⟩

lemma conj_mulVec (A : Matrix ι α ℂ) (v : Phase α) :
    star (A *ᵥ v) = A.map conj *ᵥ star v := by
  ext; simp [Matrix.mulVec, dotProduct]

lemma conj_tune (p : Site m) (v : Phase ι) :
    star (tune p v) = tune (-p) (star v) := by
  ext; simp [tune,cell_duality (-p),cell_inverse, ← cell_duality p]

lemma exists_jaunt_real (m : Side) (w : Momentum → CompM α β)
    (h : ∀ p q, rolls (mon (n:=m) p) q → w (mon p) = w q)
    (hstar : ∀ p : Site m, (w (-(mon p))).map conj = w (mon p)) :
    ∃ K, Jaunt (approached K : CircM m α β) w 0 := by
  obtain ⟨A,hA⟩ := exists_jaunt m w h
  have hb : A.map conj = A := by
    apply mat_ext_on_tune; intro p v
    rw [hA p _ (rolls.refl _)]
    have eq := hA (-p) _ (rolls.flip_sign (rolls.refl _)) (star v)
    simpa [conj_mulVec,conj_tune,hstar] using congr_arg star eq
  have hr : approached (A.map Complex.re) = A := by
    ext a b
    obtain ⟨r,hr⟩ := Complex.conj_eq_iff_real.mp (congr_fun (congr_fun hb a) b)
    simp [approached,hr]
  exact ⟨_,hr.symm ▸ hA⟩

/-- Grouping by internal momentum detects invertibility. -/
lemma isUnit_of_jaunt {K : CircM m α α} {w : Momentum → CompM α α} (h : Jaunt K w 0)
    (hu : ∀ p : Site m, IsUnit (w (mon p)).det) : IsUnit K.det := by
  obtain ⟨X,hx⟩ := exists_circ m (fun p => (w (mon p))⁻¹)
  have ht : K*X=1 := by
    apply mat_ext_on_tune; intro p v
    rw [← Matrix.mulVec_mulVec,hx,h p _ (rolls.refl _),add_zero,Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hu _), Matrix.one_mulVec, Matrix.one_mulVec]
  exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_,_,ht,mul_eq_one_comm.mp ht⟩,rfl⟩

lemma isUnit_of_approached {A : Matrix α α ℝ} (h : IsUnit (approached A).det) :
    IsUnit A.det := by
  have hk : (approached A).det = (A.det : ℂ) := (Complex.ofRealHom.map_det A).symm
  rw [hk,isUnit_iff_ne_zero, Ne, Complex.ofReal_eq_zero] at h
  exact isUnit_iff_ne_zero.mpr h

lemma jaunt_eq {a : Site m} {A B : CircM m α β}
    {w : Momentum → CompM α β} (h : Jaunt A w a) (i : Jaunt B w a) : A = B :=
  mat_ext_on_tune fun p v => by rw [h p _ (rolls.refl _), i p _ (rolls.refl _)]

end ExactRunning
