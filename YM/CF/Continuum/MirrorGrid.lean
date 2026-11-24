import YM.CF.Spire.Stand
import YM.CF.Reed.Dance
import YM.CF.Reflect.Center

/-!
# A reflection of the FiniteGaugeData grids

Use native units of the gauge lattice. Reflect in its time-zero plane (always
version with equal halves of the torus). Matter sites are *odd* sites. The
formula `prepU` therefore includes BOTH the half-spacing adjustment and the
anticut sign. We prove the actual values they take here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Fock Lattice Lat Cube SU Scroll Spire Tulip Mir Mir.Trip Phase RP
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {m B N : Side}

/-- Occupation indices for the physical (not tag) read. -/
abbrev SpinFields (m B : Side) := Single (CSide m B)

def shape (i : Axis) : Shape := ⟨Signed.mirror i, 0⟩
def gaugePoint (m B : Side) (i : Axis) : Site (Domain m B) → Site (Domain m B) :=
  revX m B i
def matterPoint (m B : Side) (i : Axis) : Equiv.Perm (Site (CSide m B)) :=
  tiltM m B i

def mirrorPane (m B : Side) (i : Axis) : Skin m B → Skin m B := rayUK m B i

local notation "Λ" => CSide m B

lemma glazed_slide (i : Axis) : glazed (slideM m i).glare = Signed.mirror i := by
  rfl

lemma mirrorPane_eq (i : Axis) : mirrorPane m B i = pull (Signed.mirror i) 0 := by
  funext V; dsimp only [mirrorPane, rayUK, through]; rw [glazed_slide, torShift, paneShift,
    show (slideM m i).move = 0 from rfl, map_zero, map_zero]

lemma gaugePoint_eq (i : Axis) (x : Site (Domain m B)) :
    (shape i).anon Λ x = gaugePoint m B i x := by
  unfold gaugePoint revX run Shape.anon shape
  rw [glazed_slide, torShift, paneShift, show (slideM m i).move = 0 from rfl,
    map_zero, map_zero]
  simp

lemma mirror_gauge (i : Axis) (g : Site (Domain m B) → E) (V : Skin m B) :
    mirrorPane m B i (gauge g V) = gauge (g ∘ gaugePoint m B i) (mirrorPane m B i V) :=
  invert_path (slideM m i) _ _

lemma mirror_invol (i : Axis) : Involutive (mirrorPane m B i) := by
  intro x; funext e
  unfold mirrorPane; rw [reflect_E]
  cases e with | mk x a =>
    by_cases p : a = i <;> simp only [p] <;> rw [reflect_E, ray_back] <;> simp [p, rayE]

lemma gaugePoint_invol (i : Axis) : Involutive (gaugePoint m B i) := (rev_back (m:=m) (B:=B) · i)
lemma matterPoint_invol (i : Axis) : Involutive ⇑(matterPoint m B i) := tiltBack i
lemma node_turn (i : Axis) (x) : node (matterPoint m B i x) = gaugePoint m B i (node x) :=
  tiltR i x

lemma matterPoint_eq (i : Axis) (x) : (shape i).mills Λ x = matterPoint m B i x :=
  Tenant.needle (by rw [Shape.nodex, node_turn, gaugePoint_eq])

private lemma cover_flee (i j : Axis) (x : Cover) :
    (shape i).flee x j = if i = j then -(x j)-1 else x j := by
  have h := congrFun ((shape i).mote x) j
  by_cases hj : i=j <;> simp [hj, Ne.symm, Shape.motion, shape, Signed.act, Signed.mirror] at h ⊢ <;> omega

lemma anti_sign (i : Axis) (x : Site N) : (shape i).payA x = -1 := by
  have hp : (shape i).rent x = -step i := by
    funext j; rw [Shape.rent, Rush.periods, cover_flee];
    have hv := ZMod.val_lt (x j); have hl := N.property
    by_cases hj : i = j
    · simp only [if_pos hj, Rush.natural]
      -- interval -N ≤ -val-1 < 0
      have hk : ((-(x j).val : ℤ) - 1) / N.val = -1 := by
        have hv' : (x j).val < N.val := hv
        rw [Int.ediv_eq_iff_of_pos (by positivity)]
        simp only [neg_one_mul]; omega
      rw [hk]; subst i; simp
    have hk : ((x j).val : ℤ) / N.val = 0 := by
      have hv' : (x j).val < N.val := hv
      exact Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hv')
    simp only [if_neg hj, Rush.natural, hk]; simp [Ne.symm hj]
  unfold Shape.payA; rw [hp]
  simp [Rush.fee, apply_ite]

/-- Pin convention matched to the Euclidean gamma matrices of this project. -/
abbrev pinLift (i : Axis) : UNI SpinIdx := ⟨pin i, pin_U i⟩

def fullTurn (m B : Side) (i : Axis) : UNI (SpinFields m B) :=
  prepU (shape i) (pinLift i) inert (CSide m B)

def onsite (N : Side) (i : Axis) : UNI (Single N) :=
  ⟨love N (pinM N i).val, by constructor
                             · rw [← map_star, ← map_mul, (pinM N i).property.1, map_one]
                             rw [← map_star, ← map_mul, (pinM N i).property.2, map_one]⟩

lemma fullTurn_matrix (i : Axis) :
    (fullTurn m B i).val = love (CSide m B) (-(finger m B i).val) := by
  unfold fullTurn; change love Λ (jump (Tofu (shape i) Λ) (fun x=>(milU (shape i) (pinLift i) inert x).val)) = _
  rw [seen, ← jump_neg]
  have h : Tofu (shape i) Λ = tiltM m B i := Equiv.ext (matterPoint_eq i)
  apply congrArg (love Λ); rw [h]
  congr 1; funext x; change (shape i).payA x • _ = (-(_ : Op (SpinIdx × Slot)))
  rw [anti_sign, neg_one_smul]; rfl

lemma fullTurn_square (i : Axis) :
    (fullTurn m B i).val*(fullTurn m B i).val = -1 := by
  rw [fullTurn_matrix, ←map_mul, neg_mul_neg, straight2, map_neg, map_one]

lemma onsite_square (i : Axis) :
    (onsite N i).val*(onsite N i).val = -1 := by
  change love N (spin N Slot _) * love N (spin N Slot _) = _
  rw [← map_mul, spin_mul, pin_square, spin_neg, spin_one, map_neg, map_one]

lemma tick_upper : cutM (Tset N) = love N (cutM (upperP N)) := by
  rw [← touchP]; rfl

lemma fullTurn_swaps (i : Axis) :
    twist (fullTurn m B i) (cutM (Tset (CSide m B))ᶜ) = cutM (Tset (CSide m B)) := by
  have h := tickR (shape i) inert (pinLift i) (mirrorX i) Λ
  change twist (fullTurn m B i) (cutM (Tset Λ)) = 1-cutM _ at h
  rw [dim_cut, map_sub, map_one, h]; abel

private lemma same_ref (i : Axis) :
    twist (pinM (CSide m B) i) (cutM (upperP (CSide m B))ᶜ)=cutM (upperP (CSide m B)) := by
  have hp := slide_plus (m:=m) (B:=B) i
  unfold RP.finger pinTrip at hp; rw [Fock.twin, dim_cut, Lat.plane_diag, map_sub, map_one, siteSpin] at hp
  rw [dim_cut, Lat.plane_diag]; exact hp

lemma onsite_swaps (i : Axis) :
    twist (onsite (CSide m B) i) (cutM (Tset (CSide m B))ᶜ)=cutM (Tset (CSide m B)) := by
  have he := congrArg (love Λ) (same_ref (m:=m) (B:=B) i)
  rw [dim_cut, twist_formula, map_mul, map_mul, map_sub, map_one, map_star] at he
  rw [dim_cut, twist_formula, tick_upper]; exact he

-- localize matrix transport on matter sites

def matterSet (N : Side) (S : Finset (Site N)) : Finset (Single N) :=
  univ.filter (fun i => i.1.1 ∈ S)

lemma mem_matterSet (S : Finset (Site N)) (x) : x ∈ matterSet N S ↔ x.1.1 ∈ S := by
  simp [matterSet]

private lemma jump_sites (S T : Finset (Site N)) (M : Equiv.Perm (Site N))
    (e : ∀ x, x ∈ T ↔ M x ∈ S) (B : Site N → Op (SpinIdx × Slot)) :
    let F := love N (jump M B); F * cutM (matterSet N S) = cutM (matterSet N T) * F := by
  intro F; ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩
  simp only [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul, mem_matterSet]
  change jump M B (x,i,j) (y,k,l)*_ = _ * jump M B (x,i,j) (y,k,l)
  by_cases p : M x = y
  · subst y; by_cases h : x ∈ T <;> simp [← e x,h]
  simp [jump_apply, p]

lemma onsite_sites (S : Finset (Site N)) (i : Axis) :
    twist (onsite N i) (cutM (matterSet N S))=cutM (matterSet N S) :=
  Mir.twist_comm _ _ _ (jump_sites S S (Equiv.refl _) (fun _=> Iff.rfl) _)

lemma mirror_sites (i : Axis) (S : Finset (Site (CSide m B))) :
    twist (fullTurn m B i) (cutM (matterSet (CSide m B) S)) =
      cutM (matterSet _ (S.image (matterPoint m B i))) := by
  let M := matterPoint m B i
  apply Mir.twist_comm; rw [fullTurn_matrix, seen, map_neg, neg_mul, mul_neg]
  apply congrArg Neg.neg; apply jump_sites; intro x; constructor
  · intro p; obtain ⟨y,h,rfl⟩ := mem_image.mp p; rw [show tiltM m B i (M y)=y from tiltBack i y]; exact h
  intro h; exact mem_image.mpr ⟨M x,h,tiltBack i x⟩

lemma tradew_eq_love (g : Site (More N) → E) :
    (tradew N g).val=love N (conjG matter (g ∘ node)).val := by
  ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩; by_cases h:x=y <;> by_cases e:i=k <;>
    simp [tradew, loveAt, unityP, conjG, jump_apply, Lat.color, h,e, helix, Matrix.submatrix_apply]

private lemma pinGauge (i : Axis) (g g' : Site (More N) → E) (S : Equiv.Perm (Site N))
    (p : ∀ x, g (node (S x))=g' (node x)) :
    let U := jump S fun _ : Site N => pin i ⊗ₖ (1:Op Slot)
    U * (conjG matter (g ∘ node)).val=(conjG matter (g'∘node)).val * U := by
  intro U; unfold U conjG; simp only [jump_mul, Equiv.refl_trans,
    Equiv.trans_refl, color, op_kron_mul, one_mul, mul_one, Function.comp_apply, p]

lemma commuteGaugeLocal (i : Axis) (g : Site (More N) → E) :
    (onsite N i).val*(tradew N g).val=(tradew N g).val*(onsite N i).val := by
  rw [tradew_eq_love]; let C := conjG matter (g ∘ node); let P := (pinM N i).val
  change love N P * love N C.val=love N C.val * love N P
  have h : P*C.val=C.val*P := pinGauge i _ _ (Equiv.refl _) (fun _=>rfl)
  rw [←map_mul, ←map_mul,h]

lemma commuteGaugeMirror (i : Axis) (g : Site (Domain m B) → E) :
    (fullTurn m B i).val*(tradew (CSide m B) (g ∘ gaugePoint m B i)).val=(tradew (CSide m B) g).val*(fullTurn m B i).val := by
  rw [fullTurn_matrix, tradew_eq_love, tradew_eq_love, ← map_mul, ← map_mul, neg_mul, mul_neg]; congr 2
  rw [seen]; exact pinGauge i _ _ (tiltM m B i) (fun x=> congrArg g ((by
    change revX m B i (node (tiltM m B i x)) = node x; rw [tiltR, rev_back])))

lemma commuteMirror (i : Axis) :
    (onsite (CSide m B) i).val * (fullTurn m B i).val =
      (fullTurn m B i).val * (onsite (CSide m B) i).val := by
  rw [fullTurn_matrix, seen]; let J : Op SpinIdx := pin i
  let D := (fun x : Site Λ => J ⊗ₖ (1:Op Slot)); let M := matterPoint m B i
  change (love Λ (jump (Equiv.refl _) D)) * love Λ (-jump M D) =
    love Λ (-jump M D) * love Λ (jump (Equiv.refl _) D)
  rw [←map_mul, ←map_mul, mul_neg, neg_mul, jump_mul, jump_mul,
    Equiv.trans_refl, Equiv.refl_trans]

end YM.CF.Window
