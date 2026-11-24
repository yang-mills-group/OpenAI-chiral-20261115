import ExactRunning.Step.Equal
/-!
# Gauge laws under the cut

The complete block Hessian is defined off shell in independent link
and frame variables. No stationarity needed for gauge covariance. With cut,
gauge covariance for `staged` gauges (fixed under designated translation);
throughout, fine and coarse gauges are independent (we carry the
extra frame).
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


section switch
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {P : ModeCut m} {Q : ModeCut n} {A : Funds m} {B : Funds n}

def ModeCut.Swivel (P : ModeCut m) (A : Funds m) : Prop :=
  Military A ∧ P.e * A = A * P.e

def pairBlocks (A : Funds m) (B : Funds n) := fromBlocks A 0 0 B

lemma ModeCut.Swivel.pair (h : P.Swivel A) (i : Q.Swivel B) :
    (P.direct Q).Swivel (pairBlocks A B) := by
  constructor
  · constructor
    rw [pairBlocks,fromBlocks_transpose, fromBlocks_multiply]
    simp [h.1.right,i.1.right]
  simp [ModeCut.direct, pairBlocks, fromBlocks_multiply,h.2,i.2]

lemma ModeCut.Swivel.log {X Y : Funds m} (h : P.Swivel A)
    (hp : Aᵀ * X * A = Y) : P.cutlog X = P.cutlog Y := by
  unfold ModeCut.cutlog ModeCut.cutdet; apply congr_arg Real.log (h.1.turn_det _)
  apply h.1.back
  unfold ModeCut.compMat
  simp only [Matrix.add_mul,Matrix.mul_add, Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,
    Matrix.mul_one,h.2, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X A, h.1.pulls hp, Matrix.mul_assoc A, ← Matrix.mul_assoc P.e A,h.2,Matrix.mul_assoc]

lemma epoch (X Y : Matrix m n ℝ) (h : Military A) (i : Military B)
    (p : X * B = A * Y) :
    Aᵀ * (X*Xᵀ) * A = Y * Yᵀ := by
  apply h.back
  rw [Matrix.mul_assoc, i.transpose_cross h p, ← Matrix.mul_assoc, p, Matrix.mul_assoc]

end switch
namespace Latitude
variable {G : Gauge} {m : Side} {D : Latitude}
def staged (D : Latitude) (k : Coats G m) := ∀ i, k (i+D.stepIV m)=k i

lemma staged.solid (g : G.El) : D.staged (solid (n:=m) g) :=
  fun _ => rfl

lemma reinstates {x : BaseSites G m} (h : D.repeats x) :
    D.staged (switchSite x) := by
  intro i; simp only [switch_color]
  apply congr_arg
  ext j
  exact congr_fun (h : x ∘ _ = _) (i,vac,j)

lemma staged.troop {k : Coats G m} (h : D.staged k) :
    (D.cut m (Foot G)).Swivel (troop k) := by
  refine ⟨troop_orthogonal _,cut_of_spin rfl ?_⟩
  apply testers; intro x y
  simp only [← mulVec_mulVec, Stationary.troop, bill_pay, spin, scroll_mulVec]
  congr 1
  apply (gaugeColor (G:=G) (n:=m)).injective
  funext i
  rw [armorG_at,
    show gaugeColor ((armorG k y) ∘ D.shift m (Foot G)) i = gaugeColor (armorG k y) (i+D.stepIV _) from rfl,
    armorG_at, h i]
  rfl

lemma staged.trench {k : Coats G m} (h : D.staged k) :
    (D.cut m (Entry G)).Swivel (trench k) := by
  refine ⟨trench_orthogonal _,cut_of_spin rfl ?_⟩
  apply testers; intro x y
  simp only [← mulVec_mulVec, Stationary.trench, bill_pay, spin, scroll_mulVec]
  congr 1
  apply (edgeColor (G:=G) (n:=m)).injective
  funext i
  rw [armor_at,
    show edgeColor ((armor k y) ∘ D.shift m (Entry G)) i =
      edgeColor (armor k y) (i.1+D.stepIV _,i.2) from rfl,
    armor_at, h i.1]
  rfl

lemma staged.ghost {k : Coats G m} (h : D.staged k) (U : Config G m) :
    (D.cut m (Foot G)).cutlog (tonic (Lattice.gauge k U))
      = (D.cut m (Foot G)).cutlog (tonic U) :=
  h.troop.log (by
    have hk := (troop_orthogonal k).transpose_cross (trench_orthogonal k) (mail_carry k U)
    simpa [tonic] using epoch _ _ (troop_orthogonal k) (trench_orthogonal k) hk)

lemma staged.paidUp (E : Pylon G) {k : Coats G m} (h : D.staged k) {U : Config G m}
    (he : ContDiffAt ℝ ω (burn E.p E.r (Lattice.gauge k U)) 0) :
    epCost D E.p E.r (Lattice.gauge k U)=epCost D E.p E.r U := by
  refine congrArg₂ (fun x y => 1/2 * x-y) (h.trench.log ?_) (h.ghost _)
  rw [epMat,Matrix.mul_add,Matrix.add_mul, flare_carry _ E.paths _ he,
    epoch _ _ (trench_orthogonal k) (troop_orthogonal k) (mail_carry k U)]
  rfl
end Latitude

private lemma billsM_pair {X Y ι κ : Type}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (i : Module.Basis ι ℝ X) (j : Module.Basis κ ℝ Y)
    (A : X→L[ℝ] X) (B : Y→L[ℝ] Y) :
    billsM (i.prod j) (i.prod j) (A.prodMap B) =
      pairBlocks (billsM i i A) (billsM j j B) := by
  apply bill_eq (i.prod j);intro x
  rw [bill_at]
  simp only [bill_at,pairBlocks,halvesC,Matrix.fromBlocks_mulVec,Sum.elim_comp_inl,
    Sum.elim_comp_inr, zero_mulVec,add_zero, zero_add]
  rfl
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


variable (X) (r : ℝ)
abbrev _root_.ExactRunning.ridge (r : ℝ) := Latitude.native r
/-- Latitude for incoming endpoint. Use the coarse radius (`ridge r` outgoing)
but applied to dilated fine momentum. For native radius `d` on fine side, use
`r=L*d`, see `Latitude.incoming`. -/
def back : Latitude := ⟨X.L,r⟩

def bCut (m : Side) : ModeCut (Bodies G m (X.up m)) :=
  ((X.back r).cut (X.up m) (Entry G)).direct ((ridge r).cut m (Foot G))

def together (m : Side) : ModeCut (X.Drum m) :=
  (X.bCut r m).direct ((ridge r).cut m (Entry G))

def zCost (b : Joint G m (X.up m)) (v : Config G m) :=
  (1/2) * (X.together r m).cutlog (X.vibrant b v) -
   ((X.back r).cut (X.up m) (Foot G)).cutlog (tonic b.1) -
   ((ridge r).cut m (Foot G)).cutlog (tonic v)

def hCost (b : Joint G m (X.up m)) (v : Config G m) :=
  (1/2) * (X.bCut r m).cutlog (X.high b v) -
   ((X.back r).cut (X.up m) (Foot G)).cutlog (grenade X.μ b.1)

def zEnergy (z : Point G m (X.up m)) :=
  X.zCost r (Stationary.extend z.2) (input _ _ z.1)

def hEnergy (z : Point G m (X.up m)) :=
  X.hCost r (Stationary.extend z.2) (input _ _ z.1)

variable {k : Coats G (X.up m)} {u : Coats G m} {r}
lemma tactics_i (hk : (X.back r).staged k) (hu : (ridge r).staged u) :
    (X.bCut r m).Swivel (tactics k u) := by
  rw [tactics,helmets, armUp,billsM_pair]
  exact hk.trench.pair hu.troop

variable (k u)
abbrev sign := wages (X.S m) k u

lemma seating (y : X.Hall m) :
    Stationary.extend (armUp k u y.1)*X.sign k u 1 = X.sign k u (Stationary.extend y.1) := by
  rw [sign,arm_root,mul_one]

lemma regalia {v : Config G m} {b : Joint G m (X.up m)}
    (h : ContDiffAt ℝ ω (X.sitting (X.sign k u b) (Lattice.gauge u v)) 0) :
    let T := pairBlocks (tactics k u) (trench u)
    Tᵀ * X.vibrant (X.sign k u b) (Lattice.gauge u v) * T = X.vibrant b v := by
  have hh : X.sitting (X.sign k u b) (Lattice.gauge u v) ∘
      ((armUp k u).prodMap (armor u)) = X.sitting b v := by
    funext y
    change X.J m (input G m (armor u y.2) * _) (Stationary.extend (armUp k u y.1) * wages _ _ _ b) = _
    rw [arm_root,armor_go]
    exact root_wages _ _ X.branches _ _ _ _ _ E.paths _
  have hB := (damage_rate (X.podium m) (X.podium m) _ ((armUp k u).prodMap (armor u)) h).symm
  rw [hh, billsM_pair] at hB
  dsimp only [vibrant]
  rw [Matrix.mul_add, Matrix.add_mul];refine congr_arg₂ (·+·) hB ?_
  rw [pairBlocks,fromBlocks_transpose,fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,transpose_zero,zero_add,add_zero,
    epoch _ _ (trench_orthogonal u) (troop_orthogonal u) (mail_carry u v)]
  have he : (tactics k u)ᵀ * ((X.settings (X.sign k u b))ᵀ * X.settings (X.sign k u b)) *
      tactics k u = (X.settings b)ᵀ * X.settings b := by
    have ht : (X.settings (X.sign k u b))ᵀ * troop k = tactics k u * (X.settings b)ᵀ := by
      rw [settings,settings,transpose_mul, transpose_mul,transpose_transpose, transpose_transpose,
        Matrix.mul_assoc,show (X.sign k u b).1=Lattice.gauge k b.1 from rfl,mail_carry k b.1, ← Matrix.mul_assoc,
        (tactics_orthogonal k u).transpose_cross (trench_orthogonal k) (rear_tactics k u), Matrix.mul_assoc]
    simpa only [transpose_transpose] using epoch _ _ (tactics_orthogonal k u) (troop_orthogonal k) ht
  rw [he]

variable {k u}

lemma z_swivel (hk : (X.back r).staged k) (hu : (ridge r).staged u)
    {b : Joint G m (X.up m)} {v : Config G m}
    (h : ContDiffAt ℝ ω (X.sitting (X.sign k u b) (Lattice.gauge u v)) 0) :
    X.zCost r (X.sign k u b) (Lattice.gauge u v) = X.zCost r b v := by
  rw [zCost,zCost]
  refine congrArg₂ ((·-·):ℝ→ℝ→ℝ) (congrArg₂ ((·-·):ℝ→ℝ→ℝ)
    (congr_arg ((1/2:ℝ)*·) (((X.tactics_i hk hu).pair hu.trench).log (X.regalia _ _ h))) ?_) ?_
  · exact hk.ghost _
  exact hu.ghost _

lemma h_swivel (hk : (X.back r).staged k) (hu : (ridge r).staged u)
    {b : Joint G m (X.up m)} {v : Config G m}
    (hb : Explosives (X.S m) (X.choice m) 1 b)
    (hw : Explosives (X.S m) (X.choice m) 1 (X.sign k u b))
    (h : ContDiffAt ℝ ω (X.sitting (X.sign k u b) (Lattice.gauge u v)) 0) :
    X.hCost r (X.sign k u b) (Lattice.gauge u v) = X.hCost r b v := by
  rw [hCost,hCost,X.high_eq,X.high_eq]
  refine congrArg₂ ((·-·):ℝ→ℝ→ℝ)
    (congr_arg ((1/2:ℝ)*·) ((X.tactics_i hk hu).log (honors_status X.branches _ _ _ _ _ E.paths hb hw X.hμ ?_)))
    (hk.troop.log (hk.troop.1.back (battery _ X.hμ k).2))
  let J := ContinuousLinearMap.inl ℝ (Vault G m (X.up m)) (Link G m)
  let v₁ := Lattice.gauge u v
  have hp : ContDiffAt ℝ ω (X.sitting (X.sign k u b) v₁) (J 0) := by rw [map_zero];exact h
  refine (hp.comp 0 J.contDiff.contDiffAt).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun x=> by simp only [Function.comp_apply, sitting,J,
    ContinuousLinearMap.inl_apply, input_zero, one_mul];rfl

end BlockTie
end ExactRunning
