import GaugeFieldConstruction.Altars

/-!
# Formal derivative data on the comparison system
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction
open Cauchy Row Record Conj Function Submodule Finset U1 Raw LabelAction
open Matter (Generation FlavorIndex)
open scoped BigOperators
namespace Calibration
open Floor
/-- Jet coordinates without restriction on engineering grade. This is not `U_6`. -/
abbrev Shell := ℂ × J g × Fragment (J f) × Fragment (J x)
section
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
def mv (X : A→ₗ[ℂ]B) : Fragment A →ₗ[ℂ] Fragment B := LinearMap.pi fun i => X ∘ₗ LinearMap.proj i
lemma mv_at (X : A→ₗ[ℂ]B) (x i) : mv X x i=X (x i) := rfl
end

def shells (i : Floor) : UV i →ₗ[ℂ] Shell := LinearMap.prodMap LinearMap.id (LinearMap.prodMap (SG i).subtype
  (LinearMap.prodMap (mv (A:=UF i) (B:=J f) (SF i).subtype) (mv (A:=UX i) (B:=J x) (SX i).subtype)))
lemma shell_in (i : Floor) : Injective (shells i) := by
  intro u v h
  obtain ⟨g,k⟩:= Prod.mk.inj h; obtain ⟨b,c⟩:= Prod.mk.inj k; obtain ⟨y,w⟩:=Prod.mk.inj c
  exact Prod.ext g (Prod.ext (Subtype.ext b) (Prod.ext (funext fun i=>Subtype.ext (congr_fun y i)) (funext fun i=>Subtype.ext (congr_fun w i))))

lemma shell_lift (i : Floor) : shells five ∘ₗ lift i=shells i := LinearMap.ext fun _ => rfl

def P (k : Axis) : Module.End ℂ Shell := LinearMap.prodMap 0 (LinearMap.prodMap (P_g k)
  (LinearMap.prodMap (mv (P_f k)) (mv (A:=J Row.x) (B:=J Row.x) (P_x k))))
-- P restricted through degree 4

def deriv (k : Axis) : UV four →ₗ[ℂ] UV five := LinearMap.prodMap 0 <| LinearMap.prodMap
    (LinearMap.restrict (P_g k) (fun _ h => dG k h))
    (LinearMap.prodMap (mv (A:=UF four) (B:=UF five) (LinearMap.restrict (P_f k) (fun _ h=>dF k h)))
      (mv (A:=UX four) (B:=UX five) (LinearMap.restrict (P_x k) (fun x h=> by rw [show x=0 from (Submodule.mem_bot ℂ).mp (show x∈(⊥:Submodule ℂ _) from h)]; simp))))
lemma scene (k : Axis) : shells five ∘ₗ deriv k=P k ∘ₗ shells four:=LinearMap.ext fun _=>rfl
lemma exchanges (k i : Axis) (x : Shell) : P k (P i x) = P i (P k x) :=by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext (funext fun b=>?_) (funext fun b=>?_)))
  · change (0:Module.End ℂ ℂ) (P i x).1 = (0:Module.End ℂ ℂ) (P k x).1; simp
  · exact gc k i x.2.1
  · change P_f k _=P_f i _; exact fc k i (x.2.2.1 b)
  change P_x k (P_x i (x.2.2.2 b))= P_x i (P_x k (x.2.2.2 b)); exact xc k i (x.2.2.2 b)
lemma hue_frame {M Q : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup Q] [Module ℂ Q]
    (X : M→ₗ[ℂ]Q) (p : Flavor) (i : Fragment M) : mv X (hues p i)=hues p (mv X i) := by
  ext1 j; change X (pay (p⁻¹.bit j) (i _)) = pay (p⁻¹.bit j) (X _); cases p⁻¹.bit j <;> simp
lemma white_d (k : Axis) (x : UV four) (h : white x) : white (deriv k x) := by
  intro g; have ht : flavors five g (deriv k x)=deriv k (flavors four g x) := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · let X : UF four →ₗ[ℂ] UF five := LinearMap.restrict (P_f k) (fun _ h=>dF k h)
      exact (hue_frame (M:=UF four) (Q:=UF five) X g x.2.2.1).symm
    let X : UX four →ₗ[ℂ] UX five := LinearMap.restrict (P_x k) (fun _ h=> (show SX four ≤ comap (P_x k) (SX five) from bot_le) h)
    exact (hue_frame (M:=UX four) (Q:=UX five) X g x.2.2.2).symm
  rw [ht,h g]

private lemma moveP {A B} {H : Record A B} {M N : Submodule ℂ (J A)} (G : Carries H M) (B : Carries H N)
    (h : ∀ i,M≤comap (H.P i) N) (k : Axis) (s) (v : M) :
    let D (i : Axis) : M→ₗ[ℂ]N:= LinearMap.restrict (H.P i) (fun _ x=> h i x)
    B.moves s (D k v)=pay (s.flip k) (D (s.perm k) (G.moves s v)) := by
  intro D; apply Subtype.ext; apply ext_jet H.faith; intro w
  obtain ⟨u,H'⟩:= H.permit s w
  rw [←B.transit H']
  change H.tester u (H.P k v.val)= H.tester w _
  rw [H.atP k _ _ s w u H' false (G.transit H' v)]
  cases he:s.flip k
  · exact rfl
  change -(H.tester w _) = H.tester w (-_); rw [map_neg]; rfl

lemma spin_d (k : Axis) (s : Signed) (x : UV four) : spinFrame five s (deriv k x) =
    pay (s.flip k) (deriv (s.perm k) (spinFrame four s x)) := by
  apply Prod.ext
  · change (0:ℂ)=(pay (α:=UV five) (s.flip k) _).1; cases s.flip k; rfl
    exact (neg_zero).symm
  apply Prod.ext
  · have hp:= moveP (gauge four).toCarries (gauge five).toCarries dG k s x.2.1; dsimp only at hp
    cases he:s.flip k <;> rw [he] at hp <;> exact hp
  refine Prod.ext (funext fun i=>?_) (funext fun i=>?_)
  · have hp:=moveP (matter four).toCarries (matter five).toCarries dF k s (x.2.2.1 (rev s i))
    dsimp only at hp; cases he:s.flip k <;> rw [he] at hp <;> exact hp
  have hp:=moveP (mixed four).toCarries (mixed five).toCarries (fun _=>bot_le) k s (x.2.2.2 (rev s i))
  dsimp only at hp; cases he:s.flip k <;> rw [he] at hp <;> exact hp

lemma real_d (k) (x : UV four) : shade five (deriv k x) = deriv k (shade four x) := by
  refine Prod.ext (map_zero bar) (Prod.ext ?_ (Prod.ext (funext fun i=> ?_) (funext fun i=>?_)))
  · exact Subtype.ext (G_tr k x.2.1.val)
  · exact Subtype.ext (f_tr k (x.2.2.1 i).val)
  exact Subtype.ext (x_tr k (x.2.2.2 i).val)

abbrev SymT := invariant Raw.symAct four
abbrev OneW := invariant Raw.v five
abbrev BothV := invariant vsAct five
-- mathematical maps

def push : SymT→ₗ[ℂ] (VS → UV five) := LinearMap.pi fun k => deriv k.1 ∘ₗ LinearMap.proj k.2 ∘ₗ SymT.subtype
lemma carriesP (x : SymT) : push x∈BothV := by
  constructor
  · intro i; exact ⟨rfl, white_d i.1 _ (x.property.1 i.2).2⟩
  rintro ⟨k,j⟩ s
  change spinFrame five s (deriv k (x.val j))= pay ((s.flip k).xor (symAct.cost s j)) (deriv (s.perm k) (x.val _))
  rw [spin_d,x.property.2 j s,← pay_comp (α:=UV five)]; cases symAct.cost s j 
  · rfl
  exact congr_arg (pay (α:=UV five) (s.flip k)) (map_neg (deriv (s.perm k)) (x.val (symAct.move s j)))

def rowSum : BothV →ₗ[ℂ] Axis → UV five := LinearMap.pi fun j=> (∑ i:Axis, LinearMap.proj ((i, ordered i j):VS)) ∘ₗ BothV.subtype
lemma rowAt (X : BothV) (j) : rowSum X j=∑ i: Axis,X.val (i,ordered i j) := by
  change (∑ i:Axis,(LinearMap.proj ((i,ordered i j):VS): (VS→UV five) →ₗ[ℂ] UV five)) X.val= _; rw [LinearMap.sum_apply]; rfl
lemma may_row (X : BothV) : rowSum X∈OneW := by
  constructor
  · intro i; constructor
    · let L:=LinearMap.fst ℂ ℂ (UG five × Fragment (UF five) × Fragment (UX five)); change L (rowSum X i)=0
      rw [rowAt,map_sum]; apply Finset.sum_eq_zero; intro b _; exact (X.property.1 _).1
    intro s; rw [rowAt,map_sum]; exact Finset.sum_congr rfl fun _ _=> (X.property.1 _).2 s
  intro i s; rw [rowAt,map_sum,rowAt]; change _ = pay (s.flip i) _
  rw [Record.feePay (M:=UV five) (T:=Axis)]
  conv_rhs=> rw [← Equiv.sum_comp s.perm]
  apply Finset.sum_congr rfl
  intro j _
  rw [X.property.2]
  change pay ((s.flip j).xor (symAct.cost s _)) (X.val (s.perm j,symAct.move s _))=pay _ _
  rw [fee_turn,sym_turn]
  cases s.flip j <;> cases s.flip i <;> rfl
  -- adjust

def gradient : SymT →ₗ[ℂ] BothV := push.codRestrict _ carriesP
def divergence : SymT →ₗ[ℂ] OneW := (rowSum.codRestrict _ may_row) ∘ₗ gradient
@[simp] lemma component_div (t : SymT) j : (divergence t).val j=∑ i : Axis, deriv i (t.val (ordered i j)):=
  rowAt (gradient t) j
end Calibration
end YM.GaugeFieldConstruction
