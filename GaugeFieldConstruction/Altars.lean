import GaugeFieldConstruction.Prescription

/-!
# U1. Tensor spaces with flavor & H charge, on the full
  symbol space. Pack isomorphism (both species).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Cauchy Row Record Conj LabelAction U1 Raw
open Matter (Generation FlavorIndex)
namespace Calibration
open Floor
variable {d : Floor} {α V P : Type*}

set_option synthInstance.maxSize 5000

def centered (v : UV d) : Prop := v.1=0
def white (v : UV d) : Prop := ∀ p, flavors d p v=v

def invariant (A : Labels α) (d : Floor) : Submodule ℂ (α → UV d) where
  carrier:={x| (∀ i, centered (x i) ∧ white (x i)) ∧ ∀ i s,
    spinFrame d s (x i)=pay (A.cost s i) (x (A.move s i))}
  zero_mem':= by
    refine ⟨fun i=>⟨rfl,fun p=>map_zero _⟩, ?_⟩; intro i s; change spinFrame d s 0 = pay _ 0
    rw [map_zero]; exact (pay_zero (α:=UV d) _).symm
  add_mem':= by
    intro u v hu hv
    refine ⟨fun i=>⟨?_,fun s=>?_⟩,fun i s=>?_⟩
    · change (u i).1+(v i).1=0; rw [(show (u i).1=0 from (hu.1 i).1),(show (v i).1=0 from (hv.1 i).1),add_zero]
    · simp only [Pi.add_apply,map_add,(hu.1 i).2 s,(hv.1 i).2 s]
    simp only [Pi.add_apply, map_add,hu.2 i s,hv.2 i s]; exact (pay_add _ (u (A.move s i)) _).symm
  smul_mem':= by
    intro a u hu
    refine ⟨fun i=>⟨?_,fun s=>?_⟩,fun i s=>?_⟩
    · change a • (u i).1=0; rw [(show (u i).1=0 from (hu.1 i).1),smul_zero]
    · simp only [Pi.smul_apply, map_smul,(hu.1 i).2 s]
    simp only [Pi.smul_apply, map_smul,hu.2 i s]; cases A.cost s i <;> simp
    exact smul_neg a (u (A.move s i))

section Eval
variable [AddCommGroup V] [modV : Module ℂ V]

/-- Precisely the complete sum over generations has flavor white. -/
lemma blank_flavor (v : Bool→ V) (g : Flavor) : hues g (Flavor.bundle_ v)=Flavor.bundle_ v := by
  funext i
  obtain ⟨j,hj⟩ : ∃ j, g.reprice j=i := ⟨g⁻¹.reprice i, by simpa only [inv_inv] using reverses g⁻¹ i⟩
  rw [←hj,plate, Flavor.keeps g]
lemma faded (v : Fragment V) (h : ∀ g,hues g v=v) : v= Flavor.bundle_ fun i=> v (i,0,0) := by
  apply Flavor.settles
  intro g i; rw [← plate, h]
end Eval
variable (d)

def centered_g : UV d →ₗ[ℂ] J Row.g := (SG d).subtype ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
def centered_f (i : FlavorIndex) : UV d →ₗ[ℂ] J f := (SF d).subtype ∘ₗ LinearMap.proj i ∘ₗ
  LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
def centered_x (i : FlavorIndex) : UV d →ₗ[ℂ] J x := (SX d).subtype ∘ₗ LinearMap.proj i ∘ₗ
  LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _

def first (b : Bool) : FlavorIndex := (b,0,0)
lemma rev_first (s b): rev s (first b)=first b := by cases h:signBit s<;>simp [rev,h, first]

variable (A : Labels α)
section Assemble
lemma retain_f (v : invariant A d) (b : Bool) : (fun i=>centered_f d (first b) (v.val i))∈ph.allowed A (SF d) := by
  let p (i : α) := (v.val i).2.2.1 (first b)
  change (fun i=>(p i).val)∈_
  refine ⟨((matter d).toCarries.turn_field _ _).mpr (fun s i=> ?_),fun i _=>(p i).property⟩ -- order
  have he (z : UV d) : (spinFrame d s z).2.2.1 (first b)=(matter d).moves s (z.2.2.1 (first b)) := by
    change (matter d).moves s (z.2.2.1 _) = _; rw [rev_first]
  have h:= congr_arg (fun z : UV d=>z.2.2.1 (first b)) (v.property.2 i s)
  rw [he] at h
  cases hz : A.cost s i <;> rw [hz] at h <;> exact h
lemma retain_x (v : invariant A d) (b : Bool) : (fun i=>centered_x d (first b) (v.val i))∈recX.allowed A (SX d) := by
  let p (i : α) := (v.val i).2.2.2 (first b)
  change (fun i=>(p i).val)∈_
  refine ⟨((mixed d).toCarries.turn_field _ _).mpr (fun s i=> ?_),fun i _=>(p i).property⟩
  have he (z : UV d) : (spinFrame d s z).2.2.2 (first b)=(mixed d).moves s (z.2.2.2 (first b)) := by
    change (mixed d).moves s (z.2.2.2 _) = _; rw [rev_first]
  have h:= congr_arg (fun z : UV d=>z.2.2.2 (first b)) (v.property.2 i s)
  rw [he] at h
  cases hz : A.cost s i <;> rw [hz] at h <;> exact h
lemma retain_g (v : invariant A d) : (fun i=>centered_g d (v.val i))∈ recG.allowed A (SG d) := by
  let p (i : α) := (v.val i).2.1
  change (fun i=>(p i).val)∈_
  refine ⟨((gauge d).toCarries.turn_field _ _).mpr (fun s i=> ?_),fun i _=>(p i).property⟩
  have h:=congr_arg (fun z:UV d=> z.2.1) (v.property.2 i s)
  cases hz:A.cost s i <;> rw [hz] at h <;> exact h

abbrev Trio := ((recG.allowed A (SG d)) × ((Bool→(ph.allowed A (SF d))) × (Bool→(recX.allowed A (SX d)))))

def forward (v : invariant A d) : Trio d A := (⟨_,retain_g d A v⟩,fun x=>⟨_,retain_f d A v x⟩,fun x=>⟨_,retain_x d A v x⟩)
-- ↑T → invariant A d
private def fine {H : Record V P} {U} (v : H.allowed A U) (i : α) : U := ⟨_,v.property.2 i (Set.mem_univ _)⟩
private lemma fine_rot {H : Record V P} {U} (B : Carries H U) (v : H.allowed A U) (s i) :
    B.moves s (fine A v i)=pay (A.cost s i) (fine A v (A.move s i)) := (B.turn_field A _).mp v.property.1 s i
private lemma recharge {R : Record V P} {H : Flip V} {U} (T : Grade R H U) (p : Bool→R.allowed A U) (s : Signed) (i : α) :
    onFrame T s (Flavor.bundle_ fun b=>fine A (p b) i)=pay (A.cost s i) (Flavor.bundle_ (fun b=> fine A (p b) (A.move s i))) := by
  funext j
  change T.moves s ((Flavor.bundle_ _) (rev s j)) = pay (A.cost s i) (Flavor.bundle_ _) j
  cases he:j with | mk x y =>
  unfold Flavor.bundle_
  cases hz:A.cost s i <;> cases hu:signBit s <;> by_cases q : y.1=y.2
  all_goals simp only [rev,hu,Bool.false_eq_true,↓reduceIte,pay_true,pay_false,Pi.neg_apply]
  all_goals first | (simp only [q, ↓reduceIte]; exact (by simpa only [hz,pay_false,pay_true] using fine_rot A T.toCarries (p x) s i)) |
    (simp only [if_neg q,if_neg (Ne.symm q), map_zero, neg_zero])

def backward (p : Trio d A) : invariant A d :=
  ⟨fun i => (0, fine A p.1 i,Flavor.bundle_ fun b=> fine A (p.2.1 b) i,Flavor.bundle_ fun b=>fine A (p.2.2 b) i), by
    refine ⟨fun i=>⟨rfl,fun g=>?_⟩,fun i s=> ?_⟩
    · exact Prod.ext rfl (Prod.ext rfl (Prod.ext (blank_flavor (V:=UF d) (fun b => fine A (p.2.1 b) i) g)
          (blank_flavor (V:=UX d) (fun b=>fine A (p.2.2 b) i) g)))
    have hg:=fine_rot A (gauge d).toCarries p.1 s i
    have hf:=recharge A (matter d) p.2.1 s i
    have hx:=recharge A (mixed d) p.2.2 s i
    cases h : A.cost s i <;> rw [h] at hg hf hx <;> refine Prod.ext ?_ (Prod.ext hg (Prod.ext hf hx))
    · rfl
    exact (neg_zero).symm⟩

def package (d) (A : Labels α) : invariant A d ≃ₗ[ℂ] Trio d A where
  toFun := forward d A; invFun := backward d A
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p:= by
    apply Subtype.ext
    funext i
    have h := (p.property.1 i)
    refine Prod.ext (Eq.symm (show (p.val i).1=0 from h.1)) (Prod.ext rfl (Prod.ext ?_ ?_))
    · have he v := congr_arg (fun z : UV d=> z.2.2.1) (h.2 v)
      exact (faded (V:=(UF d)) (p.val i).2.2.1 (fun v=> he v)).symm
    have he v:= congr_arg (fun z : UV d=> z.2.2.2) (h.2 v)
    exact (faded (V:=(UX d)) (p.val i).2.2.2 (fun v=>he v)).symm
end Assemble
end Calibration
end YM.GaugeFieldConstruction
