import GaugeFieldConstruction.ZActive
/-!
# Active representation descends, costs at SO. Proper restrictions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Calibration.RawBank Floor Cauchy Row Phys Conj Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles
section prod
variable {α : Type*} {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

lemma sent {f : ℝ→ A × B} {p : A × B} {t : ℝ} (h : Sends (fun x=> (f x).1) t p.1)
    (u : Sends (fun x=> (f x).2) t p.2) : Sends f t p := by
  intro L
  have he (p : A × B): L p=L (p.1,0)+L (0,p.2):=by rw [← map_add]; congr; simp
  unfold Function.comp; conv_lhs =>skip -- adjusts
  -- rewrite
  rw [show (fun i=>L (f i)) = fun i=> L ((f i).1,0)+L (0,(f i).2) from funext fun i=>he _,he]
  exact (h (L ∘ₗ LinearMap.inl ..)).add (u (L ∘ₗ LinearMap.inr ..))
lemma sorted [Fintype α] [DecidableEq α] {f : ℝ→α→ A} {p : α→A} {t} (h : ∀ i,Sends (fun x=> f x i) t (p i)): Sends f t p := by
  intro L
  have he v: L v=∑ i:α,L (Pi.single i (v i)):= by rw [← map_sum]; apply congr_arg L; ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]
  unfold Function.comp
  rw [show (fun x=> L (f x)) = fun x=> ∑ i:α, L (Pi.single i (f x i)) from funext fun x=>he _,he]
  exact HasDerivAt.fun_sum (fun i _=> h i (L ∘ₗ LinearMap.single ℂ (fun _=> A) i))
lemma cprod {f : SO→ A × B} (h : ∀ l : A→ₗ[ℂ]ℂ, Continuous fun x=>l (f x).1) (g : ∀ l:B→ₗ[ℂ]ℂ, Continuous fun x=>l (f x).2) : ∀ L:A×B→ₗ[ℂ]ℂ, Continuous fun x=> L (f x) := by
  intro L
  have he p:L p=L (p.1,0)+L (0,p.2):=by rw [← map_add]; congr; simp
  rw [show (fun x=> L (f x))=fun x=> L ((f x).1,0)+L (0,(f x).2) from funext fun x=>he _]
  exact (h (L ∘ₗ LinearMap.inl ..)).add (g (L ∘ₗ LinearMap.inr ..))
lemma cvec [Fintype α] [DecidableEq α] {f : SO→ α→ A} (h : ∀ a,∀ l:A→ₗ[ℂ]ℂ, Continuous fun x=> l (f x a)): ∀ l:(α → A)→ₗ[ℂ]ℂ, Continuous fun x=> l (f x) := by
  intro L
  have he p:L p=∑ i:α, L (Pi.single i (p i)) := by rw [← map_sum]; apply congr_arg L; ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]
  rw [show (fun x=> L (f x))=fun x=> ∑ i:α, L (Pi.single i (f x i)) from funext fun x=>he _]
  exact continuous_finsetSum _ fun a _=> h a (L ∘ₗ LinearMap.single ℂ (fun _=> A) a)
end prod

abbrev rhoG (d):= Angles.repr (DeckG d) (gCard d) (leavesG d) (gauge d).fin
abbrev rhoF (d):= Angles.repr (DeckF d) (fCard d) (leavesF d) (matter d).fin
abbrev rhoX (d a b):= Angles.repr (DeckX d) (xCard d a b) (leavesX d a b) (mixed d).fin
variable (D : District) {d : Floor}

def Tag (d : Floor) (s : SO) : Module.End ℂ (UV d) := LinearMap.prodMap LinearMap.id (LinearMap.prodMap (if D.g then rhoG d s else LinearMap.id)
  (LinearMap.prodMap
    (LinearMap.pi fun i:FlavorIndex=> (if D.f i.1 then rhoF d s else LinearMap.id) ∘ₗ LinearMap.proj i)
    (LinearMap.pi fun i:FlavorIndex=> rhoX d D.g (D.f i.1) s ∘ₗ LinearMap.proj i)))
lemma takeF (s i) (x:UV d): (Tag D d s x).2.2.1 i= (if D.f i.1 then rhoF d s else LinearMap.id) (x.2.2.1 i):= rfl
lemma takeG (s) (x:UV d): (Tag D d s x).2.1= (if D.g then rhoG d s else LinearMap.id) (x.2.1):=rfl
lemma takeX (s i) (x:UV d): (Tag D d s x).2.2.2 i=rhoX d D.g (D.f i.1) s (x.2.2.2 i):=rfl

def ledger (D: District) (d) : SO →* Module.End ℂ (UV d) where
  toFun:=Tag D d
  map_one':=by
    apply LinearMap.ext; intro x
    change Tag D d 1 x=x; apply Prod.ext
    · rfl
    apply Prod.ext
    · rw [takeG,map_one]; cases D.g <;> rfl
    apply Prod.ext
    · ext1 i; rw [takeF,map_one]; cases D.f i.1 <;> rfl
    ext1 i; rw [takeX,map_one,Module.End.one_apply]
  map_mul' s t:=by
    apply LinearMap.ext; intro x; rw [Module.End.mul_apply]
    apply Prod.ext
    · simp only [Tag,LinearMap.prodMap_apply,LinearMap.id_apply]
    apply Prod.ext
    · rw [takeG,takeG,takeG,map_mul]; cases D.g <;> rfl
    apply Prod.ext
    · ext1 i; rw [takeF,takeF,takeF,map_mul]; cases D.f i.1 <;> rfl
    ext1 i; rw [takeX,takeX,takeX,map_mul]; rfl

-- explicit UF instance, harmonize
local instance iA (d:Floor) :AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J f) _ _ _ (SF d)
local instance iG (d:Floor) :AddCommGroup (UG d):= @Submodule.addCommGroup ℂ (J g) _ _ _ (SG d)
local instance iX (d:Floor) :AddCommGroup (UX d):= @Submodule.addCommGroup ℂ (J Row.x) _ _ _ (SX d)

lemma cost (u : Rotors) (x : UV d) (t) : Sends (fun t=>ledger D d (rise u t) x) t (enlarged D d u (ledger D d (rise u t) x)) := by
  change Sends (fun t=> Tag D d (rise u t) x) t (enlarged D d u (Tag D d (rise u t) x))
  apply sent
  · intro L; change HasDerivAt (fun _ : ℝ=>L (x.1)) (L 0) _; rw [map_zero]; exact hasDerivAt_const ..
  apply sent
  · rw [ruleG,takeG]; simp_rw [takeG]; cases D.g
    · intro l; change HasDerivAt (fun _ : ℝ=>l x.2.1) (l ((0:ℂ) • _)) t; rw [zero_smul,map_zero]; exact hasDerivAt_const ..
    simp only [activates, one_smul, ↓reduceIte]; exact pressure (DeckG d) (gCard d) (leavesG d) (gauge d).fin u x.2.1 t
  apply sent
  · apply sorted; intro i; rw [ruleF,takeF]; simp_rw [takeF]; unfold EF; cases D.f i.1
    · simp only [activates,Bool.false_eq_true,↓reduceIte, LinearMap.id_apply, LinearMap.smul_apply, zero_smul,LinearMap.zero_apply]; intro l; simp; exact hasDerivAt_const ..
    simp only [activates, ↓reduceIte,one_smul]; exact pressure (DeckF d) (fCard d) (leavesF d) (matter d).fin u (x.2.2.1 i) t
  apply sorted; intro i; rw [ruleX,takeX]; simp_rw [takeX]; exact pressure (DeckX d) (xCard d _ _) (leavesX d D.g (D.f i.1)) (mixed d).fin u (x.2.2.2 i) t
lemma continu (x : UV d): ∀ L:UV d →ₗ[ℂ]ℂ, Continuous fun s=> L (ledger D d s x) := by
  change ∀ L:UV d→ₗ[ℂ]ℂ,Continuous fun s=> L (Tag D d s x)
  apply cprod
  · intro l; change Continuous fun _ : SO=> l x.1; exact continuous_const
  apply cprod
  · simp_rw [takeG]; cases D.g
    · intro l; change Continuous fun _:SO=> l x.2.1; exact continuous_const
    intro l; exact Angles.cont (DeckG d) (gCard d) (leavesG d) (gauge d).fin x.2.1 l
  apply cprod
  · apply cvec; intro i l
    simp_rw [takeF]; cases D.f i.1
    · change Continuous fun _ : SO=> l (x.2.2.1 i); exact continuous_const
    exact Angles.cont (DeckF d) (fCard d) (leavesF d) (matter d).fin (x.2.2.1 i) l
  apply cvec; intro i l; exact Angles.cont (DeckX d) _ (leavesX d D.g (D.f i.1)) (mixed d).fin (x.2.2.2 i) l
end YM.GaugeFieldConstruction.Stage
