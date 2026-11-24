import GaugeFieldConstruction.GlowCell
/-!
# Active representation descends, costs at Lorentz . Proper restrictions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Mink Complex Calibration Calibration.RawBank Floor Cauchy Row Phys Conj Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles
section prod
variable {α : Type*} {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

lemma cprodL {f : Lorentz → A × B} (h : ∀ l : A→ₗ[ℂ]ℂ, Continuous fun x=>l (f x).1) (g : ∀ l:B→ₗ[ℂ]ℂ, Continuous fun x=>l (f x).2) : ∀ L:A×B→ₗ[ℂ]ℂ, Continuous fun x=> L (f x) := by
  intro L
  have he p:L p=L (p.1,0)+L (0,p.2):=by rw [← map_add]; congr; simp
  rw [show (fun x=> L (f x))=fun x=> L ((f x).1,0)+L (0,(f x).2) from funext fun x=>he _]
  exact (h (L ∘ₗ LinearMap.inl ..)).add (g (L ∘ₗ LinearMap.inr ..))
lemma cvecL [Fintype α] [DecidableEq α] {f : Lorentz → α→ A} (h : ∀ a,∀ l:A→ₗ[ℂ]ℂ, Continuous fun x=> l (f x a)): ∀ l:(α → A)→ₗ[ℂ]ℂ, Continuous fun x=> l (f x) := by
  intro L
  have he p:L p=∑ i:α, L (Pi.single i (p i)) := by rw [← map_sum]; apply congr_arg L; ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]
  rw [show (fun x=> L (f x))=fun x=> ∑ i:α, L (Pi.single i (f x i)) from funext fun x=>he _]
  exact continuous_finsetSum _ fun a _=> h a (L ∘ₗ LinearMap.single ℂ (fun _=> A) a)
end prod

def GeoSphereL : Meridian (gCard four):= (PilotCellL.spar PilotCellL).spar (PilotCellL.spar PilotCellL)
def FlavorScopeL : Meridian (fCard four):= PilotCellL.sail (PilotCellL.spar (PilotCellL.sail PilotCellL))
def MixScopeL (a b): Meridian (xCard four a b):= stayL Empty

abbrev rhoGL := Angles.jetMeridianL (DeckG four) (gCard four) GeoSphereL (leavesG four) (gauge four).fin
abbrev rhoFL := Angles.jetMeridianL (DeckF four) (fCard four) FlavorScopeL (leavesF four) (matter four).fin
abbrev rhoXL (a b):= Angles.jetMeridianL (DeckX four) (xCard four a b) (MixScopeL a b) (leavesX four a b) (mixed four).fin
variable (D : District) {d : Floor}

def TagL (s : Mink.Lorentz) : Module.End ℂ (UV four) := LinearMap.prodMap LinearMap.id (LinearMap.prodMap (if D.g then rhoGL s else LinearMap.id)
  (LinearMap.prodMap
    (LinearMap.pi fun i:FlavorIndex=> (if D.f i.1 then rhoFL s else LinearMap.id) ∘ₗ LinearMap.proj i)
    (LinearMap.pi fun i:FlavorIndex=> rhoXL D.g (D.f i.1) s ∘ₗ LinearMap.proj i)))
lemma takeFL (s i) (x:UV four): (TagL D s x).2.2.1 i= (if D.f i.1 then rhoFL s else LinearMap.id) (x.2.2.1 i):= rfl
lemma takeGL (s) (x:UV four): (TagL D s x).2.1= (if D.g then rhoGL s else LinearMap.id) (x.2.1):=rfl
lemma takeXL (s i) (x:UV four): (TagL D s x).2.2.2 i=rhoXL D.g (D.f i.1) s (x.2.2.2 i):=rfl

def ledgerL (D: District) : Mink.Lorentz →* Module.End ℂ (UV four) where
  toFun:=TagL D
  map_one':=by
    apply LinearMap.ext; intro x
    change TagL D 1 x=x; apply Prod.ext
    · rfl
    apply Prod.ext
    · rw [takeGL,map_one]; cases D.g <;> rfl
    apply Prod.ext
    · ext1 i; rw [takeFL,map_one]; cases D.f i.1 <;> rfl
    ext1 i; rw [takeXL,map_one,Module.End.one_apply]
  map_mul' s t:=by
    apply LinearMap.ext; intro x; rw [Module.End.mul_apply]
    apply Prod.ext
    · simp only [TagL,LinearMap.prodMap_apply,LinearMap.id_apply]
    apply Prod.ext
    · rw [takeGL,takeGL,takeGL,map_mul]; cases D.g <;> rfl
    apply Prod.ext
    · ext1 i; rw [takeFL,takeFL,takeFL,map_mul]; cases D.f i.1 <;> rfl
    ext1 i; rw [takeXL,takeXL,takeXL,map_mul]; rfl

attribute [local instance] iA iG iX

abbrev CountUpL (D:District)(a:SpaceAxis): Module.End ℂ (UV four):= (-I) • enlarged D four (pVecΩL a)
lemma costL (a:SpaceAxis)(x:UV four): Sends (fun t=>ledgerL D (γBeamL a t) x) 0 (CountUpL D a x):=by
  change Sends (fun t=> TagL D (γBeamL a t) x) 0 _; dsimp only [CountUpL,LinearMap.smul_apply]; apply sent
  · intro L; change HasDerivAt (fun _:ℝ=>L x.1) (L ((-I) • ((enlarged D four (pVecΩL a) x).1))) _; rw [rule0,smul_zero,map_zero]; exact hasDerivAt_const _ _
  apply sent
  · change Sends (_) _ ((-I) • (enlarged D four (pVecΩL a) x).2.1); simp only [Prod.snd_smul,Prod.fst_smul,ruleG,takeGL]; cases D.g
    · intro L; simp only[activates,Bool.false_eq_true, ↓reduceIte, zero_smul,smul_zero,map_zero]; change HasDerivAt (fun _:ℝ=> L x.2.1) 0 0; exact hasDerivAt_const _ _
    simp only [activates,one_smul, ↓reduceIte]; exact spikeL (DeckG four) (gCard four) GeoSphereL (leavesG four) (gauge four).fin a x.2.1
  apply sent
  · apply sorted; intro i; change Sends _ _ ((-I) • ((enlarged D four (pVecΩL a) x).2.2.1 i)); simp only[Prod.snd_smul,Prod.fst_smul, Pi.smul_apply,ruleF,takeFL]; unfold EF; cases D.f i.1
    · simp only [activates,Bool.false_eq_true,↓reduceIte, LinearMap.id_apply, LinearMap.smul_apply, zero_smul,LinearMap.zero_apply]; intro l; simp; exact hasDerivAt_const _ _
    simp only[activates,one_smul,↓reduceIte]; exact spikeL (DeckF four) (fCard four) FlavorScopeL (leavesF four) (matter four).fin a (x.2.2.1 i)
  apply sorted; intro i; change Sends _ _ ((-I) • ((enlarged D four (pVecΩL a) x).2.2.2 i)); simp only [Prod.snd_smul, Pi.smul_apply,takeXL,ruleX]; exact spikeL (DeckX four) (xCard four D.g (D.f i.1)) (MixScopeL _ _) (leavesX four _ _) (mixed four).fin a (x.2.2.2 i)
lemma continL (x : UV four): ∀ L:UV four →ₗ[ℂ]ℂ, Continuous fun s=> L (ledgerL D s x) := by
  change ∀ L:UV four→ₗ[ℂ]ℂ,Continuous fun s=> L (TagL D s x)
  apply cprodL
  · intro l; change Continuous fun _ : Mink.Lorentz=> l x.1; exact continuous_const
  apply cprodL
  · simp_rw [takeGL]; cases D.g
    · intro l; change Continuous fun _:Mink.Lorentz=> l x.2.1; exact continuous_const
    intro l; exact Angles.distendL (DeckG four) (gCard four) GeoSphereL (leavesG four) (gauge four).fin x.2.1 l
  apply cprodL
  · apply cvecL; intro i l
    simp_rw [takeFL]; cases D.f i.1
    · change Continuous fun _ : Mink.Lorentz=> l (x.2.2.1 i); exact continuous_const
    exact Angles.distendL (DeckF four) (fCard four) FlavorScopeL (leavesF four) (matter four).fin (x.2.2.1 i) l
  apply cvecL; intro i l; exact Angles.distendL (DeckX four) _ (MixScopeL _ _) (leavesX four D.g (D.f i.1)) (mixed four).fin (x.2.2.2 i) l
lemma punTurnL (A:Ortho) (h:Lorentz.spatialTurn A): ledgerL D (Lorentz.room A h)= ledger D four (parkLorL A h):=by
  apply LinearMap.ext; intro x; change TagL D _ x=Tag D four _ x
  unfold TagL Tag rhoGL rhoFL rhoXL; simp_rw[Angles.padlockL]
#print axioms ledgerL
#print axioms costL
#print axioms punTurnL
end YM.GaugeFieldConstruction.Stage
