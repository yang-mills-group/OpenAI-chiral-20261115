import GaugeFieldConstruction.Tidings
/-!
# Change in active type, costs over the inserted legs
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Calibration.RawBank Floor Cauchy Row Phys Conj Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles
section lemmaS
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
variable [Module.Finite ℂ B]
lemma SO_compute (x : SO) {p : SO→ Prop} (H : ∀ u t,p (rise u t)) (h : p 1) (m : ∀ s t,p s→ p t→p (s*t)) (v :∀ s,p s → p s⁻¹) : p x := by
  obtain ⟨x,hx⟩:=x
  apply Subgroup.closure_induction (p:= fun x h=> p ⟨x,h⟩) _ _ _ _ hx
  · rintro _ ⟨u,t,rfl⟩; exact H u t
  · exact h
  · intro x y hx hy w u; exact m ⟨x,hx⟩ ⟨y,hy⟩ w u
  intro x hx e; exact v ⟨x,hx⟩ e
lemma follows {R : SO→* Module.End ℂ A} {r : Rotors→ Module.End ℂ A}
    {S : SO→* Module.End ℂ B} {s : Rotors→ Module.End ℂ B} (H : ∀ u a t,Sends (fun t=> R (rise u t) a) t (r u (R (rise u t) a)))
    (G : ∀ u b t,Sends (fun t=> S (rise u t) b) t (s u (S (rise u t) b))) (F : A→ₗ[ℂ]B) (p : ∀ u, F ∘ₗ r u=s u ∘ₗ F) (x:SO): F ∘ₗ R x=S x ∘ₗ F := by
  apply SO_compute x (p:=fun x=> F ∘ₗ R x=S x ∘ₗ F)
  · intro u t; apply LinearMap.ext; intro a
    have h (t) : Sends (fun t=> F (R (rise u t) a)) t (s u (F (R (rise u t) a))):= (LinearMap.congr_fun (p u) (R (rise u t) a)) ▸ posts (H u a t) F -- adjust
    apply congr_fun (captain (s u) _ _ h (G u (F a)) ?_) t
    simp only [show rise u 0=1 from Subtype.ext (YM.Work.A13.oneParameter_zero _),map_one,Module.End.one_apply]
  · rw [map_one,map_one]; rfl
  · intro x y w u
    rw [map_mul,map_mul]; apply LinearMap.ext; intro a
    simp only [LinearMap.comp_apply,Module.End.mul_apply]; rw [show F (R x _)= S x _ from LinearMap.congr_fun w _,show F (R y _)=S y _ from LinearMap.congr_fun u _]
  intro x v; apply LinearMap.ext; intro a
  simp only [LinearMap.comp_apply];
  have ht : R x (R x⁻¹ a)=a:= by rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]; rfl
  rw [← show S x⁻¹ (S x (F (R x⁻¹ a)))=F (R x⁻¹ a) from by rw [←Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]; rfl,
    ← show F (R x (R x⁻¹ a))=S x (F (R x⁻¹ a)) from LinearMap.congr_fun v _,ht]
end lemmaS
variable (D : District) {d : Floor}
lemma riseGrade (s:SO) (v: UV d): lift d (ledger D _ s v)=ledger D _ s (lift d v):= by
  have ht:= @follows (UV d) (UV five) _ _ _ _ _ (ledger D d) (enlarged D d) (ledger D five) (enlarged D five) (cost D (d:=d)) (cost D (d:=five)) (lift d) (fun u=>LinearMap.ext fun i=> (SY_up (activates D.g) (fun j=> activates (D.f j)) d u i).symm) s
  exact LinearMap.congr_fun ht v
lemma shade_moves (s : SO) (x : UV d): shade d (ledger D d s x)=ledger D d s (shade d x):= by
  change shade d (Tag D d s x)=Tag D d s _; apply Prod.ext
  · rfl
  apply Prod.ext
  · rw [takeG];
    change flipT (gauge d) (Tag _ _ _ x).2.1= _
    rw [takeG]; cases D.g
    · rfl
    exact Subtype.ext (hero (DeckG d) _ (leavesG d) _ x.2.1 (flipT (gauge d) _) s rfl).symm
  apply Prod.ext
  · ext1 i; rw [takeF]; change flipT (matter d) ((Tag D d s x).2.2.1 i) = _; rw [takeF]; cases D.f i.1
    · rfl
    exact Subtype.ext (hero (DeckF d) _ (leavesF d) _ (x.2.2.1 i) (flipT (matter d) _) s rfl).symm
  ext1 i; rw [takeX]; change flipT (mixed d) ((Tag D d s x).2.2.2 i) = _; rw [takeX]
  exact Subtype.ext (hero (DeckX d) _ (leavesX d D.g (D.f i.1)) _ (x.2.2.2 i) (flipT (mixed d) _) s rfl).symm

abbrev All : District := ⟨true,fun _=> true⟩
def signMot (u : Signed) (p : signBit u=false) : SO := ⟨u.ortho,(covers_all _).mpr (by rw [parity,p]; rfl)⟩
lemma properG (u : Signed) (p:signBit u=false) (x:UG d):rhoG d (signMot u p) x = (gauge d).moves u x := Eq.symm (charges _ _ (leavesG d) _ (gauge d).toCarries (fromG d) u x p)
lemma properF (u : Signed) (p:signBit u=false) (x:UF d):rhoF d (signMot u p) x=(matter d).moves u x:= Eq.symm (charges _ _ (leavesF d) _ (matter d).toCarries (fromF d) u x p)
lemma properX (u : Signed) (p:signBit u=false) (x:UX d):rhoX d true true (signMot u p) x=(mixed d).moves u x:= Eq.symm (charges _ _ (leavesX d true true) _ (mixed d).toCarries (fromX d) u x p)
lemma mirror (s : Signed) (p:signBit s=false) (x:UV d): spinFrame d s x=ledger All d (signMot s p) x := by
  change _=Tag All d _ x; apply Prod.ext
  · rfl
  apply Prod.ext
  · rw [tuneG,takeG]; exact (properG ..).symm
  apply Prod.ext
  · ext1 i; rw [tuneF, takeF,Calibration.rev,p]; exact (properF ..).symm
  ext1 i; rw [tuneX,takeX, Calibration.rev, p]; exact (properX ..).symm
lemma stamp (s : Signed) (p: signBit s=false): s.ortho∈orbit := (signMot s p).property
end YM.GaugeFieldConstruction.Stage
