import GaugeFieldConstruction.Sell

/-!
# Satisfactions in calibration basis. Slot and mixed factors exact
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Row Stage Stage.Cell Stage.Wide Phys Function Filter Set Finset Complex Calibration Lamp
open Matter (Slot FlavorIndex)
open scoped Topology BigOperators ContDiff
variable {x y : E4} {χ : E4→ℝ} {K : Dollars}

namespace Lamp
variable {α β γ : Type*} (G : Lamp α β)
lemma summer {s t u v} (p : Course K) (c : Chassis x y χ) (a : G.Latch χ K x y s u) (b : G.Latch χ K x y t v): G.Latch χ K x y (s+t) (u+v) := by
  intro d; rw [total G p c,a,b,map_add,LinearMap.add_apply]
lemma coins {s t} (h:G.Latch χ K x y s t) (r : ℂ) : G.Latch χ K x y (r • s) (r • t) := by intro d; rw [tip,h,map_smul]; rfl
lemma mints : G.Latch χ K x y 0 0 := by intro d; simp [glow,YM.GaugeFieldConstruction.Flux.Shell,Flux, currentZ,toll,YM.Maxwell.Free.exportFlux]
lemma summed (p : Course K) (c : Chassis x y χ) {S : Finset γ} {v w : γ→ J α} (h : ∀ i∈S,G.Latch χ K x y (v i) (w i)): G.Latch χ K x y (∑ i∈S,v i) (∑ i∈S,w i) := by
  classical
  induction S using Finset.induction_on with
  | empty=> simp; exact G.mints
  | insert i s ht ih=> rw [Finset.sum_insert ht,Finset.sum_insert ht]; exact G.summer p c (h i (by simp)) (ih (fun i m=> h i (by simp [m])))
lemma rotor {Ω v w c} (p : G.Touch (soar Ω x) c v w) (g : Chassis x y χ) : G.Latch χ (soar Ω x) x y v (c • w) := by
  have h:=G.receives p g; simpa only [Stage.still, ofReal_zero,zero_smul,sum_const_zero, add_zero] using h
end Lamp

lemma a_balance (u : FlavorIndex) (i j : Slot) (v : Phys.alpha u i j≠0) : rad i=u.1 ∧ rad j=u.1 := by
  change Matter.coeffs _ _ _ ≠0 at v; rw [Flavor.wear] at v; split_ifs at v with h; swap; contradiction
  have ht : (Flavor.tagged i.2,i.1,j.1)=u:= by by_contra t; simp [Pi.single_apply,t] at v
  exact ⟨congr_arg Prod.fst ht,by unfold rad; rw [← h, ← ht]⟩
lemma b_balance (u : FlavorIndex) (i j : Slot) (s) (v : Phys.beta u s i j≠0) : rad i=u.1 ∧ rad j=u.1 := by
  change Matter.costing _ _ _ _ ≠0 at v; rw [Flavor.roof] at v
  have ht : (Flavor.tagged i.2,i.1,j.1)=u:= by by_contra t; simp [Pi.single_apply,t] at v
  have h : Flavor.tagged i.2=Flavor.tagged j.2:= by
    have hm : Matter.repX (Matter.H (dye s)) i.2 j.2 ≠ 0 := fun t=> v (by rw [t,mul_zero]); rcases i with ⟨r,m|m⟩ <;> rcases j with ⟨a,t|t⟩
    · rfl
    · exact (hm rfl).elim
    · exact (hm rfl).elim
    rfl
  exact ⟨congr_arg Prod.fst ht,by unfold rad; rw [← h, ← ht]⟩

-- stays upon every Slot weighting. K general for PH.
lemma phase (p : Course K) (V : Bool→ℂ) (X Z : J f) (w : ∀ c d,(X,Z)∈ ready V c d K) (k : FlavorIndex) :
    (gloF (fStress V)).Touch K (V k.1) (tiap k X) (tiap k Z) := by
  simp_rw [tiap,LinearMap.sum_apply,LinearMap.smul_apply]; apply sums_T p; intro a _; apply sums_T p; intro b _
  by_cases h:Phys.alpha k a b=0
  · rw [h,zero_smul,zero_smul]; exact emptyT
  obtain ⟨y,u⟩:= a_balance k a b h; apply wish; rw [← y]; exact acts V p (y.trans u.symm) (X,Z) (w a b)

def mixB (a : MX) (Ω : Rotors) := Cell.beta (PX true false) Ω (ket a)
def mixL (a : MX) (Ω : Rotors) := Cell.beta (PX false true) Ω (ket a)
lemma split_m (Ω : Rotors) (i) : jet Wide.log (mixB i Ω) = times' (B i.1) (jet sheet (Cell.beta Theta Ω (ket i.2))) := by
  rcases i with ⟨x,y⟩; change jet Wide.log (Cell.beta ((Still Axis).wings Theta) Ω (ket (x,y)))=_; rw [fork_cost,vacant,map_zero,zero_add]
  have H : jet (fun i=>Wide.log (x,i))=times' (B x) ∘ₗ jet sheet := ket_ext (fun i=>by simp [Wide.log])
  rw [H]; rfl
lemma split_f (Ω : Rotors) (i) : jet Wide.log (mixL i Ω) = times' (jet B (Cell.beta UnitV Ω (ket i.1))) (sheet i.2) := by
  rcases i with ⟨x,y⟩; change jet Wide.log (Cell.beta (UnitV.wings (Still W)) Ω (ket (x,y)))=_; rw [fork_cost,vacant,map_zero,add_zero]
  have H : jet (fun i=>Wide.log (i,y))=times'.flip (sheet y) ∘ₗ jet B := ket_ext (fun i=>by simp [Wide.log]);
  rw [H]; rfl

lemma mixed_pay (Ω : Rotors) (a : MX) (m : ℂ) (V : Bool→ℂ) (k : FlavorIndex) (c : Chassis x y χ):
    (gloX (fStress V) (gStress m)).Latch χ (soar Ω x) x y (tuap k (Wide.log a))
      (tuap k (m • (jet Wide.log (mixB a Ω)) + V k.1 • jet Wide.log (mixL a Ω))) := by
  have H := (soarC Ω x).toCourse; have h := soarT Ω x
  rw [split_m,split_f]; unfold tuap; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]; apply summed _ H c
  intro i _; apply summed _ H c; intro j _; apply summed _ H c; intro l _
  by_cases p : Phys.beta k l i j=0
  · rw [p,zero_smul,zero_smul]; exact Lamp.mints _
  apply Lamp.coins
  obtain ⟨r,q⟩:= b_balance k i j l p
  simp only [fD, Wide.log,map_add,map_smul,straps]; rw [← r,add_comm]
  have hv := Bc H h V (c:=i) (d:=j) a.1
  have hp:= (gloF (fStress V)).sum_pay _ H c ((gloF _).rotor (acts V H (r.trans q.symm) _ hv) c) ((Flash _).rotor (leaf_touch H h m a.2 l) c)
  dsimp only at hp
  rw [map_smul, (times' _).map_smul, LinearMap.smul_apply] at hp; exact hp
end YM.GaugeFieldConstruction.Flux.One
