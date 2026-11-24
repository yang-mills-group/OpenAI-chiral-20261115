import YM.SU5.Reconstruction.Quanta.Printer
import YM.SU5.Reconstruction.Quanta.Touch
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
set_option linter.unusedVariables false -- h₁, V etc
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)


-- charging gauge for all animal grades. Scans EVEN χ-local gauge wallets; Ward for the Frame extension. Individual Weyl seeds NO GRAM COST!
open Finset Mir Phase RP Nacre Spire Scroll Peaks Rush Tulip Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Fock
namespace SpectrumGauge
local notation "Pₓ" => price Y H V G C j χ
variable (s:ℕ)(a:Axis) (z:ℤ)
local notation "Z"=> Heat.gaugeShift Λ.block z
local notation "F₊"=> poleForm K a (Heat.gaugeShift Λ.block z)
variable {g₀:Bool} {S T:Finset Cover} {f g f' g':Family (tent Y H)} {J:Calibration}
private lemma color_pair {A B:Family J} {X:Family J}(p:InTest J true S g₀ X){v:Cover→ SU.E}(q:Tapestry.Circular T v A B)(e:Disjoint S T): ∃ V:Cover→SU.E,Tapestry.Circular (S∪T) V (X*A) (X*B):=by
 let V:=fun u=> if u∈S then 1 else v u
 exact ⟨V, Circular.mul _ _ (largerGauge Finset.subset_union_left (circle_swap (Garret.anywhereOne p) (fun x u=> (show V x=1 from if_pos u)))) (largerGauge Finset.subset_union_right (circle_swap q (fun i u=>if_neg (fun E=> Finset.disjoint_left.mp e E u))))⟩ -- tune binder
lemma paysGauge (p:InTest K true S g₀ f)(q:InTest K true T g₀ g)(q':InTest K true T g₀ g')(u:Tower.region a (Heat.gaugeShift Λ.block z) (K).ℓ S)(v:Tower.region a (Heat.gaugeShift Λ.block z) (K).ℓ T)
    (W:Cover→ SU.E)(t:Tapestry.Circular T W g g'):Pₓ s false (F₊ g₀ f g)= Pₓ s false (F₊ g₀ f g'):=by
 let h:= mirror_detached Λ l u v; obtain ⟨w,h⟩:=color_pair (axial K a Z p) t (detached_disjoint h)
 exact (price_rotation Y H V G C j χ s w (NorthTapes.statement a Z p q) (NorthTapes.statement a Z p q') (h.scale w _ (Reflect.chord g₀))).symm
-- annihilate arbitrary charged partner by THE actual interior estimator, not assuming elementary field states in a
-- Mink theory. true physical grades accept any such Wilson dressing with residual charge in this sense.
lemma suppress (b:ℂ)(h:b≠1)(p:InTest K true S g₀ f)(q:InTest K true T g₀ g)(u:Tower.region a Z ((tent Y H).ℓ) S)(v:Tower.region a Z ((tent Y H).ℓ) T)(W:Cover→ SU.E)(t:Tapestry.Circular T W g (b • g)): Pₓ s false (F₊ g₀ f g)=0:=by
 have he:= paysGauge Y H V G C j χ s a z p q (InTest.smul b q) u v W t
 rw [show F₊ g₀ f (b • g)= b • (F₊ g₀ f g) from ?_,price_smul Y H V G C j χ s (NorthTapes.statement a Z p q)] at he; swap; · unfold poleForm; rw [Algebra.mul_smul_comm,smul_comm]
 by_contra p'; apply h; apply mul_right_cancel₀ p'; rw [one_mul]; exact he.symm

open SU Lat
abbrev frac (w: SU.Slot):= SU.z ^ SU.charge w
lemma frac_ne (w:SU.Slot):frac w ≠1:=by intro h; obtain h:= z_prim.dvd_of_pow_eq_one _ h; rcases w with ⟨i,k|k⟩ <;> unfold SU.charge at h <;> norm_num at h
lemma frac_unit (w:SU.Slot): star (frac w)* frac w=1:=by rw [mul_comm (star _), frac, star_pow,← mul_pow, z_uu,one_pow]
lemma actual_pin {T:Finset Cover}{x:Cover}(b:SpinIdx)(w:SU.Slot) (p:nodeC x∈ T) {n:Side}(u:Seat n→ SU.E)(t:TraceGauge T (fun _=> SU.central) u) : acts (tradew n u).val (basisC n x b w) = frac w • basisC n x b w:= by
 rw [turn_basisC,t _ p,SU.by_charge,sum_eq_single w]; rw [Matrix.diagonal_apply_eq]
 · intro j _ v; rw [Matrix.diagonal_apply_ne _ v,zero_smul]
 simp
-- positive half queries on THIS estimator
variable {k₁:SpinIdx}(w:SU.Slot)(x:Cover)
lemma creat_atom (p:nodeC x∈ S): Circular S (fun _=> SU.central) (creation (tent Y H) x k₁ w) (star (frac w) • creation (tent Y H) x k₁ w):=by
 intro m g h X; change create (basisC ((K).c m) x k₁ w) = twist (quantU (tradew _ g)) (star (frac w) • create (basisC ..)); rw [twist_scalar, twist_create,actual_pin k₁ w p g h,map_smul, smul_smul,frac_unit,one_smul]
lemma death_atom (p:nodeC x∈ S): Circular S (fun _=> SU.central) (removal (tent Y H) x k₁ w) (frac w • removal (tent Y H) x k₁ w):=by
 intro m g h X; change Fock.remove (basisC ((K).c m) x k₁ w)=twist (quantU (tradew _ g)) (frac w • Fock.remove (basisC ..)); rw [twist_scalar,twist_remove, actual_pin k₁ w p g h,show Fock.remove (frac w • basisC ((K).c m) x k₁ w)=star (frac w) • Fock.remove (basisC ((K).c m) x k₁ w) from ?_,smul_smul,mul_comm,frac_unit,one_smul]
 unfold Fock.remove; rw [map_smul,star_smul] -- tune
lemma nucleon {fp : Family (tent Y H)} (t:nodeC x∈ T)(p:InTest K true S true fp)(u:Tower.region a Z ((tent Y H).ℓ) S)(v:Tower.region a Z ((tent Y H).ℓ) T):
    (k₁∈plusHalf → Pₓ s false (F₊ true fp (creation (tent Y H) x k₁ w))=0) ∧ (k₁∉plusHalf → Pₓ s false (F₊ true fp (removal K x k₁ w))=0) := by
 constructor
 · intro p'; apply suppress Y H V G C j χ s a z (star (SpectrumGauge.frac w)) ?_ p (InTest.creator _ p' t) u v _ (creat_atom Y H w x t)
   intro h; apply frac_ne w; apply star_injective; simpa only [star_one] using h
 intro p'; exact suppress Y H V G C j χ s a z (SpectrumGauge.frac w) (frac_ne w) p (InTest.remover _ p' t) u v _ (death_atom Y H w x t)
end SpectrumGauge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.SpectrumGauge.suppress
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.SpectrumGauge.nucleon
