import YM.CF.Vp929.Contour.Form
import YM.CF.Vp929.Contour.Germs
import YM.CF.Vp929.Contour.Display
import YM.CF.Vow.Move
import YM.CF.Ione.Lean
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open VolumeRate Jet
/- Transport actual parameter analytic values to the needed charged jets in the real argument.
The spatial charges are only on tests at clear points. -/
namespace Ascent
variable {L:Set ℂ}{T:Set (Pane n)}{C e:ℝ}{A:ℂ→ Pane n → ℂ}{b:Finset (Bond (More n))}
-- pay on recentered TEST charts; hence the actual jets used there are analytic in z.
abbrev recur (b:Finset (Bond (More n)))(e:ℝ)(A:Pane n→ℂ)(U:Pane n) : tangD n→ℂ:=fun x=> A (gyrate b U (e • x))
lemma recenter (hs:IsOpen T)(v:Pane n)(p:v∈T)(t:0< e)(u:0≤ C)(n₀:ℕ):
 ∃ D:ℝ,0 ≤ D ∧ ∃ U:Set (tangD n), IsOpen U ∧ 0∈ U ∧ (∀ w∈ U,gyrate b v (e • w)∈ T) ∧ (∀ A:Pane n→ℂ,(∀ v∈T, Allows n₀ (recur b e A v) 0 C) → ∀ w∈ U,Allows n₀ (recur b e A v) w D):= by
 let g:= fun x: tangD n=> gyrate b v (e • x); let S:= e • ContinuousLinearMap.id ℝ (tangD n); let L:= e⁻¹ • ContinuousLinearMap.id ℝ (tangD n)
 let U:=g ⁻¹' T∩ {x |S x∈Metric.ball (0:tangD n) 1}
 let C':= composeCost n₀ C ‖L‖; obtain ⟨D,V,pW⟩:= Arbor.lime (α:=Unit) (E:=ℂ) SU.group b n₀ 1 C' (by unfold C' composeCost; positivity)
 have hu:IsOpen U:=by
    exact (hs.preimage ((stickU b v).comp S.continuous)).inter (isOpen_ball.preimage S.continuous)
 refine ⟨composeCost n₀ D (max ‖S‖ 1),by unfold composeCost; positivity,U,hu,⟨?_ ,?_⟩,fun v p=>p.1,?_⟩
 · change gyrate b v (S 0)∈ T; rw [map_zero,born]; exact p
 · change S 0 ∈ ball (0:tangD n) 1; rw [map_zero]; exact mem_ball_self zero_lt_one
 intro A t' w hw
 have hv(x:Pane n)(g:x∈T): Allows n₀ (A ∘ gyrate b x) 0 C':=by
    have hn:A ∘ gyrate b x= recur b e A x ∘ L:=by funext i; change _= A (gyrate b x (e • (e⁻¹ • i))); rw [smul_inv_smul₀ t.ne']; rfl
    rw [hn]; have hcL:Allows n₀ (recur b e A x) (L 0) C:= L.map_zero.symm ▸ t' x g
    have heL:Allows n₀ L 0 ‖L‖:= Jet.allows_linear (L:=L) (le_refl _) (by rw [map_zero,norm_zero]; exact norm_nonneg _)
    exact hcL.comp heL
 have hw₁:gyrate b v (S w)∈T:=hw.1; have hw₂:S w ∈ ball (0:tangD n) 1:= hw.2
 have pin: Allows n₀ (A ∘ gyrate b v) (S w) D:= @pW T (fun (_:Unit)=> A) (fun u p x=>⟨Warm.simple _ (hv u p).smooth,hv u p⟩) () v (S w) hw₁ hw₂
 have hcS:Allows n₀ S w (max ‖S‖ 1):= Jet.allows_linear (L:=S) (le_max_left ..) ((mem_ball_zero_iff.mp hw₂).le.trans (le_max_right ..))
 exact pin.comp hcS
lemma sure (hs:IsOpen T)(v:Pane n)(p:v∈ T)(t:0<e)(u:0≤C)(n₀:ℕ)(hU:∀ y∈L,∀ x∈T,Allows n₀ (recur b e (A y) x) 0 C)(hs':IsOpen L)(hu:∀ x∈T,DifferentiableOn ℂ (fun z=> A z x) L)(j:ℕ)(k:j≤n₀)(d:Fin j→ tangD n): DifferentiableOn ℂ (fun z=> iteratedFDeriv ℝ j (recur b e (A z) v) 0 d) L:=by
 obtain ⟨D,hD,W,U,W₀,V,q⟩:= recenter (b:=b) hs v p t u n₀; exact jet_p hs' U hD (fun u p=> hu _ (V u p)) (fun z e=> q _ (hU z e)) _ k 0 W₀ _

private lemma lift_i {f:tangD n→ℂ}{C:ℝ}{D:ℂ}{k:ℕ}(z:‖D‖=1) (p:Allows k f 0 C): Allows k (D • f) 0 C:=by
 refine ⟨p.smooth.const_smul D,fun u g=>?_⟩; rw [iteratedFDeriv_const_smul_apply (p.smooth.of_le (by exact_mod_cast g)), norm_smul,z,one_mul]; exact p.norm_le u g
variable {B:ℂ→ Pane n→ℂ}
open Complex
lemma sureHolo (hs:IsOpen T)(v:Pane n)(p:v∈T)(t:0<e)(u:0≤C)(n₀:ℕ)(hU:∀ y∈L,∀ x∈T,Allows n₀ (recur b e (A y) x) 0 C ∧ Allows n₀ (recur b e (B y) x) 0 C)(hs':IsOpen L)(hu:∀ x∈T,Holo L (fun z=> (A z x,B z x)))(j:ℕ)(k:j≤n₀)(d:Fin j→ tangD n) : Holo L (fun z=> (iteratedFDeriv ℝ j (recur b e (A z) v) 0 d, iteratedFDeriv ℝ j (recur b e (B z) v) 0 d)):=by
 let F(z:ℂ)(x:Pane n):= Pair.plus (A z x,B z x); let G(z:ℂ)(x: Pane n):= Pair.minus (A (star z) x,B (star z) x)
 have he(y:ℂ)(hy:y∈L): ∀ z, z∈ T→ Allows n₀ (recur b e (F y) z) 0 (C+C):=fun z p=>(hU y hy z p).1.add (lift_i (D:=Complex.I) Complex.norm_I (hU y hy z p).2)
 refine ⟨(sure hs v p t (add_nonneg u u) n₀ he hs' (fun z w=> (hu z w).1) j k d).congr (fun z q=> ?_),?_⟩
 · have hp:=hU z q v p; change _= iteratedFDeriv ℝ j (recur b e (A z) v+ Complex.I • recur b e (B z) v) 0 d; rw [iteratedFDeriv_add_apply (hp.1.smooth.of_le (by exact_mod_cast k)) ((lift_i Complex.norm_I hp.2).smooth.of_le (by exact_mod_cast k)) ,iteratedFDeriv_const_smul_apply (hp.2.smooth.of_le (by exact_mod_cast k))]; rfl
 have h(x)(z): recur b e (G x) z= recur b e (A (star x)) z + -Complex.I • recur b e (B (star x)) z:=by rw [neg_smul,←sub_eq_add_neg]; rfl
 apply (sure hs v p t (add_nonneg u u) n₀ ?_ (hs'.preimage continuous_conj) (fun v p=> (hu v p).2) (A:=G) j k d).congr
 · intro z q; let hp:=hU (star z) q v p; let Z:= lift_i (D:=-Complex.I) (by simp) hp.2; rw [h,iteratedFDeriv_add_apply (hp.1.smooth.of_le (by exact_mod_cast k)) (Z.smooth.of_le (by exact_mod_cast k)),iteratedFDeriv_const_smul_apply (hp.2.smooth.of_le (by exact_mod_cast k))]; refine Eq.symm ?_; simp only [_root_.add_apply,_root_.smul_apply,neg_smul,←sub_eq_add_neg]; rfl
 intro z q v p; rw [h]; exact (hU (star z) q v p).1.add (lift_i (by simp) (hU (star z) q v p).2)
end Ascent
end YM.CF.Py.Rate
