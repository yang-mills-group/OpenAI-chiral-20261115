import YM.SU5.Registration.Affine.StageAgenda
import YM.SU5.Registration.Affine.Collateral
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
/-!
 ## Extend (116) at actual continuum point fields
 Statement over character space AND any axis computing (116) estimate, not
 requiring that observer to have the same order from the given axis chart. Use on
 all-axis generic configurations. Elected continuum fields from the same stencils
 even if varying padding/cuts for the actual width & grid prices. Doesn't assert
 unprojected-norm convergence of slab operators on Mean.
 -/
open WeakDual
variable {I:Type*}(K:P.Register)(L:List I)(A:I→P.Swatch)(T₁:∀ i x,(A i).WPermit x a)(p:I→Vantage)
local notation "uC" L:max=> (fun x=> P.EuCost x a L (fun i=>(T₁ i x).atHeat) p)
variable (P' : P.Passport a L A T₁ p)(h:StarCluster L p)(t:LightsCross a L p)(Y:∀ i∈L,(A i).Finishes)
variable {n:ℕ→ℕ}{σ:ℕ→I→ℕ}{r:ℕ→I→ Cover}(hn:∀ᶠ k:ℕ in atTop,∀ i∈L, ((A i).fieldA (σ k i)).s ≤ n k)(hy:∀ i∈ L,Tendsto (fun k=>σ k i) atTop atTop)(hq:∀ i∈L, Tendsto (fun k=> P.laysM (P.vtile (n k) (r k i))) atTop (𝓝 (p i)))
local notation "Z" k:max=> P.fullVisit L A (σ k) (r k) (n k)
local notation "VΓ" k:max x:max=> P.singleState 3 (n k) x (Z k)
local notation "WΓ" k:max j:max=> P.reading j (n k) (Z k)
local notation "Ξ" j:max=> P.Ensemble j
local notation "μ"=>P.pillars 3
local notation "Ωg" j:max=> P.groundZero j
include hn hy hq P' h t K Y
lemma full_uniform_visit : Agrees (b:=fun _=>ℂ) atTop (fun k x=>VΓ k x) (fun _ x=> (uC L) x):= by
 let q(k:ℕ):= P.laysM ∘ (P.vtile (n k) ∘ r k)
 refine (SatinRegistration.of_eq (?_)).trans (P' σ q hy hq)
 filter_upwards [hn,P.power_finishes a L p A Y hy (p':=q) hq t,P.power_cluster L p A Y hy (p':=q) hq h] with i t0 u v
 funext x; exact P.full_visit_exact x a L A (Classical.choice (P.ellisP 3 x K)) _ _ _ u v t0
omit hn hy hq P' h t K Y
lemma costed_character (n:ℕ)(T:P.Test) : Continuous (fun x=> P.singleState a n x T):= P.chi_joint a _ -- T local notation!
include P' h t K Y
lemma continuum_statement : Continuous (fun x=> (uC L) x):=by
 let σ:=fun (i:ℕ)(_ : I)=>i
 obtain ⟨r,n,p',b,c⟩:=P.full_visit_possible L p A σ
 exact TendstoUniformly.continuous (Agrees_uniform.mp (P.full_uniform_visit a K L A T₁ p P' h t Y (Eventually.of_forall c) (σ:=σ) (fun _ _=>tendsto_id) b)) (Eventually.frequently (Eventually.of_forall fun _=> P.costed_character 3 _ _))
-- represent that by a function manually even for other γ in its intrinsic memory; using exactly ALL certificates not inverse character transport issues. not claiming off-budget queries can compute this.
noncomputable def SensorCharacter (P' : P.Passport a L A T₁ p)(h:StarCluster L p)(t:LightsCross a L p)(Y:∀ i∈ L,(A i).Finishes) (K:P.Register):P.Ensemble 3:= (gelfandStarTransform (P.Ensemble 3)).symm ⟨uC L,P.continuum_statement a K L A T₁ p P' h t Y⟩ -- `(include)` duplicate? Lean previous argument references, check
omit P' h t K Y
local notation "Γ"=> P.SensorCharacter a L A T₁ p P' h t Y K
include P' h t K Y
lemma sensor_priced (x:P.Spectrum0 3) : (uC L) x = P.chi 3 x Γ := by rw [P.chi_eval]; unfold SensorCharacter; rw [(gelfandStarTransform (P.Ensemble 3)).apply_symm_apply]; rfl
lemma fixes_on_any (j:Axis)(x:P.Spectrum0 3) : P.chi j (P.advocate 3 x j) (P.migrateHom 3 j Γ)=(uC L) x:=by unfold advocate; rw [P.translates,P.migrate_reverse]; exact (P.sensor_priced a K L A T₁ p P' h t Y x).symm
-- use sup killer
include hn hy hq
private lemma spectral_priced : Tendsto (fun k=> (WΓ k 3)) atTop (𝓝 Γ):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 filter_upwards [P.full_uniform_visit a K L A T₁ p P' h t Y hn hy hq (ε/2) (half_pos e)] with k v
 rw [dist_eq_norm]; by_contra! t0
 obtain ⟨x,hp⟩:= P.chi_one_top 3 ((WΓ k 3)-Γ) e t0
 have ht: P.chi 3 x (WΓ k 3) = VΓ k x:=rfl
 rw [map_sub,←P.sensor_priced a K L A T₁ p P' h t Y,ht, ←dist_eq_norm] at hp; exact not_lt_of_ge hp ((v x).trans_lt (half_lt_self e)) -- combined
lemma reading_limits (j:Axis) : Tendsto (fun k=>WΓ k j) atTop (𝓝 (P.migrateHom 3 j Γ)):=by
 have ht: Continuous (P.migrateHom 3 j):= open CStarAlgebra in map_continuous _
 exact ((ht.tendsto Γ).comp (P.spectral_priced a K L A T₁ p P' h t Y hn hy hq)).congr fun i=> P.returns_reading ..
-- retain floor prices of whole word (not multiply the prelimit compressions) computed in any observer.
omit hn hy hq K P' h t Y
lemma color_permit (σ:I→ℕ)(r:I→ Cover)(n:ℕ): P.fullVisit L A σ r n ∈ enclave P.calibration:= Subalgebra.smul_mem _ (P.full_scroll_effect n _ r L) _
-- reading equals projection if positively shifted to that box. use `preRead` law in Selected/Single.
variable (j:Axis)
lemma boxes_receive {w:ℕ}(p:0<w) (v:ℕ)(R:P.Test)(T:P.Card j v w)(z:ℤ)(h:P.voxTest j v T.val=P.shifts j z R): P.reading j v R=P.shadow j (P.atSide j v w p T):=by
 rw [P.boxes_here]; exact Eq.trans (P.shifted_read j v z R).symm (congrArg (P.reading j v) h.symm) -- preRead & reading defeq
lemma visit_here (σ:I→ℕ)(r:I→ Cover)(n:ℕ) : ∃ v:ℕ,0<v ∧ ∃ (z:ℤ)(b:P.Card j n v), P.voxTest j n b.val= P.shifts j z (P.fullVisit L A σ r n):=by
 let X:= P.fullVisit L A σ r n; obtain ⟨i,w,p,t,_,h,_⟩:= P.totalCost j X (P.color_permit L A σ r n) n; exact ⟨w,p,i,t,h⟩
lemma seed_on_box {w:ℕ}(p:0<w) (v:ℕ)(R:P.Test)(T:P.Card j v w)(z:ℤ)(h:P.voxTest j v T.val=P.shifts j z R) : (P.reading j v R).val (P.groundZero j)= P.piZero j (P.Box j v w p T (P.floorVec j)):=by rw [P.boxes_receive j p v R T z h, shadow_val, P.compress_apply]; rfl
include hn hy hq K P' h t Y
-- ∀ sequence of admissible shifted sails on the same pre-limit reading kernels even at compactly separated costs. j not required to align with read-axis a.
lemma egret_lands (v:ℕ→ℕ)(f:∀ i,0<v i)(z:ℕ→ℤ)(p':∀ i,P.Card j (n i) (v i))(q:∀ᶠ i:ℕ in atTop,P.voxTest j (n i) (p' i).val=P.shifts j (z i) (Z i)): Tendsto (fun i=> P.piZero j (P.Box j (n i) (v i) (f i) (p' i) (P.floorVec j))) atTop (𝓝 ((P.migrateHom 3 j Γ).val (P.groundZero j))):=by
 let G:=(Ωg j); let S: (Ξ j)→ (P.groundHil j).space:= fun A=> A.val G -- syntax coax uses `(P.groundHil j).space`
 have he:Continuous S:= (show Continuous fun f:(P.groundHil j).Op=> f G from continuous_id.clm_apply continuous_const).comp continuous_subtype_val -- edit notation shadows
 exact ((he.tendsto _).comp (P.reading_limits a K L A T₁ p P' h t Y hn hy hq j)).congr' (q.mono (fun i v'=> P.seed_on_box j (f i) _ _ _ _ v'))
-- unconditioned limit at same full price by that projection. No interpreting for now on mean spatial analytic.
lemma egret_mean : Tendsto (fun i=> P.E (n i) (Z i).val) atTop (𝓝 (inner ℂ (Ωg j) ((P.migrateHom 3 j Γ).val (Ωg j)))):=by
 let h0:= (P.reading_limits a K L A T₁ p P' h t Y hn hy hq j); let G:=(Ωg j); have he:Tendsto (fun i=> (WΓ i j).val G) atTop (𝓝 ((P.migrateHom 3 j Γ).val (Ωg j))):= ( (continuous_id.clm_apply (continuous_const (y:=G))).continuousAt.tendsto).comp (continuous_subtype_val.continuousAt.tendsto.comp h0)
 exact ( (tendsto_const_nhds (x:=G)).inner (𝕜:=ℂ) he).congr fun i=> P.occupied ..
-- mean of character function equals this result. use separate stmt below.
omit hn hy hq
lemma egret_reads : (∫ x, (uC L) x ∂μ) = inner ℂ (Ωg j) ((P.migrateHom 3 j Γ).val (Ωg j)):=by simp_rw [← P.fixes_on_any a K L A T₁ p P' h t Y j]; exact P.recovery_all ..

/- Equation (116) even between two different enrollments using any axis. -/
local notation "egret!"=> P.migrateHom 3
lemma egret_gram {J:Type*}(k:Axis)(B:J→P.Swatch)(W:∀ i x,(B i).WPermit x k)(l:List J)(q:J→Vantage)(qT:P.Passport k l B W q)(W₁:StarCluster l q)(W₂:LightsCross k l q)(W₃:∀ i∈l,(B i).Finishes):
  inner ℂ ((P.migrateHom 3 j Γ).val (Ωg j)) ((P.migrateHom 3 j (P.SensorCharacter k l B W q qT W₁ W₂ W₃ K)).val (Ωg j)) = ∫ x:P.Spectrum0 3, star ((uC L) x) * (P.EuCost x k l (fun i=>(W i x).atHeat) q) ∂ (P.pillars 3):=by
 -- at every gamma values already true in that election, then exact (116) by recovery_all
 let X:= egret! j Γ; let Y':= P.migrateHom 3 j (P.SensorCharacter k l B W q qT W₁ W₂ W₃ K); let Z':=P.chi j
 have hx(x:P.Spectrum0 3):=P.fixes_on_any a K L A T₁ p P' h t Y j x; have hz(x:P.Spectrum0 3):=P.fixes_on_any k K l B W q qT W₁ W₂ W₃ j x; have hm:= P.recovery_all 3 j (star X*Y'); have he:inner ℂ (Ωg j) ((star X*Y').val (Ωg j))=inner ℂ (X.val (Ωg j)) (Y'.val (Ωg j)):=ContinuousLinearMap.adjoint_inner_right X.val _ _
 rw [he] at hm; simp_rw [map_mul,map_star] at hm
 simp_rw [← hx,← hz]; exact hm.symm -- defeq

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.seed_on_box
#print axioms Spine.visit_here
#print axioms Spine.egret_gram
#print axioms Spine.egret_lands
#print axioms Spine.egret_mean
#print axioms Spine.egret_reads
#print axioms Spine.full_uniform_visit
