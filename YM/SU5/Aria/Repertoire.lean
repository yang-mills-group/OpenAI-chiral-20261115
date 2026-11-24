import YM.SU5.Aria.Personnel
import YM.SU5.Aria.Troupe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "Ω"=>P.heaven j x
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "Μ"=> timeMesh P.par
local notation "Γ"=> P.VMark
local notation "ξ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "E'"=> (P.seasons j x).E
local notation "κ"=> P.truck j x
local notation "Υ"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "τ" r:max=> Real.toNNReal r
variable (D:P.Apron)
local notation "P₀"=> D.engine P j x
local notation "u" p:max=> Apron.time_panel P j p D
local notation "v" p:max=> Apron.time_edge P j p D
variable (c d:ℝ)
def raze (g:Γ): (X).Op:= (E (τ ((u (ξ g))-c))).comp ((P.charter j x g P₀).comp (E (τ (d-v (ξ g)))))
def pillar (g: Vantage):(Χ).Op:= (E' (τ (u g-c))).comp ((P.tableau j x g P₀).comp (E' (τ (d-v g))))
def remunerate (m:Mist P.VMark) := m.mean (P.raze j x D c d)
lemma raze_pay (g:Γ): ‖P.raze j x D c d g‖≤‖P₀‖:= (wrap_pay (P.charter j x g P₀) _ _ ((ψ).shrinks _) ((ψ).shrinks _)).trans (P.charter_pay ..)
lemma remuneration (m:Mist P.VMark): ‖P.remunerate j x D c d m‖≤ ‖P₀‖:= m.mean_budget _ _ (m.solves _ (P.raze_pay j x D c d))
lemma unFee {p:Vantage} (g:ℕ→ Mist P.VMark)(t:P.gentle p g)(y: u p>c)(w: v p< d):
    ∀ ε>0,∀ᶠ n in atTop,(g n).holds (fun b=> dist (E (τ (u (ξ b)-c))) (E (τ (u p-c)))≤ ε ∧ dist (E (τ (d-v (ξ b)))) (E (τ (d-v p)))≤ ε):=by
 have h₁: ContinuousAt (fun t:Vantage=> E (τ (u t-c))) p:= (steam_contPos (ψ) _ (sub_pos.mpr y)).comp (f:=fun t:Vantage=>u t-c) (show ContinuousAt (fun t:Vantage=>u t-c) p by unfold Apron.time_panel; exact (((continuous_apply j).sub continuous_const).sub continuous_const).continuousAt)
 have h₂: ContinuousAt (fun t:Vantage=> E (τ (d-v t))) p:= (steam_contPos (ψ) _ (sub_pos.mpr w)).comp (f:=fun t:Vantage=>d-v t) (show ContinuousAt (fun t:Vantage=>d-v t) p by unfold Apron.time_edge; exact (continuous_const.sub ((continuous_apply j).add continuous_const)).continuousAt)
 intro ε e; have v' := P.gentle_room t ((Metric.tendsto_nhds.mp h₁ ε e).and (Metric.tendsto_nhds.mp h₂ ε e)); exact v'.mono (fun n h=> (g n).promotes (fun b v₁=> ⟨v₁.1.le,v₁.2.le⟩) h) -- v notation conflict if followed => (fun b v fine?)
private lemma handy_dist {B:Hilbert}(X' Y':B.Op)(y:B) : dist (X' y) (Y' y)≤ dist X' Y' * ‖y‖:=by simp only [dist_eq_norm]; exact (X'-Y').le_opNorm y
lemma raze_est (p:Vantage)(y:X) (g:ℕ→Mist P.VMark)(t: P.gentle p g)(a:u p>c)(b:v p<d): ∀ ε>0,∀ᶠ n in atTop,(g n).holds (fun z=> dist (P.raze j x D c d z y) (E (τ (u p-c)) ((P.charter j x z P₀) (E (τ (d-v p)) y))) ≤ ε):=by
 intro ε e; let μ:= ‖P₀‖; let T:=ε/(2*(μ+1)*(‖y‖+1)); have hu:0 ≤ μ:=norm_nonneg _; have ht:0<T:=by positivity
 refine (P.unFee j x D c d g t a b T ht).mono (fun n v₀=> (g n).promotes ?_ v₀); intro z h
 have hp: dist (P.raze j x D c d z) ((E (τ (u p-c))).comp ((P.charter j x z P₀).comp (E (τ (d-v p)))))≤ T*μ+μ*T:= wrap_est (P.charter j x z P₀) _ _ _ _ ((ψ).shrinks _) ((ψ).shrinks _) h.1 h.2 (P.charter_pay ..)
 refine (handy_dist («X'»:=P.raze j x D c d z) («Y'»:= (E (τ (u p-c))).comp ((P.charter j x z P₀).comp (E (τ (d-v p))))) y).trans (le_trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) ?_); have he: T*(2*(μ+1)*(‖y‖+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith [norm_nonneg y,mul_nonneg ht.le (mul_nonneg hu (norm_nonneg y)),mul_nonneg ht.le (norm_nonneg y)]
section attenuation
variable (A:ℕ→ Mist P.VMark)(a:P.gentle 0 A)(t:∀ y:(P.ColorHil j x), Tendsto (fun i=>(A i).mean (fun z=> P.truck j x z y)) atTop (𝓝 (P.enter j x (P.wealth j x y)))) (q:ℕ→ P.VMark)(p : Vantage)(r:Tendsto (P.laysM∘ q) atTop (𝓝 p))
-- this variable repeated for all factors by user for product test
local notation "Q" i:max=> (A i).onFn (fun b=>q i+b)
include a t r
lemma prompting (x₁:Χ) : Tendsto (fun i=>(Q i).mean (fun z=> P.charter j x z P₀ (Υ x₁))) atTop (𝓝 (Υ ((P.tableau j x p P₀) x₁))):= (P.tableau_arrives j x P₀ a t q p r x₁).congr (fun n=> (Mist.mean_onFn (A n) _ (fun z=>P.charter j x z P₀ (Υ x₁))).symm)
lemma firming (w:u p> c)(z:v p<d)(y:Χ): Tendsto (fun i=> (P.remunerate j x D c d (Q i)) (Υ y)) atTop (𝓝 (Υ ((P.pillar j x D c d p) y))):=by
 let t':=τ (u p-c); let b:=τ (d-v p); let T₁:=E t'; let y':= E b (Υ y); let v' := E' b y; let X' := P.tableau j x p P₀ v'; let k(n:ℕ):=(Q n)
 have hx : Tendsto (fun n=> T₁ ((k n).mean (fun z=> P.charter j x z P₀ y'))) atTop (𝓝 (T₁ (Υ X'))):= by unfold y'; rw [← P.soleHeat]; exact T₁.continuous.continuousAt.tendsto.comp (P.prompting j x D A a t q p r v') -- CLM .continuousAt error name
 change Tendsto _ _ (𝓝 (Υ (E' t' X'))); rw [P.soleHeat]
 have he:Tendsto (fun n=> (k n).mean (fun z=> P.raze j x D c d z (Υ y))) atTop (𝓝 (T₁ (Υ X'))):=
    attains_mean (g:=fun _ z=> T₁ (P.charter j x z P₀ y')) (hx.congr fun i=>(Mist.mean_linear' _ _ _).symm) (P.raze_est j x D c d p (Υ y) k (P.frugal_moves a q p r) w z)
 exact he.congr fun i=> Casting.use_measured ..
end attenuation
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.firming
