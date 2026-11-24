import YM.SU5.Reconstruction.Hygrometry.Morph
import YM.CF.Continuum.Conditional
import YM.UVNext.COUPLING_RESET.Probe
/-!
 Continuum/Conditionals estimate on exactly an invariant-pane, extending to either parity here
 and paying condition in the ensemble of estimates of this CP. Not gauge-averaged.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Pressure RG Push.SectorMeasure Phase Reflect RP Mir Mir.Trip Scree Brace Vale Vale.Grace Peaks Paige Vault
open scoped ComplexOrder Classical
variable {N m B:Side}
lemma flat_flag (p: BudgetPoint): flags p.threshold (1:Bkg (More N))=∅:= UVNext.CouplingReset.flags_one _
lemma atlas_guard {e:ℝ} (p:0≤e): Guard (1:Bkg (More N)) e:=atAtlas N ▸ tax_guard emptyC _ _ p
lemma fixed_atlas (m B:Side)(a:Axis): rayUK m B a 1=1:=by funext i; rw [reflect_E]; simp
lemma overhead {d₁: Side}{j:ℕ}{h:Odd d₁.val}{Y:Pricing j d₁ h (Thread j)}{δ:ℝ}(P₀:Grasp Y B δ) (d:0≤δ) (e:P₀.roundZ ≤ (CSide m B).val) (p:Pad j (CSide m B))(M:Jill.Male) : Sea (latPose j M (CSide m B)) (changeM P₀ (1:Bkg (More (CSide m B))) M):= identity_atlas M p ▸ sea_g e 1 (atlas_guard d) M
-- normalization. lemma using Loan conditional. $q$ supplied from query.
variable {K : Teller group} {P:Patch}{e:ℝ}{Y:Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(u:A.roundZ ≤ (CSide m B).val)(g:0≤e)
set_option quotPrecheck false
local notation "τ" => CSide m B
local notation "N₀" => (1:Bkg (More τ))
local notation "Z₁" => changeM (m:=m) A 1 babyM
variable (q:BudgetPoint)(V:Op SpinIdx) (α:Axis)(p:Pad K.j (CSide m B))(hp:1 ≤ K.j)
-- unfolding cap at β=0; Assess hypothetical q without assuming already making it in law. Stamp. keep B as $exact*$. Need binder not shadow. 
lemma meterBorn: capP (K:=K) (P:=P) (m:=m) A 0 q 1= Z₁:=by
 unfold capP; rw [Set.indicator_of_mem (show N₀∈ _ from flat_flag q)]; simp -- tune
include u g p hp q
lemma straightW {b:Bool}{F:FC (Single (CSide m B))} (v:Sector (matterSet (CSide m B) (posY m B α)) b F): 0 ≤ SpinPrice (changeM A (1:Skin m B) babyM) (Reflect.chord b • (Fock.theta (Buffered.carR α 0 _) F * F)) := by
 let Φ:= chord b • (Fock.theta (Buffered.carR α 0 _) F * F); let Z:= capP (K:=K) (P:=P) (m:=m) A 0 q 1
 have hv:= overhead A g u p babyM; have he : oneField N₀ Z 1≠0:= by unfold Z; rw [oneField_vac, meterBorn]; exact can_spend p.1 hp hv
 let X : Evaluation (CSide m B) := fun _=>Φ
 obtain ⟨d,k⟩:= conditional_balance (K:=K) (P:=P) (m:=m) (L:=A) N₀ 0 q α u (atlas_guard g) (flat_flag q) he X
 rw [show SpinPrice Z₁ Φ=conditional (N:=τ) N₀ Z X from ?_]
 swap; · unfold Z conditional; rw [meterBorn,oneField_vac]; rfl
 unfold Z; rw [d]; apply div_nonneg _ k.le
 unfold seamed X Φ; rw [toSeam_scalar,toSeam_prod, carR_zero,toSeam_turn α v]; exact reflector_line _ (fixed_atlas m B α) _ (toSeam_forward α v rfl) (wiel_ok _ A.baseY (atlas_guard g))
end YM.CF.Hygrometry
