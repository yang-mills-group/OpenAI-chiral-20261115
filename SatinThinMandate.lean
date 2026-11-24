import SatinThinScrolls
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
set_option maxRecDepth 3600
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N:Side}{j r p d Mθ:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
open Regis.Head Garland Etch AnalyticBridge.VerifiedReset StressFlux RG Pressure
open Push.SectorMeasure Buffered.Lifted Scree
namespace Hookah.Blaze
variable {N n:Side}{G:Gauge}{I:Type} [Fintype I] (z:PlaqAxes→ℝ) (s:Signed) (x:Cover) {m c:ℕ} (a t:ℝ)
open scoped Classical
open Py.Rate.LocalLimit Preparation Yoke
open RG Push.SectorMeasure Buffered RP
structure Trip(I:Type) where
 loc:I → Cover
 orient : I→ Signed
variable (V:Trip I)
namespace Trip
abbrev tryN (N:Side): Tour I N:= ⟨wrap N ∘ V.loc,V.orient⟩
abbrev issued (x:ℝ): Papal.Weaver := fun n=> pension z (V.tryN (More n)) x
def canvasC := univ.biUnion (stencilFrame ∘ V.loc)
def superC(x:ℝ)(U:PairsC):ℂ:= ∏ i:I,(valueFl z (Real.sqrt x) (temp x) (V.orient i) (V.loc i) U.1:ℂ)
lemma touchedC (i:I) : stencilFrame (V.loc i) ⊆ V.canvasC:=fun x hx=> mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
lemma recorded (x:ℝ) : Coeff true V.canvasC (V.superC z x):=by
 have he(i:I):= (insideFl z (V.orient i) (V.loc i) (Real.sqrt x) (temp x)).mono (V.touchedC i)
 exact ⟨fun v=>by contradiction,Buffered.Stack.product_env _ _ (fun i _=> (he i).env),fun i j h S=> prod_congr rfl fun k _=> (he k).locus i j h S⟩
lemma issued_at (x:ℝ)(W:Fields N): V.issued z x N W= V.superC z x (onC N W.1,onC N W.2) • (1:FC _):=by
 let F:=V.tryN (More N); unfold issued pension chalkOp; rw [superC]; unfold silk; dsimp only; rw [Complex.ofReal_prod]; congr 1; exact prod_congr rfl fun i _=> congrArg Complex.ofReal (valueCovers ..).symm
lemma issued_eq (x:ℝ)(K:Calibration): Papal.household K (V.issued z x)= Buffered.scalar K (V.superC z x):=funext fun i=>funext fun j=> V.issued_at z x j
lemma issues (x:ℝ)(K:Calibration): InTest K true V.canvasC false (Papal.household K (V.issued z x)):=by rw [issued_eq]; exact .seed (V.recorded z x)
private lemma everyLodge {K:Calibration}{f:Papal.Weaver}{S:Finset Cover}(h: InTest K true S false (Papal.household K f)){q:Side}(p:K.c q=N) : AtSupport false (dBook N S) (f N):=by subst N; exact h.support q
lemma therapy_charge {K:Calibration}{M:Side}(h:K.c M=N){S:Finset Cover}(p:V.canvasC ⊆ S)(x:ℝ): AtSupport false (dBook N S) (V.issued z x N):=by subst N; exact ((issues z V x K).mono p).support M
lemma registered (q:I): (V.tryN (More N)).loc q∈ dBook N V.canvasC:= mem_image_of_mem _ (V.touchedC q (loc_frame _))
lemma kris_survives (j:PlaqAxes→ℝ)(a b:ℝ)(Q:Signed)(o:Skye.Seat N): GaugeInvariant (kris j a b Q o):=by
 intro u x; unfold kris; simp only; rw [Push.Local.pull_gauge, show ∀ x:Pane N,pingS b (Lattice.halo 10 {0}) (gauge (u ∘ Push.Local.turnSites Q o) x) ↔pingS b (Lattice.halo 10 {0}) x from fun x=>?_]; swap; · unfold pingS; simp_rw [face_gauge, Gauge.chord_conj]
 split; · unfold petalWorth; simp_rw [AnalyticBridge.VerifiedReset.petals_gauge, norm_smul,SU.group.norm_adjoint]
 rfl
lemma issued_invar (x:ℝ)(N:Side): Buffered.covariant (V.issued z x N):=by
 intro g p -- tune
 unfold issued pension chalkOp; have he: silk z (V.tryN (More N)) (Real.sqrt x) (temp x) (gauge g p.1)=silk z (V.tryN (More N)) (Real.sqrt x) (temp x) p.1:= Finset.prod_congr rfl fun _ _=>kris_survives ..; rw [show (simultaneous g p).1=gauge g p.1 from rfl]; dsimp only; rw [he, twist_scalar,map_one]
end Trip
end Hookah.Blaze
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.Trip.issues
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.Trip.issued_invar
