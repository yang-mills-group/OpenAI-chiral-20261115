/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.WindTorque.Halo
import YM.SU5.WakeInvestment.CurrentClan
import YM.SU5.Hiro.Platters
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Lifted Hiro
open Py.Rate.LocalLimit.Papal
open Window
-- frame from node xo to Gauge reference (or, if offset/orientation taken, in full from
-- that node to plaq base). all paths enter into the same Mark.
structure Staff where
 hub: Cover
 u: Cover
 face: Face ℤ
 spin: Twah.DirSpin
 steps: Walk
 stop_at: stop (nodeC u) steps=face.1
variable (W:Staff) {r:ℕ}
namespace Staff
abbrev xo : Cover:= nodeC W.u
structure Pays (r w:ℕ) : Prop where
 stepCost : W.steps.length≤w
 roomSites: ∀ i∈ visits W.xo W.steps,i∈ skyDeck W.hub r
 faceSites : visa W.face ⊆ skyDeck W.hub r
lemma Pays.node {w:ℕ}(h:W.Pays r w): W.xo∈ skyDeck W.hub r:= h.roomSites _ (by cases W.steps <;> simp [visits])
lemma Pays.root {w:ℕ}(h:W.Pays r w): W.face.1∈ skyDeck W.hub r:= h.faceSites (by simp [visa,visits,Lattice.square])
variable (ρ:ℝ)
def collar (U:LinksC): ColorL:= (SU.group.adjoint (Lattice.travel U W.xo W.steps)) (ρ • SU.group.curvature (faceValue U W.face))
open scoped Matrix.Norms.Frobenius in
lemma collarAd_cont (G : Gauge) : Continuous (fun z : G.El × G.Color => G.adjoint z.1 z.2) := by
  let F := G.colorMat.toContinuousLinearMap
  change Continuous (fun z : G.El × G.Color => G.projectColor (G.conjugate z.1 (G.colorMat z.2)))
  apply G.projectColor.toContinuousLinearMap.continuous.comp (f:=fun z : G.El × G.Color => G.conjugate z.1 (G.colorMat z.2))
  unfold Gauge.conjugate
  exact ((G.continuous_mat.comp continuous_fst).mul (F.continuous.comp continuous_snd)).mul ((continuous_star.comp G.continuous_mat).comp continuous_fst)

lemma collar_cont : Continuous (W.collar ρ) := by let T (U:LinksC):= (travel U W.xo W.steps,ρ • SU.group.curvature (faceValue U W.face)); apply (collarAd_cont SU.group).comp (f:=T); unfold T faceValue; fun_prop
lemma collarReads {w:ℕ}(p:W.Pays r w)(U V:LinksC)(h:Agrees (skyDeck W.hub r) U V): W.collar ρ U=W.collar ρ V:=by
 unfold collar; rw [show travel U W.xo W.steps=travel V W.xo W.steps from travel_local _ _ _ _ (fun _ i w=> h _ (p.roomSites _ i) (p.roomSites _ w)), show faceValue U W.face=faceValue V W.face from travel_local _ _ _ _ (fun j i k=> h _ (p.faceSites (List.mem_toFinset.mpr i)) (p.faceSites (List.mem_toFinset.mpr k)))] -- p.roomSites order?

def docked (r:ℕ)(t:ℝ)(U:LinksC):ColorL := if landingC r W.hub t U then W.collar ρ U else 0
-- before overall Spin sum. normalize A and `/16` below. location o= matter index u
noncomputable def rungWeave (r:ℕ)(t:ℝ): Weaver:= fun N x=> wrapCurrent W.u W.spin 1 N (W.docked ρ r t (onC N x.1))
abbrev skyRent(r:ℕ) := skyDeck W.hub (r+8)
lemma docker {w:ℕ}(p:W.Pays r w)(t:ℝ)(i: SU.group.ColorIndex): Coeff true (W.skyRent r) ((fun x:LinksC=> (mug.coord i (W.docked ρ r t x):ℂ))∘Prod.fst):=by
 let F: LinksC→ℂ:=fun x=> mug.coord i (W.collar ρ x); let f : LinksC →ℂ:= fun x=> (mug.coord i (W.docked ρ r t x):ℂ); let U:=setOf (landingC r W.hub t)
 have he:Continuous F:=Complex.continuous_ofReal.comp ((mug.coord i).continuous_of_finiteDimensional.comp (collar_cont W ρ)); let g:=he.measurable; have hp:f= U.indicator F:=by
   funext x; by_cases h:x∈U; · rw [Set.indicator_of_mem h]; unfold f docked; rw [if_pos (show landingC r W.hub t x from h)]
   rw [Set.indicator_of_notMem h]; unfold f docked; rw [if_neg (show ¬landingC r W.hub t x from h)]; simp
 have hx:= land_meas r W.hub t; have hu:Envelope f:=by
   rw [hp]; obtain ⟨C,H⟩:= (Env.compact he).cost; refine ⟨g.indicator hx, |C|,fun x=> ?_⟩; by_cases h:x∈U; · rw [Set.indicator_of_mem h]; exact (H x).trans (le_abs_self _)
   rw [Set.indicator_of_notMem h,norm_zero]; exact abs_nonneg _
 refine ⟨fun h=>by contradiction,Env.along hu measurable_fst,fun V Q h _=>?_⟩
 change f V.1 = f Q.1; rw [hp]; have hf: V.1∈U ↔ Q.1∈ U:= voyage_local _ _ _ _ h
 by_cases y:V.1∈U; · rw [Set.indicator_of_mem y,Set.indicator_of_mem (hf.mp y)]; unfold F; rw [W.collarReads ρ p _ _ (fun i u v=>h i (pav_mono (show r ≤ r+8 by omega) u) (pav_mono (show r≤r+8 by omega) v))]
 rw [Set.indicator_of_notMem y,Set.indicator_of_notMem (mt hf.mpr y)]
lemma letterBudget (K:Calibration)(t:ℝ){w:ℕ}(p:W.Pays r w): InTest K true (W.skyRent r) false (household K (W.rungWeave ρ r t)):=by
 let G(i:SU.group.ColorIndex):= household K (holdC W.u W.spin 1 (mug i)); let V(i:SU.group.ColorIndex):=scalar K ((fun x:LinksC=> (mug.coord i (W.docked ρ r t x):ℂ))∘Prod.fst)
 rw [show household K (W.rungWeave ρ r t)=∑ i:SU.group.ColorIndex,V i*G i from ?_]
 · exact InTest.sum _ _ (fun i _=> (InTest.seed (W.docker ρ p t i)).mul (((Hiro.holdPass W.u W.spin 1 (mug i)).narrow K).widen.mono (singleton_subset_iff.mpr (pav_mono (show r ≤ r+8 by omega) (p.node W)))))
 funext N Y; simp only [Finset.sum_apply,Pi.mul_apply]; unfold V; simp_rw [scalar, Algebra.smul_mul_assoc,one_mul,Function.comp_apply]; let A:= W.docked ρ r t (onC _ Y.1); change wrapCurrent W.u W.spin 1 (K.c N) A=_; nth_rw 1 [show A=∑ i: SU.group.ColorIndex,(mug.coord i A) • mug i from (mug.sum_repr A).symm]; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl

abbrev gateS (r:ℕ)(n:Side):= halo r {wrap (More n) W.hub}
abbrev scope (n:Side): Site (More n):=wrap (More n) W.xo
abbrev localFace (n:Side): Face (Per (More n)) := (wrap (More n) W.face.1,W.face.2)
lemma budgetStop(n:Side) : stop (W.scope n) W.steps=(W.localFace n).1:= (wrap_stop_cover ..).symm.trans (congrArg (wrap _) W.stop_at)

def edgeBudget(n:Side)(U:Pane n):ColorL:=SU.group.adjoint (travel U (W.scope n) W.steps) (ρ • SU.group.curvature (faceValue U (W.localFace n)))
noncomputable def pearl(n:Side)(r:ℕ)(t:ℝ)(U:Pane n) : ColorL:= if pingS t (W.gateS r n) U then W.edgeBudget ρ n U else 0
lemma edge_on(n:Side)(U:Pane n): W.collar ρ (onC n U)=W.edgeBudget ρ n U:=by
 unfold onC collar faceValue edgeBudget; rw [travel_at,travel_at]; simp; rfl
lemma antenna(n:Side)(r:ℕ)(t:ℝ)(U:Pane n): W.docked ρ r t (onC n U)=W.pearl ρ n r t U:= by unfold docked pearl; rw [land_wrap,edge_on]
lemma onMark(n:Side)(r:ℕ)(t:ℝ)(U:Fields n): W.rungWeave ρ r t n U= wrapCurrent W.u W.spin 1 n (W.pearl ρ n r t U.1):= by unfold rungWeave; rw [antenna]
lemma dockGauge(n:Side)(r:ℕ)(t:ℝ)(V:Pane n)(g:Seat n→SU.E): W.pearl ρ n r t (gauge g V)= SU.group.adjoint (g (W.scope n)) (W.pearl ρ n r t V):=by
 unfold pearl; rw [pingB]; split; swap; · rw [map_zero]
 unfold edgeBudget; rw [face_gauge,SU.group.curvature_conjugate, ←map_smul, travel_gauge,W.budgetStop,← Gauge.adjoint_mul,← Gauge.adjoint_mul,inv_mul_cancel_right] -- cancel syntax
lemma oneVox (r:ℕ)(t:ℝ)(n:Side) : covariant (W.rungWeave ρ r t n):=by
 intro g x; rw [onMark,onMark]; let G:=W.pearl ρ n r t x.1; rw [show (simultaneous g x).1=Lattice.gauge g x.1 from rfl, show W.pearl _ _ _ _ _= _ from W.dockGauge ρ n r t x.1 g]; exact current_cov W.u W.spin 1 G x g
lemma registration (t:ℝ){w:ℕ}(K:Calibration)(_:W.Pays r w): Afterglow.Tower.CovCover K (household K (W.rungWeave ρ r t)):=by intro n; exact W.oneVox ρ _ t _

lemma spear (r:ℕ)(t:ℝ) (N:Side)(U:Fields N): W.rungWeave ρ r t N U=∑ b:SU.Slot,∑ c:SU.Slot, (-Complex.I*dMatter (SU.group.colorMat (W.pearl ρ N r t U.1)) b c) • (create (basisC N W.u (upSpin W.spin.1) b)*Fock.remove (basisC N W.u (dnSpin W.spin.2) c)):=by
 rw [onMark,Hiro.hold_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> ?_
 rw [Hiro.walk_price,Matrix.smul_apply,smul_eq_mul]; let X:= Twah.gold 1; let a:= create (basisC N W.u (upSpin W.spin.1) i); let b:= Fock.remove (basisC N W.u (dnSpin W.spin.2) j); change _ • (X • (b*a))=_ • _; rw [SitSpin.cr_swap]; unfold X Twah.gold; simp
#print axioms Staff.registration
#print axioms Staff.spear
end Staff
end YM.CF.Buffered.EmberWind
