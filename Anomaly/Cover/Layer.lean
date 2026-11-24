import Anomaly.Cover.Court
import Anomaly.Framing.MarkFrame
import Anomaly.Pose
set_option maxHeartbeats 850000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Swell Sonar StageQ Ione Vow Tapestry.StageW
namespace Spine
universe u
/-! actual stencil geometry for points in (128).^s gauge translation paired costs all. establish chosen.J moves for continuum E readers. -/
open Tapestry.StageW Sour
variable (P:Spine)
local notation "W"=>P.calibration
variable (i:Axis)(q:ℤ){N:Side}
lemma spinVis : tagMove i 0 N * tagMove i q N= taxiPlus (-(wrap N (q • step i))):=by
 let s:= Signed.mirror i; let b:=wrap N (q • step i); change Sweep.mk (s*s) ((wrap N (0 • step i)) + s.act b) _=Sweep.mk 1 (-b) false; rw [show s*s=1 from (by unfold s; nth_rw 1 [← Signed.mirror_inv i]; exact inv_mul_cancel s),zero_smul,map_zero,zero_add]; congr 1; ext j; by_cases h:j=i
 · subst j; simp [s,Signed.act,Signed.mirror]
 simp [s,Signed.act,Signed.mirror,h,Ne.symm h,b]
-- possible `sp` order. use Mark grammar supports. inverse flight gives TAXI. 
lemma lot_φ (t:Site N)(x:FC (Single N)) : Hive.teen (taxiPlus t) x=twist (quantU (γS (taxiPlus t))) x:=by
 unfold Hive.teen Hive.yodel; rw [show detX (castX (taxiPlus t)).s=false from det_i]; try rfl
lemma visa_spin (F:Mark N) (S:Support (More N))(p:AtSupport false S F): reflMark i q (reflMark i 0 F)=flyMark (taxiPlus (-(wrap N (q • step i)))) F:=by
 let h:= flies_theta (i:=i) (V:=F) S 0 p; rw [←h]; have he:= whirl_step (tagMove i 0 N) _ rfl p; rw [←flies_theta _ i q he,fliesCombine _ S _ p,spinVis]
lemma taxi_neg (N:Side)(a:Site N): (taxiPlus (-a))⁻¹=taxiPlus a:=by apply (mul_left_cancel (a:=taxiPlus (-a))); rw [mul_inv_cancel,taxi_chain,neg_add_cancel]; try rfl -- direction tune
variable {b:Bool}{k r m:ℕ}{l d a c:ℝ}{K:Scree.Loom N}{D:BudgetPoint}
variable {X:SOp N}(h:Roof N c d r K)(p:Trunk (node (0:Site N)) X k l a d)(hd:0<d)(l0:0 ≤ l)(g:D.threshold ≤ c)(u:k+r+10≤D.B)
abbrev costN(b:Bool)(m:ℕ):ℤ:=if b then m else -(m:ℤ)
lemma nudges (b:Bool)(m:ℕ)(i:Axis):alongM m (0:Site N) i b=wrap N (costN b m • step i):=by unfold alongM costN; cases b <;> simp only [↓reduceIte,Bool.false_eq_true,gapPlus,zero_sub,zero_add,map_zsmul,map_neg,map_nsmul,wrap_step,neg_smul,Nat.cast_smul_eq_nsmul ℤ] -- tune
include h p hd g u l0
lemma matrixCoverSilhouette (i:Axis) (m:ℕ)(b:Bool):
 reflMark i (costN b m) (reflMark i 0 (spinMark D K 0 X))=moveMark D K 0 (alongM m 0 i b) X:=by
 let t:= spinWindow _ h hd p g u l0; rw [visa_spin _ _ _ _ t.ticket]
 let x:= alongM m (0:Site N) i b; let Z:= co_Ψ x 0 X; let Q:= spinMark D K x Z; let G:=taxiPlus x; let F:= spinWindow _ h hd (p.station x) g u l0
 funext y; rw [←nudges]; unfold flyMark; rw [taxi_neg]
 let j':= (γS (taxiPlus x)); have he : G⁻¹=taxiPlus (-x):= by apply inv_injective; rw [inv_inv,taxi_neg]
 let y':= (flashA G y.1,flashA G y.2)
 have ht: twist (quantU j') (Q y)=spinMark D K 0 X y':= by
    have Hv:= spin_taxi (0:Site N) x h hd p (p.station x) g u (fun _=>rfl) y
    rw [sub_zero] at Hv; exact Hv
 change Hive.teen (taxiPlus (-x)) (spinMark D K 0 X y')=_; rw [←ht,← lot_φ]
 have hy:= paritySale.checked ((F.ticket.allV y).sector) -- names
 change Hive.teen _ (Hive.teen G _) = Q y; rw [←he, Hive.yetL G G⁻¹ (Q y) hy, mul_inv_cancel,Hive.lot_i _ hy]
section
omit p h l0 u hd g
variable {d m:ℕ}{B t:ℕ→ℕ}{A:ℕ→Proscenium→Tapestry.Swatch (P.roomFox d m)}{F:Proscenium→Tapestry.Swatch (P.roomFox d m)}
variable {X:(j:ℕ)→ SOp (age P.run ((P.nomadic∘B) j) d)}{J:(j:ℕ)→ Axis→ SOp (age P.run ((P.nomadic ∘ B) j) d)} (w: OnTape P d m B X J t A F)
local notation "rS"=>roomFox P d m
variable {a b:ℝ}(T:PinnedW P.run d (P.nomadic∘B) (P.engine∘B) m a b X J)(x: Tendsto B atTop atTop)(hp:0 ≤ a)
private lemma exhibit_chime (j:ℕ)(Q:Family W)(σ:ℤ) : exhibit P.run P.large d (P.nomadic j) (chime W i σ Q)=reflMark i σ (reflMark i 0 (exhibit P.run P.large d (P.nomadic j) Q)):= by let g:=terrain P.run P.large (P.run.ir (P.nomadic j)) d; change arrange _ _ g (reflMark _ _ (reflMark _ _ _))=reflMark _ _ (reflMark _ _ (arrange _ _ g _)); rw [displayRef g,displayRef g]; try rfl
local notation "η"=>P.nomadic
include w T x hp
lemma cameoMoves (v:Bool):∀ᶠ j:ℕ in atTop, chime W i (costN v m) (render rS W (A j (.core i)))=render rS W (A j (.nudge i v)):=by
 let g(j):= B (t j); let D:=η∘g; let a:=costN v m; let S:= rS ∪ address i a rS
 let Tc(j):= render rS W (A j (.core i)); let U(j):= render rS W (A j (.nudge i v))
 filter_upwards [(P.stockGo.comp (x.comp w.advance.tendsto_atTop)).eventually (roomyTail P.run P.large d S)] with j H
 let r:= g j; let m':= momentm P.run (η r) d; let γ:=terrain P.run P.large (P.run.ir (η r)) d
 have ht : chime W i a (Tc j) m'=U j m':=by
    apply (arrange (P.calibration.c m') _ γ).injective
    change exhibit P.run P.large d (η (g j)) (chime W i a (Tc j))=exhibit P.run P.large d (η (g j)) (U j)
    unfold Tc U g; obtain ⟨e,g,H1,y,p,G⟩:=T (t j)
    rw [exhibit_chime,←present_exhibit,←present_exhibit,w.issued,w.issued]; rw [←(show (RootBook P.run (P.nomadic (B (t j))) _ _).p=P.run.meter.a d from (Papal.prices_plot P.run d _ _ e.le).1)]
    exact matrixCoverSilhouette G.pulse.roof (G.ropes.tubes.hatJ i) P.par.dpos hp G.pulse.reach G.capR i m v -- tune
 exact looksLike (S:=S) (γ ▸ (Roomy.seats H)) ((flow_port W i a (texture ..)).mono subset_union_right) ((texture ..).mono subset_union_left) ht
lemma nudgeMoves(v:Bool): chime W i (costN v m) (render rS W (F (.core i)))=render rS W (F (.nudge i v)):=by
 let t':=w.deckV (.core i); let f:=w.deckV (.nudge i v); funext z j
 refine tendsto_nhds_unique_of_eventuallyEq (carriesC ((t'.2.1.revolve i 0).revolve i (costN v m)) z j) (carriesC f.2.1 z j) ((cameoMoves P i w T x hp v).mono fun i t=>?_) -- use revolutions twice

 exact congrFun (congrFun t z) j
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
