import Anomaly.Cover.Portrait
import Anomaly.Cover.Layer
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option synthInstance.maxSize 26000
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
open Proscenium
variable (P:Spine)
local notation "V!"=>P.calibration
local notation "N₁" i:max=>V!
-- explicit unscaled joint object.Papers. Y rhs on compass invoices.No nr.These C represent gauge dossier of top.Flow.extension.
variable (s m:ℕ)
local notation "W"=>P.roomFox s m
local notation "U"=>Tapestry.Swatch W
local notation "E'"=>render W V!
local notation "F" i:max=> hat P.par.R.L P.par.x i
open Mew Pressure
abbrev knot_q(P:Spine)(s:ℕ):ℝ:= pinpr P.par.R.L (hat P.par.R.L P.par.x s)/(temp (hat P.par.R.L P.par.x s))^2
abbrev caseZ (Q:Proscenium→ U):= ((knot_q P s):ℂ) • (Q Proscenium.tick+ ∑ i:Axis,(Q (Proscenium.nudge i true)-Q (Proscenium.nudge i false)))
private lemma pricingR {n:Side}(b:BudgetPoint)(K:Scree.Loom n)(X:SOp n)(Y:Axis→ SOp n): jointMark b K 0 m (co_Ψ 0 0 X) (fun i=>co_Ψ 0 0 (Y i))=jointMark b K 0 m X Y:=by
 have ht(o:Site n)(x y:SOp n)(p:∀ V:Pane n,x (Tulip.profile V)=y (profile V)): pinMatrix b K (node o) x=pinMatrix b K (node o) y:= by unfold pinMatrix; simp_rw [p]
 unfold jointMark; refine congrArg₂ (fun (x y:Mark n)=>x+y) ?_ ?_
 · unfold gaugeMark traceMeter; rw [ht 0 (co_Ψ 0 0 X) X (co_unit 0 X)]
 unfold diffMark; have hp(A:SOp n)(x:Site n) : moveMark b K 0 x (co_Ψ 0 0 A)=moveMark b K 0 x A:=by
    unfold moveMark spinMark; apply funext; intro i; rw [ht _ _ _ (fun V=>(show _ from co_compose x 0 0 A V))]
 exact sum_congr rfl fun j _=> congrArg₂ (fun (x y:Mark n)=>x-y) (hp (Y j) _) (hp (Y j) _)

lemma purchase_id (i k:ℕ)(X:SOp (age P.run i s))(Y:Axis→ SOp (age P.run i s)) :
 purchaseY (i:=i) (s:=s) P.run 0 X Y k m= (knot_q P s:ℂ) • jointMark (RootBook P.run i k s).p ((P.run.voyage i).CapeT s) 0 m X Y:=by
 let V:=P.run; let n:= age P.run i s; let b:= (RootBook P.run i k s).p; let K:= (P.run.voyage i).CapeT s
 exact congrArg ((knot_q P s:ℂ) • ·) (pricingR m b K X Y) 

variable {B t:ℕ→ℕ}{A:ℕ→Proscenium→ Tapestry.Swatch (P.roomFox s m)}{G:Proscenium→Tapestry.Swatch (P.roomFox s m)}
variable {X:(j:ℕ)→SOp (age P.run (P.nomadic (B j)) s)} {J:(j:ℕ)→Axis→ SOp (age P.run (P.nomadic (B j)) s)} (u:OnTape P s m B X J t A G)
-- bundle.
include u
lemma wind_here (j:ℕ)(e : s<P.run.uv (P.engine (B (t j)))) :
 exhibit P.run P.large s (P.nomadic (B (t j))) ((E') (P.caseZ s m (A j)))= purchaseY (s:=s) (i:=P.nomadic (B (t j))) P.run 0 (X (t j)) (J (t j)) (P.engine (B (t j))) m:=by
 rw [←present_exhibit]; unfold caseZ; rw [map_smul,map_add, map_sum]; simp_rw [map_sub,u.issued]; rw [purchase_id,show (RootBook P.run _ _ _).p=_ from (Papal.prices_plot P.run _ _ _ e.le).1]; exact congrArg ((knot_q P s:ℂ) • ·) (pairingShow ..)
set_option synthInstance.maxHeartbeats 160000 in
lemma sponsor_means : BQueue (P.roomFox s m) (fun j=> render W V! (P.caseZ s m (A j))) (render W V! (P.caseZ s m G)):= by
 refine queue_V _ ((Tendsto.add (u.distance .tick) ?_).const_smul (knot_q P s:ℂ)); exact tendsto_finsetSum _ (fun i _=>(u.distance _).sub (u.distance _))
variable {r a:ℝ}(p0:PinnedW P.run s (P.nomadic∘B) (P.engine∘B) m r a X J)(hr:0≤r) (p:Tendsto B atTop atTop)
include p p0 hr
-- Mark identity on output stencils.G.X.
lemma outprint : render W V! (P.caseZ s m G)= (knot_q P s:ℂ) •
    (render W V! (G Proscenium.tick)+ ∑ i:Axis,(chime V! i (costN true m) (render W V! (G (.core i)))-chime V! i (costN false m) (render W V! (G (.core i))))):=by unfold caseZ; rw [map_smul,map_add,map_sum]; simp_rw [map_sub,nudgeMoves P _ u p0 p hr]
omit p p0 hr
lemma determinantProbe (n:Side)(h:∀ j,Roomy W (age P.run (P.nomadic (B (t j))) s)) (v:Fields (P.calibration.c n)): gaugeAccount P s m G n v=(knot_q P s:ℂ) • ∑ i:Signed,(dollar i:ℂ) • render W V! (G Proscenium.tick) n (flashA (gridTulip i 0) v.1,flashA (gridTulip i 0) v.2):=by
 unfold gaugeAccount preVote; rw [map_sum]; simp_rw [map_smul,Pi.smul_apply, Finset.sum_apply,Pi.smul_apply]; apply congrArg; apply sum_congr rfl; intro i _; rw [poseVote P i u h n v]
lemma guilder : Neutral V! (gaugeAccount P s m G)∧Licor (P.roomFox s m) V! (P.gaugeAccount s m G):=by
 let R:= (knot_q P s:ℂ); let f(i:Signed): Family V! := render W V! (G (.gauge i)); have ht(i:Signed):= u.deckV (.gauge i); choose φ ψ v using fun i:Signed=> (ht i).2.2 (Or.inr ⟨i,rfl⟩)
 let Q:= fun z:LinksC=> R*∑ i:Signed,(dollar i:ℂ)*φ i z
 have hx : (gaugeAccount P s m G)= R • ∑ i:Signed,(dollar i:ℂ) • f i:=by unfold gaugeAccount preVote; simp_rw [map_sum, map_smul]; rfl
 refine ⟨?_,Q,?_, ?_⟩
 · rw [hx]; refine (covariant_scale P.calibration (A:=∑ i:Signed,(dollar i:ℂ) • f i) (?_) R); have he(i:Signed): f i ∈ observ P.calibration W true:= ⟨texture ..,(ht i).1⟩; exact ((obs_in _ _ _ _).1 (show ∑ i:Signed,(dollar i:ℂ) • f i∈ observ P.calibration W true from (observ _ _ _).sum_mem (fun i _=>(observ _ _ _).smul_mem (he i) _))).2
 · -- coeff scaled.Scope precise no closure assumption
    refine ⟨fun _=>by contradiction, ?_,fun x y h l=>?_⟩
    · have e(i:Signed):= Girt.pole_w _ (fun z:ℂ=> (dollar i:ℂ)*z) (by fun_prop) (ψ i).env; choose C b using fun i=> (e i).cost
      have ht:Envelope (fun x:PairsC=>∑ i:Signed,(dollar i:ℂ)*φ i x.1):=⟨Finset.measurable_fun_sum _ fun i _=>(e i).meas, ∑ i:Signed,C i, fun x=> (norm_sum_le ..).trans (sum_le_sum fun i _=> b i x)⟩
      exact Girt.pole_w _ (fun v:ℂ=>R*v) (by fun_prop) ht
    exact congrArg (R*·) (sum_congr rfl fun i _=> congrArg ((dollar i:ℂ)*·) ((ψ i).locus x y h l))
 rw [hx]; funext n z; have e(i:Signed):f i= scalar P.calibration (φ i ∘ Prod.fst):= v i; simp only [Finset.sum_apply,Pi.smul_apply,e]; unfold scalar Q; simp only [Function.comp_apply]; rw [mul_smul, Finset.sum_smul]; apply congrArg; apply sum_congr rfl; intro i _; rw [mul_smul]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
