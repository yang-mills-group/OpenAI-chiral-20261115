import YM.CF.Esti.Pie
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable (T:Tube G S)(r:ℕ)(t s:ℝ)(P:Finset (Cell f))(Q: Finset (Cell c))(V:Config G c)(U:Config G f)(M: Bond c→SU.group.Mat)
open Pressure.Tube
open Bloch Exterior
abbrev wV:= taken Q T.down T.low r S.patch.L.val s V
abbrev zF:=Pressure.zip (T.Φ r V) (wV T r s Q V)
abbrev zI:=Pressure.zip (T.Φ' r V) (wV T r s Q V)
abbrev kZ(i:Bond c):=Real.sqrt S.kernel.penalty • curvatureL G (M i)
abbrev kF(i:Cell f):=king P T.up T.high r 1 t U i+∑ j:Bool,(‖zF T r s Q V (i,j)‖^2/2-inner ℝ (zF T r s Q V (i,j)) (T.Xf r U (i,j)))
abbrev kI(i:Bond c) := S.kernel.penalty*fareG G (M i) + (‖zI T r s Q V i‖^2/2 - inner ℝ (zI T r s Q V i) (kZ (S:=S) M i))
abbrev kC(i:Cell c):= (∑ j:Bool, (inner ℝ (wV T r s Q V (i,j)) (T.Xn r V (i,j)) - ‖wV T r s Q V (i,j)‖^2/2))- king Q T.down T.low r S.patch.L.val s V i
abbrev kL(i:Cell c):= ∑ j:Bool, inner ℝ (wV T r s Q V (i,j)) (unzip (T.Φ r V) (T.Xf r U) (i,j)+unzip (T.Φ' r V) (kZ (S:=S) M) (i,j)-T.Xn r V (i,j))
abbrev kN (i:Co c Gain):=‖zip (T.N r V) (wV T r s Q V) i‖^2/2
abbrev kD (i:Cell c):= ∑ j:Bool, inner ℝ (wV T r s Q V (i,j)) (wV T r s Q V (i,j)-(unzip (T.Φ r V) (zF T r s Q V) (i,j) + unzip (T.Φ' r V) (zI T r s Q V) (i,j) + unzip (T.N r V) (zip (T.N r V) (wV T r s Q V)) (i,j)))/2
-- exact compare within one window. W support reused.
def ore (H: Affine.Window S):ℝ:= (∑ i∈ H.face,kF T r t s P Q V U i)+(∑ i∈H.noise, kI T r s Q V M i)+(∑ i∈ H.coarse,(kC T r s Q V i+(kL T r s Q V U M i+kD T r s Q V i)))+ (∑ i∈H.rows, kN T r s Q V i)
-- compare has from locally implied vision of whole V and selected masks P far. z and grant. proof connectivity. predicates Work.Window
variable {T r t s P Q V U M}
def wit (V:Config G c)(Q:Config G c)(i:Bond c):SU.group.Mat:= SU.group.mat (V i*(Q i)⁻¹)
private lemma stipend_q (H:Config G c)(i:Bond c)(p:M i=wit V H i): fareG G (M i)= Pressure.wire H V i^2/2 ∧ kZ (S:=S) M i=Tube.Z S H V i:=by
 rw [p,wit,fare_h]; unfold Pressure.wire; rw [SU.group.chord_price]; constructor; ring; unfold kZ; rw [p]; rfl
lemma zI_span (e:Bond c)(j:Twin c)(h:r < separation e.1 j.1.1): T.Φ' r V e j=0:=by
 let R:=r; have hl k (h : k*S.patch.L.val ≤ R) : k ≤ R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property) h
 have hf(u:Cover): priced r S.patch.L.val V T.R.mn (Pressure.pole e) (Pressure.mesh j) u=0:=by
    unfold Pressure.priced; split
    next hv =>
        have hx : stop (Pressure.pole e).1 (route 0 u 1) = (Pressure.mesh j).1 := by
          rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (Pressure.pole e).1 0 u
        have he : separation (Pressure.pole e).1 (Pressure.mesh j).1 ≤ r := by rw [← hx]; exact (Work.E03.sep_walk (fun x : Site c=>x) Work.E03.sep_step ..).trans (hl _ hv.1)
        exact (h.not_ge he).elim
    rfl
 simp only [Tube.Φ',Pressure.kick,Pressure.lane,hf,tsum_zero]
lemma exact_o(x:ℝ)(p:Affine.Window S)(k:S.Choices)(ht:0<temp x)(h:0<fiery G x S.patch.L)(hV:∀ i:Cell c,Pressure.toll V i > temp x → i∈Q)(hU:∀ i∈p.face,(pers P T.high (fiery G x S.patch.L) U i.1 ↔ PathData.kept T.high (fiery G x S.patch.L) i.1 U) ∧ (i∈P ∨ Pressure.toll U i ≤ fiery G x S.patch.L))(hK:∀ i∈p.noise,M i=wit V (S.prediction U k) i)(hz:∀ i∈p.coarse,∀ e:Bond c,separation e.1 i.1 ≤ Stores.till x → M e=wit V (S.prediction U k) e): ore T (Stores.till x) (fiery G x S.patch.L) (temp x) P Q V U M p=p.work T x U k V:=by
 let t:=temp x; let f:= fiery G x S.patch.L; let r:=Stores.till x; let R:=wV T r t Q V; let A:=S.prediction U k
 have hf(i: Site c):pers Q T.low t V i↔ PathData.kept T.low t i V:=by
    apply persR _ _ _ _ _ ht.le; intro j e; have ht' := T.low.radius_pos; apply hV; refine lt_of_le_of_lt ?_ e; exact le_mul_of_one_le_right ht.le (Real.one_le_exp (by positivity))
 have hh(i: Cell c): i∈ Q∨Pressure.toll V i ≤ t:=by by_cases p:i∈Q; exact Or.inl p; exact Or.inr (le_of_not_gt (fun l=>p (hV i l)))
 have he:R=T.vision r t V:=funext fun i=> takes_q _ _ _ _ _ _ _ _ ht.le (hf _) (hh _)
 unfold ore Affine.Window.work onWindow; congr 1 -- tune
 · congr 1
   · congr 1
     · refine Finset.sum_congr rfl fun i l=> ?_; change king P T.up T.high r 1 f U i+ ∑ j:Bool,(‖zip _ R _‖^2/2-inner ℝ (zip _ R _) _)= _; rw [crownK _ _ _ _ _ _ _ _ h.le (hU i l).1 (hU i l).2,he]; rfl
     apply sum_congr rfl; intro i l; obtain ⟨g,v⟩:=stipend_q (S:=S) _ _ (hK i l); unfold kI; rw [g,v]; unfold workI monetary; congr 1; ring; unfold zI; rw [show wV T (Stores.till x) (temp x) Q V=_ from he]; rfl -- tune
   refine sum_congr rfl fun i l=> ?_
   
   have H(j:Bool):unzip (T.Φ' r V) (kZ (S:=S) M) (i,j)=unzip (T.Φ' r V) (Tube.Z S A V) (i,j):=by
      refine sum_congr rfl fun e g=> ?_; by_cases k:separation e.1 i.1 ≤ r; · rw [(stipend_q (S:=S) _ e (hz i l e k)).2]
      rw [zI_span e (i,j) (lt_of_not_ge k)]; simp
   unfold kC kL kD workC workL workD Mw Mv zI zF
   simp_rw [show wV T (Stores.till x) (temp x) Q V=T.vision r t V from he, crownK Q _ _ _ _ _ _ i ht.le (hf i.1) (hh i)]; unfold r at H; simp_rw [H]; rfl
 refine sum_congr rfl fun i l=>?_ ; unfold kN workN; rw [show wV T (Stores.till x) (temp x) Q V=_ from he]
end YM.CF.Esti
