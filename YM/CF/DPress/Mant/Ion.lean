import YM.CF.DPress.Loch.Indian
import YM.CF.DPress.Hues.Tor
import YM.CF.Coal.Veil
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{t:Yds (mid P B)}{v:ℂ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}(m:Penny Q O)
 (Y:Pony x C O)(E:Lobby Q O β)
namespace Penny
open Salt Oise Quality
-- stipend Fv
abbrev ηy (j:Roc (mid P B)):=actionZ E.Y j 1
abbrev tapv (m:Penny Q O) (β:ℝ)(j:Youth N P B)(T':Pane (mid N B)): Cipher (mid P B) →L[ℂ] FC (Dwell (mid N B)) := (FloatQ j.2.2.1 j.2.2.2 T').comp (σFilm (H:=m.H β) (Y:=Q.Y) (X:=m.X' β) V m.M C.D_ m.arch C.C' C.s C.Jp j)
lemma πray(j:Youth N P B)(T':Pane (mid N B)): (m.Fv Y E j T').val=m.tapv β j T' (ηy E j.1):=by
 rw [m.𝔣]; apply congrArg (cars_P j.2.2.1 j.2.2.2 T'); rw [𝓖,bothH]; rfl -- bothH unroll reference.K.Clock.Tr
lemma φGone(k:Youth N P B)(p:k∉m.Forge E): m.Fv Y E k=0:=by
 funext i; apply Subtype.ext; rw [m.𝔣,show m.𝓖 E k=0 from not_not.mp fun t=> p (mem_filter.mpr ⟨mem_univ _,t⟩),thaw_v]; rfl
lemma limits (p:Youth N P B→Prop)[DecidablePred p]:(∑ k∈m.Forge E with p k,m.Fv Y E k)=∑ k with p k,m.Fv Y E k:=sum_subset (filter_subset_filter p (subset_univ _)) fun k v h=> m.φGone Y E k (fun x=> h (mem_filter.mpr ⟨x,(mem_filter.mp v).2⟩))
-- fixed index gear for ZL
lemma sootH : m.QL Y E= soot_T univ ref_A (ref_B x) (ref_Q x) (oV∘m.Fv Y E):=by
 unfold QL soot_T; refine sum_subset (subset_univ _) fun i v p=>?_ ; simp_rw [Function.comp_apply,m.φGone Y E i p]; have he(X:Aura (mid N B)): Vow.flick X (oV (0:Pane (mid N B)→ Cipher (mid N B)))=fun t=>0:=funext fun j=>by unfold Vow.flick; split<;>rfl
 unfold stroke chasmR; rw [he,he]; simp; rfl
variable (H:Léon Q.Y.p C.h R.L.val E.F0 b)
-- actual budget at zero
variable (h0:E.F0.1=0)
include h0
lemma action_zero (j:Roc (mid P B)): actionZ E.Y j=0:=by unfold actionZ; split; rw [show E.Y.F=0 from h0]; rfl; rfl -- bullets
lemma null_fv (j:Youth N P B): m.Fv Y E j=0:=by funext T'; apply Subtype.ext; rw [m.πray,ηy, action_zero E h0]; exact map_zero _
include Y
lemma zero_hy (j:Roc (mid P B))(i:Aura (mid N B)): m.Uφ E (subtK S j) i=0:= Coal.still (Xs:=m.X' β) (Y:=E.Y) V C.F C.Z U W m.PP (m.H β) (E.FendX m) m.ht E.Base j (beamH i.val) (action_zero E h0 j) _ ((m.gro_p E).quiet _ _).toLullT
lemma zero_L : m.TL Y E=0:=by
 rw [TL]; have he:m.Ty Y E=0:=by
    funext T; unfold Ty sunY Eρ; simp_rw [m.zero_hy Y E h0]; exact sum_eq_zero fun i _=> by funext U; unfold car_A; rw [Finset.sum_apply]; simp [m.null_fv Y E h0]
 rw [he,zero_add]; funext T; unfold TC EdvP sunY tray_R; change (∑ i:Crown_L (mid N B) with EpR x i = T,_)=0; simp_rw [m.null_fv Y E h0]; simp -- check
omit h0
variable (E₁ F: Lobby Q O β) (g:F.F0.1=E₁.F0.1-E.F0.1)
include g
lemma fv_re (j:Youth N P B): m.Fv Y E₁ j- m.Fv Y E j=m.Fv Y F j:=by
 funext T; apply Subtype.ext; change (m.Fv Y E₁ j T).val-(m.Fv Y E j T).val=(m.Fv Y F j T).val; simp_rw [m.πray Y]; rw [← map_sub]; refine congrArg _ ?_; unfold ηy actionZ; split; change _=F.F0.1 _ _; rw [g]; rfl; exact sub_zero _
lemma priceC_sub : m.TC Y E₁-m.TC Y E=m.TC Y F:=by
 funext i; unfold TC EdvP; change _-_= sunY univ (EpR (N:=mid N B) x) _ i; simp only [Pi.sub_apply,sunY,tray_R]; -- expand filters Forge
 simp_rw [m.limits Y E]
 simp_rw [m.limits Y E₁,m.limits Y F]; rw [←sum_sub_distrib]; refine sum_congr rfl fun j p=>?_ ; rw [←sum_sub_distrib]; exact sum_congr rfl fun j _=> m.fv_re Y E E₁ F g j -- unfreeze
end Penny
end YM.CF.Py.Kay
