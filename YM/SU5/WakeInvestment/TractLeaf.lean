import YM.SU5.WakeInvestment.Junct
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

open WakeInvestment Gleam.Wake
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ)
local notation "X" s:max => hat P.R.L P.x s
local notation "χ" s:max c:max => WakeInvestment.chip (hat P.R.L P.x s) c
local notation "Θ" T:max=> tollR T
local notation "Υ" T:max=> tabμ T
local notation "wax" s:max=> (Υ (θ s))
local notation "ℓop" s:max i:max k:max t:max=> (WakeInvestment.weighted (spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))) t (flatShear Y s i k))

variable {b d m p B:ℕ}{I:ℝ}
variable {L:List (Hookah (side Y i s))}{φ:Fin L.length → Pane (side Y i s) →ℝ}
variable {α:ℝ} {F:Hookah (side Y i s)} {H:Real.exp 1≤P.x}
/-! # Foil-invariant arity leases. Point Warp enrollment: planning at the actually-issued α.

Unlike `LightBar` requires not just estimates on low-degree approximation but **fixed arity** even
on uncut $U$. Useful for raw Mark estimators. No claim in using this transfer for the Tails of R
in Ward price.
-/

open Window
variable {E C v:ℝ} {α:ℝ} {D:ℕ} {F₀:Hookah (side Y i s)}
local notation "PP" x:max => possession (n:=side Y i s) x

structure LampPose (α C:ℝ) (D m:ℕ)(F:Hookah (side Y i s))(φ:Pane (side Y i s)→ℝ) : Prop where
 owner: AtSupport false F.S F.x
 weld: covariant F.x
 cost: ∀ x, Cadre (modesIn _ F.S) m C (F.x x-1)
 size: F.S.card≤D
 fee: ∀ U:Fields (side Y i s), ordinary (n:=side Y i s) (possession (n:=side Y i s) F.S) (α*(RootBook Y i k s).p.threshold) U.1 → Tiny F.S U.1 (skyline (X s)) → (noble Y s i k (F.x U-1)).re ≤ φ U.1+tabμ (X s)

variable {φ:Pane (side Y i s)→ℝ} (uB:LampPose Y s i k α C D m F φ)
include uB
lemma LampPose.can (p: CorridorFee Y s i k E m) (l:C*sizeRent m D ≤ χ s (-199)): LightBar Y s i k m α F φ:=by
 let n:=side Y i s; let S:= F.S; have hc:0≤ C:= (norm_nonneg _).trans (uB.cost (1,1)).price
 have hE(x:Fields n):Lyrics (modesIn n S) m (χ s (-199)) (F.x x-1):= (uB.cost x).output.expend le_rfl (l.trans' (mul_le_mul_of_nonneg_left (size_issue uB.size m) hc))
 refine ⟨uB.owner,uB.weld,fun x t a q=>?_,fun x b h=>?_⟩
 · exact ((hE x).post _ (p.investBook t (by rwa [abs_of_nonneg a])) p.visa).trans p.sizeB
 exact ⟨_,0,hE x,(add_zero _).le.trans (uB.fee x b h),fun t _ _=>by rw [sub_self,norm_zero]⟩
omit uB
lemma tugTiny (U:Pane n){S:Support (More n)}(t:Signed)(b:Seat n)(hf:Tiny (S.image (affine t b)) U v) : Tiny S (pull t b U) v := by
 rintro ⟨x,i⟩ e g; let d:=(posDir i).rotate t; let B:= (S.image (affine t b)); let y:=affine t b x; have hp:y∈B:= mem_image_of_mem _ e; have hv:y+d.vec∈ B:= by
    rw [show y+d.vec=affine t b (x+step i) from ?_]; exact mem_image_of_mem _ g
    unfold y d; rw [Step.vec_rotate,Step.vec_pos]; unfold affine; rw [Signed.act_add]; abel
 change SU.group.chord (d.read U y) ≤ v; generalize e:d=A at *; obtain ⟨i,b⟩:=A; cases b; · exact hf (y,i) hp hv
 change SU.group.chord (U (y-step i,i))⁻¹ ≤ _; rw [Gauge.chord_inv]; exact hf (y-step i,i) (show y-step i∈ B from (by simpa [sub_eq_add_neg,Step.vec] using hv)) (by change _ ∈ B; change y - step i + step i ∈ B; rwa [sub_add_cancel])
lemma tugSmall (U:Pane n){S:Support (More n)}(t:Signed)(b:Seat n)(p:ordinary (possession (n:=n) (S.image (affine t b))) v U) : ordinary (possession (n:=n) S) v (pull t b U):=fun i u => by
 rw [Face.send_price U i t b SU.group.chord SU.group.chord_inv (fun _ u=> SU.group.chord_conj u _)]
 exact p _ (mem_filter.mpr ⟨mem_univ _, (Work.H03.touched_send t b i) ▸ image_subset_image ((mem_filter.mp u).2)⟩)

include uB
lemma LampPose.forMirror (u:evenPose Y s i) (t:ℤ)(j:Axis) : LampPose Y s i k α C D m (F.twistL j t) (φ ∘ fling j t (N s i)):=by
 let U:= carR j t (N s i); let T:=F.twistL j t; let V(x:Fields (N s i)):= F.x (reflFields j t x)-1
 have h(x):T.x x-1=Fock.theta U (V x):=by unfold V; rw [Fock.theta_sub, theta_one]; rfl
 refine ⟨uB.owner.refl j t,covariant_reflected uB.owner uB.weld t j, fun x=>?_,card_image_le.trans uB.size,fun x v w=>?_⟩
 · rw [h x]; exact (uB.cost (reflFields j t x)).march _ (refl_modes j t F.S)
 let y:= reflFields j t x; let z:=wrap (More (N s i)) (2 • (t • step j)); let l:=Signed.mirror j; have p := uB.fee y (tugSmall (n:=side Y i s) x.1 (S:=F.S) l z v) (tugTiny (n:=side Y i s) x.1 (S:=F.S) l z w)
 have hm: noble Y s i k (Fock.theta U (V x))=star (noble Y s i k (V x)):=by
    rw [noble_linear, noble_linear]; exact mirror_fare j t u (preparedFlat Y s i k) (preparedFlat Y s i k) (fun _=> V x)
 rw [h x,hm,Complex.star_def,Complex.conj_re]; exact p
variable {c:Side}{r:Ratio c (More (side Y i s))}
omit uB
lemma seePullTag (t:Signed)(b:Site (More (N s i))) (D:Support (More (N s i)))(w:LeadVision Y s i k α c r D φ) : LeadVision Y s i k α c r (D.image (affine t b)) (φ ∘ (pull t b)):=by
 let G:=RootBook Y i k s; let n:=side Y i s;
 refine ⟨⟨w.env.meas.comp (prior_pull t b).measurable,w.env.cost.choose, fun _=> w.env.cost.choose_spec _⟩,fun x=> w.price_ _, Push.Local.invariant_pull w.inv _ _,?_⟩
 intro s a T; let f:= (s*t); let u:= affine s a b; rw [show T=D.image (affine f u) from ?_];
 · simp_rw [Function.comp_apply,pull_pull]; exact w.lead f u
 unfold T; rw [image_image]; congr 1; exact funext fun x=>by simp [affine, Signed.act_mul, u, f, add_assoc] -- argument x
include uB
lemma LampPose.all (u:evenPose Y s i) (w:LeadVision Y s i k α c r F.S φ)(J:Hookah (N s i))(l:Foil F J) : ∃ φ:Pane (side Y i s)→ℝ,LampPose Y s i k α C D m J φ ∧ LeadVision Y s i k α c r J.S φ := by
 induction l with
 | base=> exact ⟨φ,uB,w⟩
 | @mirror K g j t ih=> obtain ⟨f,h,h'⟩:=ih; refine ⟨_,h.forMirror Y s i k u t j,?_⟩; let l:=Signed.mirror j; let b:= wrap (More (N s i)) (2 • (t • step j)); exact seePullTag Y s i k l b K.S h'
omit uB
lemma LampPose.receipt (u:evenPose Y s i) (p: ViewTickets (E:=E) Y s i k H m I) (e:C*sizeRent m D ≤ χ s (-199))(hp:(B:ℝ)≤ sPow P s I)(t:C≤1)
    (w:AtSupport false F.S F.x) (a:∀ j,cows j F.S B)(W:ℂ)(Xh:∀ z:ℂ, ‖z‖= leafCost (P:=P) s→ ∃ φ:Pane (N s i)→ℝ,LampPose Y s i k α C D m (sleeve F W z) φ ∧ LeadVision Y s i k α c r F.S φ) : ProofLease Y s i k α c r B m F W:=by
 refine ⟨w,a,fun z l K h=>?_,fun z l x=>?_⟩
 · obtain ⟨g,y,ht⟩:=Xh z l; obtain ⟨f,z,p0⟩:=y.all Y s i k u ht K h; exact ⟨f,z.can Y s i k (p.poses B hp).ready e,p0⟩
 obtain ⟨g,Q,h⟩:=Xh z l; have hh':= norm_le_norm_sub_add ((sleeve F W z).x x) 1; rw [norm_one] at hh'; exact (hh'.trans (by linarith only [(Q.cost x).price, t] : ‖(sleeve F W z).x x-1‖ + (1:ℝ) ≤1+1)).trans (Real.add_one_le_exp _)
#print axioms LampPose.receipt
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
