import GaugeFieldConstruction.ContinuumLegacyReceipt
import GaugeFieldConstruction.StencilFerro
import YM.SU5.Thin.Touch
import YM.SU5.Assay.Base
/-!
# Note on the old pair used for comparison: actual voucher cannot rescue the claim.
 -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace


namespace ContinuumConstruction
-- Data telescope. Naming concordance through the flagship API (QFT: E to Story,
-- L & G to continuity, calendars to labels and paths).
variable
  {nLeaf : ℕ}
  {process : Spine}
  {scale : process.Register}
  {production : YardμN process CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {vacuum : process.Spectrum0 3}
  {costAnalysis : process.Ellis 3 vacuum}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress vacuum (le_refl _) layers response}
  {screens : process.Poll 3}
namespace SecondOrient
open PadThin Sifter Discipline
open OS.Semigroup Scoop
private lemma merchSt (X:Hilbert)(F:ℕ→ X.Op) (A:X.Op) (v:Tendsto F atTop (𝓝 A))(R: ℕ→Scoop): Tendsto (fun i:ℕ=> (R i).recipe fun k=> F (i+k)) atTop (𝓝 A):=by
 rw [Metric.tendsto_nhds]; intro ε e
 obtain ⟨t,h⟩:= eventually_atTop.mp (Metric.tendsto_nhds.mp v (ε/2) (half_pos e))
 filter_upwards [eventually_ge_atTop t] with i p
 have x:(R i).recipe (fun _=>A)=A:=by unfold Scoop.recipe; rw [← Finset.sum_smul,← Complex.ofReal_sum,(R i).total,Complex.ofReal_one,one_smul]
 have hp: ((R i).recipe (fun k=> F (i+k))) - A=(R i).recipe (fun k=> F (i+k)-A):=by unfold Scoop.recipe; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, show ∑ k∈(R i).take,((↑((R i).weight k)):ℂ) • A=A from x]
 rw [dist_eq_norm,hp]; exact ((R i).cap fun k _=> (show _ from le_of_lt (by rw [←dist_eq_norm]; exact h _ (by omega)))).trans_lt (half_lt_self e)
open YM.OS.Semigroup
set_option maxHeartbeats 900000
private lemma closeSandSt (B:Hilbert)(Y:YM.OS.Semigroup B 3)(r:ℕ→ℕ)(F:ℕ→B.Op)(Hx:ℂ)(U: WageStream B r F)
    (L:∀ t:ℝ,0<t→ Tendsto (fun i:ℕ=> Y.sand (F i) t t) atTop (𝓝 (Hx • Y.wax (t+t)))): U.issue=Hx • 1:=by
 let T:=Y.wax; let W:=Hx • (1:B.Op); have h(t:ℝ)(y:0<t): (Y).sand U.issue t t = (Y).sand W t t:=by
    have hz:(Y).sand W t t=Hx • T (t+t):=by unfold W OS.Semigroup.sand; rw [mul_smul_comm, smul_mul_assoc,mul_one,(Y).wax_sq y.le y.le]
    ext1 k; let Hr(t':ℕ):B:= U.cost t' |>.recipe (fun i=> ((Y).sand (F (t'+i)) t t) k)
    let W'(i):= (U.cost i).recipe (fun j=> F (i+j)); let Q(i):= (U.cost i).recipe (fun j=> (Y).sand (F (i+j)) t t)
    have hp(i):Q i k=(T) t (W' i ((T) t k)):=DFunLike.congr_fun (around (B) (Y) _ (U.cost i) t.toNNReal t.toNNReal) k
    have he:(Y).sand U.issue t t k= (T) t (U.issue ((T) t k)):=rfl
    refine tendsto_nhds_unique_of_eventuallyEq (l:=atTop) (f:=fun i=> (T) t (W' i ((T) t k))) (g:=fun i=> Q i k) ?_ ?_ (Eventually.of_forall fun i=>(hp i).symm)
    · exact (T t).continuous.continuousAt.tendsto.comp (U.arrival ((T) t k)).1
    rw[hz]; exact ((ContinuousLinearMap.apply ℂ B.space k).continuous.continuousAt.tendsto.comp (merchSt (B) _ (Hx • T (t+t)) (L t y) U.cost))
 have p(A:(B).Op) : BSOT (fun t=> (Y).sand A t t) (𝓝[>]0) A:=by
    have hp:Tendsto (fun t:ℝ=>t) (𝓝[>]0) (𝓝 (0:ℝ)):= tendsto_id.mono_left nhdsWithin_le_nhds -- tune
    have hz := (Y).sand_limit (BSOT.stay A) hp hp; simpa [OS.Semigroup.sand, (Y).wax_zero] using hz
 ext1 v; exact tendsto_nhds_unique_of_eventuallyEq ((p U.issue).showAt v) ((p W).showAt v) (by filter_upwards [self_mem_nhdsWithin] with t hp; exact DFunLike.congr_fun (h t hp) v)
private lemma justMap_st {A B:Type} [Ring A][Ring B][Algebra ℂ A][Algebra ℂ B][Star A][Star B] (G:A →⋆ₐ[ℂ] B) (U T L:A)(y:ℂ): G (T*U*T-y • L)= G T * G U * G T-y • G L:=by rw [map_sub,map_mul,map_mul,map_smul G]
private lemma capturesCapSt (P:Spine)(x:P.Spectrum0 3)(A:P.Apron)(t l:ℝ)(y:ℂ) :
 ‖(P.physicalEnergy 3 x).sand (A.engine P 3 x) t t-y • (P.physicalEnergy 3 x).wax l‖≤
   ‖P.grantGapNX 3 A.s (A.u 3) A.F (t+A.realWidth P 3) (t+A.realWidth P 3) - y • P.hearthNX 3 l‖:=by
 let G:= P.colorSpace 3 x; let L(z:ℝ):= P.risesColor 3 z.toNNReal
 let U:=P.doorBox 3 A.s (A.u 3+A.u 3) (P.shifts 3 (A.u 3) A.F)
 let W:= L t * U * L t -y • L l
 have he:G W=(P.physicalEnergy 3 x).sand (A.engine P 3 x) t t-y • (P.physicalEnergy 3 x).wax l:=by
    have hp:A.engine P 3 x = G U:= P.engine_seen ..
    rw [hp]; change G (L t*U*L t-y • L l)= G (L t) * G U * G (L t)-y• G (L l)
    exact justMap_st (B:=(P.ColorHil 3 x).Op) G U (L t) (L l) y
 have hp:W.val=P.grantGapNX 3 A.s (A.u 3) A.F (t+A.realWidth P 3) (t+A.realWidth P 3) - y • P.hearthNX 3 l:=by
    change (L t).val * U.val*(L t).val -_ = _; rw [grantGapNX,show P.tock A.s (A.u 3)= A.realWidth P 3 from rfl,add_sub_cancel_right,←lamp_shadow P _ (A.color P 3) (A.admit 3)]; rfl
 rw [←he,←hp]; exact NonUnitalStarAlgHom.norm_apply_le G W
private lemma BuildingSt (B:Hilbert)(Y:YM.OS.Semigroup B 3)(L:ℕ→ℝ)(t:ℝ)(Hx:ℂ)(S:ℕ→B.Op)(e:0<t)(hL:Tendsto L atTop (𝓝 t))(H:∀ ε,0<ε→∀ᶠ s in atTop, ‖S s - Hx • Y.wax (L s+L s)‖ ≤ ε): Tendsto S atTop (𝓝 (Hx • Y.wax (t+t))):=by
 let F'(s:ℕ):= Hx • Y.wax (L s+L s)
 have he : Tendsto F' atTop (𝓝 (Hx • Y.wax (t+t))):= ((Y).wax_cont (add_pos e e) |>.tendsto.comp (hL.add hL)).const_smul _
 rw [Metric.tendsto_nhds]; intro ε hε
 filter_upwards [H _ (half_pos hε),Metric.tendsto_nhds.mp he (ε/2) (half_pos hε)] with s v q
 have hv:dist (S s) (F' s) ≤ ε/2:=by rw [dist_eq_norm]; exact v
 exact lt_of_le_of_lt (dist_triangle (S s) (F' s) _) (lt_of_lt_of_le (add_lt_add_of_le_of_lt hv q) (add_halves _).le)
variable {i:ℕ} {M:process.Menagerie}{b:ℕ→ℕ}{z:ℝ}{F G: SampleDose}{D:∀ Z:Lead.Clan, process.VoucherOp vacuum Z (collars i) b}
local notation "P" => process
local notation "Ψ" => process.otherSpectrum 3 3 x -- local unscoped x₁
local notation "X₀" => process.Spectrum0 3
variable (h:LegacyQuantities (scale:=scale) (c:=c) (collars:=collars) i M b z F G D)(x:process.Spectrum0 3) (Z:Lead.Clan) (t:ℝ)
local notation "ψ" => process.otherSpectrum 3 3 x
local notation "B" => process.ColorHil 3 (process.otherSpectrum 3 3 x)
local notation "Y" => process.physicalEnergy 3 (process.otherSpectrum 3 3 x)
local notation "T" => (Y).wax
local notation "Hx" => (process.electro M Z)
include h
-- at any positive t.E gap may be larger before. owner still elect.Cil.
private lemma vestalSt (e:0<t): Tendsto (fun s:ℕ=> (Y).sand ((process.thinString Z s (collars i)).engine process 3 (process.otherSpectrum 3 3 x)) t t) atTop (𝓝 (Hx • T (t+t))):=by
 let A(s:ℕ):= process.thinString Z s (collars i); let S(s:ℕ):=(Y).sand ((A s).engine process 3 ψ) t t
 let w(s):= (A s).realWidth process 3; let L(s):= t+w s
 have hp(s): t≤ L s:= (lt_add_of_pos_right _ ((A s).real_width_pos process 3)).le
 have hL:Tendsto L atTop (𝓝 t):=by
    have h' : Tendsto w atTop (𝓝 0):=probeWidth_static process (collars i) 3
    simpa only [add_zero] using (tendsto_const_nhds (x:=t)).add h'
 refine BuildingSt (B) Y L t (Hx) S e hL ?_
 intro ε e'
 filter_upwards [h.mean_read Z t ε e e'] with s v
 exact (capturesCapSt process ψ (A s) t (L s+L s) _).trans ((v 3).2 _ (hp s) _ (hp s))
local notation "hw" => Hx • (1:(B).Op)
variable (r:ℕ→ℕ) (U : process.VoucherOp x Z (collars i) r)
local notation "R" => U.issue
include x
lemma oldIssue_hereSt : U.issue= process.electro M Z • (1:(process.ColorHil 3 (process.otherSpectrum 3 3 x)).Op):=by
 let F(s:ℕ):= (process.thinString Z (r s) (collars i)).engine process 3 (process.otherSpectrum 3 3 x); let W:=hw
 exact closeSandSt (B) (Y) r F (Hx) U (fun t y=>(vestalSt h x Z t y).comp U.safe.tendsto_atTop)
#print axioms oldIssue_hereSt
end SecondOrient
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
