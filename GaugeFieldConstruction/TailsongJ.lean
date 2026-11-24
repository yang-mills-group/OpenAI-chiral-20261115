import GaugeFieldConstruction.PortionRentJ
import GaugeFieldConstruction.CunardJ
import GaugeFieldConstruction.SakhaJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
namespace RosterJ
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.

local notation "ΤΓ"=> P.run
#check ProbeθJ
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
local notation "Ξu"=> Fin (θ u)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
-- supplier cut at Gate Periods, all s. extend by zero outside.VRoot.
local notation "gk" i:max=> P.gateCut i
local notation "gi" i:max=> P.gatePeriod i
abbrev ΩPunchJ (P:Spine)(i:ℕ)(s:ℕ):Prop:= s < P.run.uv (P.gateCut i)∧ (P.run.voyage (P.gatePeriod i)).kick≤P.gateCut i
lemma PunchLongJ (P:Spine)(s:ℕ): ∀ᶠ i:ℕ in atTop, ΩPunchJ P i s:=(P.history.finance (s+1)).mono fun _ h=> ⟨h.enters,h.depth⟩
-- LampStall.Calendar with registrations. ALL x.
abbrev CalendarJ (Ω':RosterJ P θ G f0)(B0:SωJ θ)(M:JωL θ) := ∀ i:ℕ,∀ a:ΩPunchJ P i f0, BoonsθJ Ω' B0 M (P.gatePeriod i) (P.gateCut i) a.1.le a.2
variable (A:CalendarJ p B0 M)
local notation "θK"=>Fin (θ u)
local notation "Bτ" i:max a:max=> A i a
local notation "τ_"=> SωJ θ
def Stencil1Q (s:ℕ) (H:f0 ≤ s) (m:ℕ):ThreadJ (E:=Fin (θ u)):= if h:ΩPunchJ P m (s+1) then
    let t:ΩPunchJ P m f0:=⟨(by have ht:=h.1; omega),h.2⟩
    let K:= StampCK p _ _ B0 M (A m t) x R u
    (K.C s,K.a s) else 0
-- H and B⁻¹ both, unitar proof at limit after. hide regs heights floor.
def Stencil2Q (s:ℕ)(H:f0 ≤ s)(m:ℕ): ThreadJ (E:=Fin (θ u)):= if h:ΩPunchJ P m s then let t:ΩPunchJ P m f0:=⟨lt_of_le_of_lt H h.1,h.2⟩; Sunγ p _ _ B0 M (A m t) x R u L s s H else 0
def Stencil3Q (s:ℕ)(H:f0 ≤ s)(m:ℕ):ThreadJ (E:=Fin (θ u)) := if h:ΩPunchJ P m s then
    let B':= BtJ p _ _ B0 M (A m ⟨lt_of_le_of_lt H h.1,h.2⟩) x R u L H h.1.le s; (B'.symm.toLinearMap,0) else 0
abbrev ThreadShopJ (E:Type)[LinearOrder E][Fintype E](a:Slow)(F:ℕ→ThreadJ (E:=E))(G:ThreadJ (E:=E)):Prop:=∀ x:FrameK E, Tendsto (fun i=> (F (a.subSeq i)).1 x) atTop (𝓝 (G.1 x)) ∧ Tendsto (fun i=> (F (a.subSeq i)).2 x) atTop (𝓝 (G.2 x))
local notation "Ρ1"=> Stencil1Q p B0 M x R u A
local notation "Ρ2"=> Stencil2Q p B0 M x R u L A
local notation "Ρ3"=> Stencil3Q p B0 M x R u L A
section abs
variable {E:Type}[LinearOrder E][Fintype E]{Ξ:Type}[NormedAddCommGroup Ξ][NormedSpace ℂ Ξ]
lemma ΦBuild_J (F:ℕ→FrameK E→ₗ[ℂ] Ξ)(A:E→Ξ)(t:∀ j:E, Tendsto (fun i=> F i (κEye j)) atTop (𝓝 (A j)))(x:FrameK E):Tendsto (fun i=> F i x) atTop (𝓝 (ArchBuildJ A x)):=by
 have he(i): F i x= W_s (fun j=>F i (κEye j)) x:=by unfold W_s; nth_rw 1[Καone x]; rw [map_sum]; simp_rw[map_smul]
 simp_rw [he]; exact tendsto_finset_sum _ (fun i _=> tendsto_const_nhds.smul (t i)) -- tune
lemma ΦBuild_moveJ (F:ℕ→FrameK E→ₗ[ℂ] Ξ)(A:FrameK E→ₗ[ℂ]Ξ)(t:∀ x,Tendsto (fun i=>F i x) atTop (𝓝 (A x)))(x:ℕ→FrameK E)(y:FrameK E)(p:Tendsto x atTop (𝓝 y)):Tendsto (fun i=>F i (x i)) atTop (𝓝 (A y)):=by
 have he(A:FrameK E→ₗ[ℂ]Ξ)(x):A x=W_s (fun j=>A (κEye j)) x:=by unfold W_s; nth_rw 1[Καone x]; rw[map_sum]; simp_rw[map_smul]
 rw [he A]; simp_rw[he (F _) (x _)]; exact tendsto_finset_sum _ (fun i _=> (tendsto_pi_nhds.mp p i).smul (t _))
lemma χChooseJ (F:ℕ→ThreadJ (E:=E))(a b:ℝ) (B:Slow) (p:∀ᶠ i in atTop, Clipζ a b (F i)) : ∃ X:Slow,∃ V:ThreadJ (E:=E), ThreadShopJ E (B.more X) F V :=by
 let A:=F∘ B.subSeq
 let S:_root_.Set (E→E→ℂ):= Set.univ.pi fun k=> Set.univ.pi fun i=> Metric.closedBall 0 (b*LoomK (κEye k))
 let T:_root_.Set (E→ℂ):= Set.univ.pi fun k=> Metric.closedBall 0 (b*a*LoomK (κEye k))
 let g(m:ℕ): (E→ E→ℂ) × (E→ℂ):= (fun i=>(A m).1 (κEye i), fun i=> (A m).2 (κEye i))
 have h : IsCompact (S×ˢT):=(isCompact_univ_pi (fun i=> isCompact_univ_pi (fun k=> isCompact_closedBall (0:ℂ) _))).prod (isCompact_univ_pi fun i:E=>isCompact_closedBall (0:ℂ) _)
 have he:∀ᶠ i:ℕ in atTop,g i∈ S×ˢT:=(B.step.tendsto_atTop.eventually p).mono (fun i ⟨p,q⟩ => ⟨fun j _ k _=> by rw[mem_closedBall,dist_zero_right]; exact (single_k _ _).trans (p (κEye j)),fun j _=> by rw[mem_closedBall,dist_zero_right]; exact q (κEye j)⟩)
 obtain ⟨c,q,c',v,e⟩:= h.tendsto_subseq' he.frequently -- tune
 let Z: ThreadJ (E:=E):=(ArchBuildJ c.1,ArchBuildJ c.2)
 let A₀:Slow:=⟨_,v⟩
 rw [nhds_prod_eq] at e
 have hh:= tendsto_pi_nhds.mp e.snd
 have hx:= tendsto_pi_nhds.mp e.fst
 exact ⟨A₀,Z,fun i=> ⟨ΦBuild_J _ _ hx i, ΦBuild_J _ _ hh i⟩⟩ -- tune binder composition
lemma ThreadShopJ.delay {X Y:Slow}(p:X.Delayed Y){F:ℕ→ThreadJ (E:=E)}{G:ThreadJ (E:=E)}(q:ThreadShopJ E X F G):ThreadShopJ E Y F G:= fun x=> ⟨ Filter.tendsto_def.mpr (fun z u=> p.iff_tail (fun i=> (F i).1 x∈z) ((q x).1 u)), Filter.tendsto_def.mpr (fun z u=>p.iff_tail (fun i=> (F i).2 x∈z) ((q x).2 u))⟩
end abs
#check Stencil3Q
lemma FundsΧ (s:ℕ)(H:f0 ≤ s): let Y:= Stencil1Q p B0 M x R u A s H; let Z:= Stencil2Q p B0 M x R u L A s H; let T:= Stencil3Q p B0 M x R u L A s H; let W:= RankQJ P.par s
 ∃ (h K :ℝ), (∀ᶠ i:ℕ in atTop,Clipζ K h (Y i))∧(∀ᶠ i:ℕ in atTop,Clipζ W (1/2) (Z i))∧∀ᶠ i:ℕ in atTop, Clipζ (0:ℝ) 2 (T i):=by
 intro Y Z T W; let K:= chipJ P.par*W; let R':= stepRateJ P.par u.val; have hh:= p.price f0 le_rfl u 0; have he:0<R':=zero_lt_one.trans_le hh.bound; refine ⟨R',K/R', ?_, ?_,?_⟩
 · filter_upwards[PunchLongJ P (s+1)] with i z
   unfold Y Stencil1Q; rw [dif_pos z]; have ht:ΩPunchJ P i f0:= ⟨(by have ht:=z.1; omega),z.2⟩; let A':=StampCK p _ _ B0 M (A i ht) x R u
   unfold Clipζ; rw [show R'*(K/R')=K from (by field_simp)]; obtain ⟨p,q,v,h⟩:= (StripeH p _ _ B0 M (A i ht) x R u).turn s H (by have hx:=z.1; omega); exact ⟨p,h⟩
 · filter_upwards [PunchLongJ P s] with i z; unfold Z Stencil2Q; rw [dif_pos z]; exact ΓClip p _ _ B0 M (A i ⟨lt_of_le_of_lt H z.1,z.2⟩) x R u L H z.1.le s
 filter_upwards [PunchLongJ P s] with i z; unfold T Stencil3Q; rw[dif_pos z]; exact ⟨fun i'=>νBtJ p _ _ B0 M (A i ⟨lt_of_le_of_lt H z.1,z.2⟩) x R u L H z.1.le s i',fun i=> by change ‖(0:ℂ)‖≤_; simp⟩
#print axioms FundsΧ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
