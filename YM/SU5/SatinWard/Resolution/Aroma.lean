import Anomaly.Basis.Mast
import YM.SU5.SatinWard.Resolution.Spangled
import YM.SU5.SatinWard.Resolution.Symbol
import SatinThinPetal

/-! Gauge Inertia (all off-shell Hessian columns), paid on the Frap mask (not full temple from Mast!). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill Buffered StressExchange Reed
open Vow.TreasuryFog
variable {N B M L:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h x₀ y c s:ℝ}{k q j l:ℕ}
local notation "Tc"=> mid N B
variable {K:Scree.Loom (mid N B)}{o:Site (mid N B)} (X:Moto.Skate) (HX: Moto.Verc X)
local notation "κo"=> Cube.node o

variable {D:ℕ}
local notation "X★"=> offsetMask D o
local notation "Kp"=> Φrap Tc o D
abbrev pointDG {N B:Side}(o:Site (mid N B))(X:Moto.Skate)(k:ℕ)(B':BudgetPoint):Pane (mid N B)→ℂ:=({V| pingS B'.threshold (offsetMask k o) V}).indicator (kerP (node o) B' X)
local notation "χi"=> pointDG o X D P
abbrev pointK {N B:Side}(o:Site (mid N B))(X:Moto.Skate)(k:ℕ)(P:BudgetPoint): Mark (mid N B):= fun x=> pointDG o X k P x.1 • 1
abbrev pointPhys (o:Site (mid N B))(X:Moto.Skate)(k:ℕ)(P:BudgetPoint):phy (mid N B):= fun x=> pointDG o X k P x.1 • 1
local notation "A_"=> pointK o X D P
variable (p:Taxi.DayT P.order c) (h0:0≤c) (hs: ‖X‖≤ a) (v:2 ≤ D)
local notation "Uo"=> plateZ κo P X
local notation "Z"=> trotΦ P a c
include p h0 hs v
lemma rakes (h:ℝ): PressB P Kp Uo h (trotΦ P a c):= champ P X Kp p h0 (Corona.halo_mono v le_rfl) (fun _ _=> (norm_le_pi_norm ..).trans ((norm_le_pi_norm ..).trans hs))
omit p h0 hs v
lemma wet_point : (wetPC P Kp Uo) = fun V:Orbit (mid N B)=> pointDG o X D P V.1 • (1:FC (Dwell (mid N B))):=by
 funext V; unfold wetPC pointDG numbE; by_cases t: V.1 ∈{v:Pane (mid N B)| pingS P.threshold X★ v}; · rw [Set.indicator_of_mem t,Set.indicator_of_mem t]; rfl
 rw [Set.indicator_of_notMem t, Set.indicator_of_notMem t, zero_smul]; rfl
local notation "Δu"=> wetPC P Kp Uo
include p h0 hs v HX
lemma gaugeEarn (hN:20<(More (mid N B)).val) (g:0 ≤ s)(k:D ≤ j*P.B) (u:3 ≤P.B)(w:1 ≤ h)(l':axleCap j^3<l): Drill P q j l o h s (pozV κo P j Δu) (X,0) (cashPoncho (chi_f P.order*(trotΦ P a c)) s j) (cashPoncho (trotΦ P a c) P.supportExponent j) 0:=by
 have ht:=rakes (o:=o) X p h0 hs v h
 have he: Neon.pillar o Uo P= (X,0):=by
    have hp : halo 2 {κo}⊆ X★:=Corona.halo_mono v le_rfl; refine Prod.ext (suit_l P X Kp (h:=h) (zero_le_one.trans w) p h0 hp (fun i j=> (norm_le_pi_norm ..).trans ((norm_le_pi_norm ..).trans hs)) hN HX).2 ?_
    change Hove.jetsL _ _=_; rw [show Haro.orbitPH (Uo 1)=0 from Moto.hol_l _, pub_eq,map_zero]
 rw [←he]; apply gain_core (Herb.growth w ht (Corona.halo_mono k le_rfl)) w u g (fromSkate (o:=o) X p h0 hs (v.trans k) h) _ l'; intro V t
 rw [wet_point X]; change Sault.rind (pointDG o X D P V.1 • (1:FC (Dwell Tc)))=_; unfold pointDG; rw [Set.indicator_of_mem (show V.1∈{v| pingS P.threshold X★ v} from grow_b (Corona.halo_mono k le_rfl) t)]; exact Sault.sky (Sault.skit _) (Flour.allP (fineShape _)) (Sault.tileL _)
set_option maxHeartbeats 1250000 in
lemma gaugeFrame (K:Scree.Loom (mid N B)): WindowTag (pointK o X D P) o (D+12) (trotΦ P a c)∧ Contact K (offsetMask (D+12) o) (pointK o X D P) (pointPhys o X D P):=by
 let M:= χi; let T:= node o; let Q:= (X★); have uv:= rakes (o:=o) X p h0 hs v 1; let s:=Z; have hh:0≤ s:= Roots.gradeE _ _ uv (by norm_num)
 have hx(V:Pane Tc): ‖M V‖≤ s :=by
    by_cases p':pingS P.threshold Q V; swap; · unfold M pointDG; rw [Set.indicator_of_notMem (show V ∉ {U'|pingS P.threshold Q U'} from p'),norm_zero]; exact hh
    unfold M pointDG; rw [Set.indicator_of_mem (show V∈{U'|pingS _ Q U'} from p')]; have he:= Taxi.eraF _ _ uv (by norm_num) V p'; have hv: Taxi.lifeH Uo V=kerP κo P X V:= hullB _; rw [←hv]; simpa [Function.comp_def,show increment V (0:tangD Tc)=V from by funext; simp [increment]] using Prism.sig0 he
 have hs:(fun x:Pane Tc=> kerP κo P X x)=Taxi.lifeH Uo:=funext fun x=> (hullB _).symm
 have hM:Envelope M:=by
    refine ⟨?_,s,hx⟩; apply Measurable.indicator _ ping_o.measurableSet
    exact (show Continuous (kerP (node o) P X) from by unfold kerP AnalyticBridge.VerifiedReset.counter AnalyticBridge.VerifiedReset.quad; fun_prop).measurable
 have hp: WindowTag A_ o (D+12) s:=by
    refine ⟨AtSupport.mono (AtSupport.fromEval (S:= inspected Q) (fun x=> M x • 1) (Girt.pole_w _ (fun x:ℂ=> x • 1) (continuous_id.smul continuous_const) hM) ?_ (fun i=> Reed.Fine.one.scale _)) (inspect_fits ..),?_,fun i=>?_ ,fun i j t=> congrArg (fun x=>M x • 1) t⟩
    · intro U V g; apply congrArg (fun x:ℂ=> x • (1:FC (Single (mid N B)))); unfold M pointDG; by_cases u:pingS P.threshold Q U; · rw [Set.indicator_of_mem (show U∈{x| pingS P.threshold Q x} from u),Set.indicator_of_mem (show V∈{x|pingS P.threshold Q x} from (Chaff.fenceW Q g _).mp u)]; rw [congrFun hs U,congrFun hs V]; exact congrArg Pastry.pane (uv.term _ _ (agrees_mono g (Finset.coe_subset.mpr subset_union_left)))
      rw [Set.indicator_of_notMem (show U∉{x| pingS P.threshold Q x} from u),Set.indicator_of_notMem (show V∉{x|pingS P.threshold Q x} from mt (Chaff.fenceW Q g _).mpr u)]
    · intro g x; change M (Lattice.gauge g x.1) • 1= twist _ (M x.1 • 1); rw [twist_scalar,map_one]
      unfold M pointDG; by_cases w:x.1∈{u|pingS P.threshold Q u}; swap; · rw [Set.indicator_of_notMem (show gauge g x.1∉{u|pingS P.threshold Q u} from mt (pingB x.1 g).mp w),Set.indicator_of_notMem w]
      rw [Set.indicator_of_mem w,Set.indicator_of_mem (show gauge g x.1∈{u|pingS P.threshold Q u} from (pingB x.1 g).mpr w)]
      have he(y:PlaqAxes→PlaqAxes→ℝ):AnalyticBridge.VerifiedReset.counter y (node o) (Lattice.gauge g x.1)=AnalyticBridge.VerifiedReset.counter y (node o) x.1 := (AnalyticBridge.VerifiedReset.counter_regular _ y P).symmetry g x.1
      apply congrArg (· • (1:FC (Single (mid N B)))); unfold kerP; rw [he,he]
    change ‖M i.1 • (1:FC (Single (mid N B)))‖ ≤ _; rw [norm_smul,norm_one,mul_one]; exact hx _
 exact ⟨hp,hp.ticket,fun _=> Fock.Sector.one.scale _,fun _=>rfl⟩
omit HX p h0 hs v
lemma pointVessel {g:ℕ}{wL:Odd L.val}{H:Pricing g L wL (Thread g)} (U:Grasp H B d)(R:GramM (mid N B))(T:Scree.Loom (mid N B))(j:ℕ): Vessel U R T (pozV (node o) P j (wetPC P (Φrap Tc o D) (plateZ (node o) P X))) (pointPhys o X D P):=by
 rw [wet_point X (o:=o) (P:=P) (D:=D)]
 refine ⟨fun x i=> ?_,fun x i p v=>?_⟩
 · rw [offset_P]; exact Leaf.ψX _ _ Leaf.ρX
 rw [offset_P]; unfold pointPhys; rw [act_smul,act_smul,act_one,act_one,map_smul]
end YM.CF.Swell.Porticus

namespace YM.CF.QuadClock
open Ione Moto

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


open Mew Waxy Roots Rive Oise
open Reef StressFlux AnalyticBridge.VerifiedReset
variable {n N B:Side}
def kCar (o:Site (More n))(D:Skate)(P:BudgetPoint)(Y:Pane n):ℂ:= ((1/2:ℝ)•(P.threshold^2:ℝ)⁻¹ : ℝ) • (∑ i:PlaqAxes,∑ j:PlaqAxes, inner ℝ (petals (G:=SU.group) Y o i) (petals Y o j) • D i j)
lemma ker_suit(o: Site (More n))(D:Skate)(P:BudgetPoint)(Y:Pane n): kerP o P D Y=kCar o D P Y:=by
 unfold kerP kCar counter AnalyticBridge.VerifiedReset.quad; apply Complex.ext <;> simp only [smul_eq_mul,Complex.add_re,Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,zero_add,mul_one,sub_zero,add_zero,Complex.smul_re,Complex.smul_im,Complex.re_sum,Complex.im_sum, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
 all_goals apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
lemma clover_moving (X:Moto.Skate)(s:Sweep n)(q:Site (More n))(p:BudgetPoint)(A:Pane n): kerP (boxA s q) p (costSkate s X) A=phaseB s (kerP q p X (flashA s A)):=by
 let Pζ:=pull s.s ((assembly n).embed s.b) A; let t:= (p.threshold^2:ℝ); let w:=boxA s q
 have h₀: kCar q X p (flashA s A)=kCar q X p Pζ:=by
    rw [revoke]; cases s.charge
    · rfl
    change kCar q X p (echo Pζ)=_; unfold kCar; simp_rw [echo_cost,show ∀ i j:SU.group.Color, inner ℝ (frolic i) (frolic j)=inner ℝ i j from fun i j=>frolic.inner_map_map i j] -- tune
 rw [ker_suit,ker_suit,h₀]; unfold kCar; rw [map_smul,map_sum (phaseB s)]; congr 1
 let E:=PlaqAxes.transform s.s; let f:=boxA s q
 have he(i): petals Pζ q i=spinScar s.s i • petals A f (E i):= by unfold Pζ; rw [petals_moves,cornerFlux]; unfold f; rw [sitA]
 rw [←Equiv.sum_comp E]; refine sum_congr rfl fun i _=>?_ ; rw [map_sum (phaseB s),←Equiv.sum_comp E]; refine sum_congr rfl fun j _=>?_ -- rw rewrites both?
 rw [he i,he j,real_inner_smul_left,real_inner_smul_right,map_smul, show costSkate _ _ (E i) (E j) = _ from cost_price s X i j,smul_smul]; change _ • (phaseB s) _= _ • (phaseB s) _; congr 1; ring
lemma point_scale (X:Moto.Skate)(r:ℝ)(o:Site (More n))(p:BudgetPoint)(V:Pane n): kerP o p (r • X) V=r • kerP o p X V:=by rw [ker_suit,ker_suit]; unfold kCar; rw [smul_comm r]; congr 1; simp_rw [Pi.smul_apply,Finset.smul_sum,smul_comm r]
open Swell Swell.Porticus Lampshade
open Buffered
variable {s:Sweep (mid N B)}{o y: Site (mid N B)}{D:ℕ}{p:BudgetPoint}{χ:SweepSign (mid N B)}{X:Moto.Skate}
local notation "TK"=>mid N B
private lemma moves_here (v:Earlier s o y): actY s (offsetMask D o)=offsetMask D y:=by
 ext i; unfold actY offsetMask; rw [mem_map_equiv,←show boxA s (node y)=_ from v]; simp [halo_spec,sitT]
lemma point_glance (v:Earlier s o y)(P:BudgetPoint)(U:Pane TK)(X:Moto.Skate): phaseB s (pointDG y X D P (flashA s U)) = pointDG o (costSkate s X) D P U:=by
 let A:=flashA s U; have h:pingS P.threshold (offsetMask D y) A ↔ pingS P.threshold (offsetMask D o) U:=(moves_here (D:=D) v) ▸ Salt.glowA _ _ _ _ -- tune
 unfold pointDG; by_cases p:pingS P.threshold (offsetMask D y) A; swap; · rw [Set.indicator_of_notMem (show A∉_ from p),Set.indicator_of_notMem (show U∉_ from mt h.mpr p),map_zero] -- implicit set infer
 rw [Set.indicator_of_mem (show A∈_ from p),Set.indicator_of_mem (show U∈_ from h.mp p)]; rw [←clover_moving,v]
lemma point_toll (o:Site TK)(x:ℝ)(X:Moto.Skate)(V:Pane TK) : pointDG o (x • X) D p V=x • pointDG o X D p V:=by
 unfold pointDG; by_cases t:V∈ {U| pingS p.threshold (offsetMask D o) U}; rw [Set.indicator_of_mem t,Set.indicator_of_mem t,point_scale]; rw [Set.indicator_of_notMem t,Set.indicator_of_notMem t,smul_zero]
lemma face_point (H:χ.Eigenspace (X,0))(p:BudgetPoint)(D:ℕ): SignBent χ BodyPull (fun i=>pointK i X D p) :=by
 intro s hs a b e; funext i; change Hive.teen s⁻¹ (pointDG b X D p (flashA s⁻¹⁻¹ i.1) • 1)= χ.sgn s • (pointDG a X D p i.1 • (1:FC _)); rw [inv_inv,
       show Hive.teen s⁻¹ (_ • _) = phaseB s (pointDG b X D p (flashA s i.1)) • Hive.teen s⁻¹ 1 from ?_,point_glance e p i.1 X, map_one]
 have he: costSkate s X=χ.sgn s • X:= congrArg Prod.fst (H s hs); rw [he,point_toll]; exact smul_assoc ..
 unfold phaseB; rw [castT]; exact Scree.cumin s⁻¹.charge _ (Sour.γS s⁻¹) _ _ -- tune
lemma point_K_scale (X:Moto.Skate) (r:ℝ)(o:Site TK)(P:BudgetPoint): pointK o (r • X) D P=r • pointK o X D P:=by funext i; unfold pointK; rw [point_toll]; exact smul_assoc ..
end YM.CF.QuadClock
