import YM.SU5.SatinWard.Resolution.Cypress
import YM.SU5.SatinWard.Resolution.Sailfin
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open LitCurrent Preparation.Tabletop Harmonic
local notation "Y"=> P.run
local notation "L★"=> P.par.R.L
local notation "B$"=> P.calibration
variable {v j f0 s w:ℕ}(p x:Cover)(wp:nodeC x=P.clockPlate s v p){a b A c φ:ℝ}{F: Family P.calibration}{S: Finset Cover}
local notation "v&"=>rentWidth P j v
local notation "U$"=> pavilion (P.clockPlate s v p) (rentWidth P j v)
variable {T:ℕ→Family P.calibration}{D:ℕ→ℕ}(q:Tendsto D atTop atTop)(e:BQueue S T F)
local notation "iv" i:max=> P.nomadic (D i)
local notation "kv" i:max=> P.engine (D i)
local notation "M" i:max=> side P.run (iv i) v
-- support widths & inclusion used up front.B proof volume budget & dapper layout.N.N rotation.As in Step previous wall.Mini.
variable (hb:Almanac P s w p) (hz: Closeted P j p s v w) (pc:S ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v))(H:InTest P.calibration true S false F) (i:Axis)
noncomputable abbrev poleDay (S₀: P.Card i v (P.reachLeaf s v w)): (P.Hil i).Op:= P.Box i v _ (P.reach_w _ hb.vivid) S₀
noncomputable abbrev cardC (i:Axis){S: Finset Cover} {F: Family P.calibration}(H:InTest P.calibration true S false F)(z:S⊆pavilion (P.clockPlate s v p) (rentWidth P j v)): P.Card i v (P.reachLeaf s v w):= P.snugLeaf i v (P.reachLeaf s v w) (H.mono z) (hz.extent i)
noncomputable abbrev daySpend : (P.Hil i).Op:= poleDay P p hb i (cardC P p hz i H pc)
noncomputable abbrev rentT (W:ℝ):= owedP A W
namespace Internal
lemma rentRegion {z:ℕ}(h:z≤rentWidth P j v) : pavilion (P.clockPlate s v p) z⊆ U$:=inclPav _ _ _ h
include wp in
lemma pavilionWidth {z:ℕ}(h:z≤rentWidth P j v) : pavilion (nodeC x) z⊆ U$:=by rw [wp]; exact inclPav _ _ _ h
include q hb pc e hz in
lemma chargeFor (h:s≤v)(fee0:0<c) (ft:∀ᶠ n in atTop, ∃ Z:Site (side P.run (P.nomadic (D n)) s)→ Mark (side P.run (P.nomadic (D n)) v), SeatsPriced A P.run s (P.nomadic (D n)) (P.engine (D n)) v Z c∧ TwistP P.run (P.nomadic (D n)) s v Z∧exhibit P.run P.large v (P.nomadic (D n)) (T n)= Z (P.rootAt s (P.nomadic (D n)) p))(k:P.NightCop): ‖daySpend P p hb hz pc e.landing i‖ ≤ owedP A c:=by
 let P0:=cardC P p hz i e.landing pc; let e':=cueMono e pc
 apply Presidential.boardPrice Y P.large P.law v P.projection i (P.reachLeaf s v w) T (U$) D q _ (mul_pos (Real.exp_pos _) fee0) (P.reach_w _ hb.vivid) 0 k (P.fitsOrigin hz.extent) rfl _ _ P0 e'; unfold Settle
 filter_upwards [ft,q.eventually (marches P v)] with j F e y s' S' x
 obtain ⟨G,T,u,v'⟩:=F; let U:= P.rootAt s (iv j) p; have v0:((RootBook P.run (iv j) (kv j) s)).p.B=P.thresholdF s:= congrArg BudgetPoint.B (Papal.prices_plot P.run _ (iv j) (kv j) (h.trans e.2.le)).1
 refine stemLayer P.run A T u P.large w 0 U h fee0 (?_) hb.budget _ v' y s' S' ?_ ; · rw [v0]; exact ⟨_,hb.stand,(node_of ..).symm⟩
 simpa only [reachLeaf,Pi.zero_apply,mul_zero] using! x
/- Namespace name chosen to avoid Lean.LibrarySuggestions metadata maxRecDepth panic (these propositions elaborate directly and are still exported normally) -/
-- combine under same Stamp funding.Thick.Compression later paid at actual column
variable {F' G:Family P.calibration}{U Q:Finset Cover}(p₁:U⊆ pavilion (P.clockPlate s v p) (rentWidth P j v))(p₂:Q⊆ pavilion (P.clockPlate s v p) (rentWidth P j v))(t₁:InTest P.calibration true U false F')(t₂: InTest P.calibration true Q false G)
lemma dayScale (x:ℝ)(p': F=x • G) : daySpend (S:=S) (F:=F) P p hb hz pc H i = x • daySpend (S:=Q) (F:=G) P p hb hz p₂ t₂ i:= box_paidCoin P i x _ _ p' _
lemma daySum (p': F= F'+G): daySpend (S:=S) (F:=F) P p hb hz pc H i = daySpend (S:=U) (F:=F') P p hb hz p₁ t₁ i+ daySpend (S:=Q) (F:=G) P p hb hz p₂ t₂ i:=by let h:P.Box i v (P.reachLeaf s v w) _ (cardC P p hz i H pc)= (1:ℂ) • daySpend (S:=U) (F:=F') P p hb hz p₁ t₁ i+daySpend (S:=Q) (F:=G) P p hb hz p₂ t₂ i:= P.box_linear i v _ _ _ _ _ 1 (by rw [one_smul]; exact p'); rwa [one_smul] at h
include H in
lemma tentScale (x:ℝ) : InTest P.calibration true S false (x • F):=by rw [← Complex.coe_smul]; exact H.smul _
include H in
lemma tentSub {V: Family P.calibration} (u:InTest P.calibration true S false V): InTest P.calibration true S false (F-V):=by rw [sub_eq_add_neg, ←neg_one_smul ℂ]; exact H.add (u.smul _)
lemma daySub (p':F= F'-G): daySpend (S:=S) (F:=F) P p hb hz pc H i = daySpend (S:=U) (F:=F') P p hb hz p₁ t₁ i-daySpend (S:=Q) (F:=G) P p hb hz p₂ t₂ i:=by let V':= daySum P p hb hz p₁ t₁ i pc p₂ H t₂ (show F'=F+G from eq_add_of_sub_eq p'.symm); exact eq_sub_of_add_eq V'.symm -- sign? eq_add_of_sub_eq : a-b=c→ a=b+c; check
-- input `Foot approval`: norm of Box <=. support intersection built union; Card etc
noncomputable abbrev letRoom (Z:P.Card i v (P.reachLeaf s v w))(pF:P.voxTest i v Z.val∈enclave P.calibration) (x:P.Spectrum0 i): (P.ColorHil i x).Op:= P.colorSpace i x (P.door i v _ (P.reach_w _ hb.vivid) Z pF)
private lemma rebate {A:Type*}[CStarAlgebra A]{Z:Hilbert} (F:A →⋆ₐ[ℂ] Z.Op)(a b:A)(z:ℂ): ‖F a-z • F b‖ ≤ ‖a-z • b‖ := by rw [←map_smul,←map_sub]; exact NonUnitalStarAlgHom.norm_apply_le F _
lemma expenses (Z Z':P.Card i v (P.reachLeaf s v w))(pF:P.voxTest i v Z.val∈enclave P.calibration)(pG:P.voxTest i v Z'.val∈enclave P.calibration)(z:ℂ)(x:P.Spectrum0 i) : ‖letRoom P p hb i Z pF x-z • letRoom P p hb i Z' pG x‖≤ ‖poleDay P p hb i Z-z • poleDay P p hb i Z'‖:=by exact rebate (Z:=P.ColorHil i x) (P.colorSpace i x) (P.door i v _ (P.reach_w v hb.vivid) Z pF) (P.door i v _ (P.reach_w _ hb.vivid) Z' pG) _ -- coherence quotient
lemma let_thread(Z:P.Card i v (P.reachLeaf s v w))(pF:P.voxTest i v Z.val∈enclave P.calibration) {F':P.Test}(v':P.voxTest i v Z.val= F') (x:P.Spectrum0 i): P.ThreadOp i x v (P.reachLeaf s v w) F' (letRoom P p hb i Z pF x):=⟨Z,P.reach_w _ hb.vivid,pF,v'.symm,rfl⟩
end Internal
#print axioms Internal.chargeFor
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
