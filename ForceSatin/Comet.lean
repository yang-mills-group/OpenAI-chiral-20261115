import ForceSatin.Garland
import YM.SU5.Hiro.Fresh
import YM.SU5.FiniteGaugeData.Tower.Baggage
import ForceSatin.Wallet
import ForceSatin.Ramp
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- tan. build covariant matter pair & color path. actual replica estimators, phase winds paid at both
open FoliageP Lifted Loaves Horizons Afterglow.Tower
namespace Moonlit
-- public builders for the tensor optics. NB use Work.PointB convention. Not the interactive Ward certificate.
namespace SwitchC
namespace Garland
open CF.SU
variable {o:Cover}{S:Finset Cover}(V:List MaskShape){m:ℕ}(N:Side)(A B:CSocket o)(F G:SpinSocket o) {U:Pane N} {x y t:ℝ}
abbrev Teeth:= SU.Slot×SU.Slot×SU.Slot×SU.Slot -- spin k,k', then a,b
noncomputable def spinBeam (Q:Op SU.Slot): Tab Teeth:= ⟨fun ⟨i,j,a,kWu⟩=>⟨[speak F false i,speak G true j],[],[⟨Rail.bot i a,nodeC F.x,F.leg.val⟩,⟨Rail.cnj (Rail.bot j kWu),nodeC G.x,G.leg.val⟩],V⟩,univ,fun ⟨_,_,a,kWu⟩=> Q a kWu⟩
-- Tab w J.Piece.Price.
lemma spin_cost (Q:Op SU.Slot) : (spinBeam V F G Q).terms ≤ Fintype.card Teeth*‖Q‖:=by
 apply (sum_le_sum (g:=fun _=> ‖Q‖) (fun ⟨i,j,a,kWu⟩ _=> norm_entry ..)).trans_eq; rw [sum_const,nsmul_eq_mul]; rfl -- card def
structure UsePair (F G:SpinSocket o) (S:Finset Cover)(x:ℝ) :Prop where
 birth : nodeC F.x ∈ S
 death : nodeC G.x ∈ S
 plus : F.spin ∈ plusHalf
 minus : G.spin ∉ plusHalf
 walk : TravelsC F.leg x S
 pace : TravelsC G.leg x S
lemma spin_price (p:UsePair F G S x)(h:∀ i∈V,UseMask i S x t)(Q:Op SU.Slot): SwitchC.ticket S t x 2 (spinBeam V F G Q):=by
 rintro ⟨i,j,a,b⟩ hq; show LoPrice _ t x S 2; unfold spinBeam; refine ⟨?_,rfl,le_refl _, Nat.zero_le _,le_refl _,?_,?_,fun i a=>⟨(h i a).inside,(h i a).min,(h i a).available⟩,?_⟩ -- helper
 · simp only [List.mem_cons, List.not_mem_nil,or_false] -- tune; choose manual.
   intro x q; rcases q with rfl|rfl; exacts [⟨p.birth, ⟨fun _=>p.plus,fun _=>rfl⟩⟩,⟨p.death, ⟨fun p=>by contradiction,fun v=> (p.minus v).elim⟩⟩]
 · simp
 · intro x g; rcases List.mem_cons.mp g with rfl|h; · exact ⟨p.walk.cope,p.walk.cost⟩
   rw [List.mem_singleton.mp h]; exact ⟨p.pace.cope,p.pace.cost⟩
 simp
private lemma pair_expand (Q:Op SU.Slot): PairBud N F G (bindN N U F G Q)= ∑ i:SU.Slot,∑ j:SU.Slot,∑ a:SU.Slot,∑ b:SU.Slot,Q a b • ((rideC N U F i a * star (rideC N U G j b)) • (packet N F i*away N G j)):=by
 unfold PairBud bindN; simp_rw [Matrix.mul_apply,Matrix.star_apply,sum_mul, Finset.sum_smul]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=>?_ ; rw [smul_smul,show Q a b*_=(rideC N U F i a*Q a b)*_ from ?_] -- defeq
 ring
lemma spin_view (Q:Op SU.Slot)(K:Calibration)(n:Side)(U:Fields (K.c n))(y:ℝ): (spinBeam V F G Q).cookP y K n U= if blink (K.c n) V U.1 then PairBud (K.c n) F G (bindN (K.c n) U.1 F G Q) else 0:=by
 let N:= K.c n; let A:= spinBeam V F G Q; unfold Tab.cookP; rw [drier_send]; unfold toMark claimant DriverP; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply]; let f(i: Teeth):= craft (Glass N (A.w i)) y U.1; change ∑ i:Teeth, A.tax i • f i= _; have hv(i): onGlow (Glass N (A.w i)) U.1 ↔ blink N V U.1:=by rcases i with ⟨i,j,a,b⟩; exact glance ..
 split
 next h=>
    rw [pair_expand]; rw [Fintype.sum_prod_type (α₁:=SU.Slot) (α₂:=SU.Slot×SU.Slot×SU.Slot)]; simp_rw [Fintype.sum_prod_type (α₁:=SU.Slot) (α₂:=SU.Slot×SU.Slot), Fintype.sum_prod_type (α₁:=SU.Slot) (α₂:=SU.Slot)]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> sum_congr rfl fun a _=> sum_congr rfl fun b _=>?_ ; -- nested
    unfold f craft; rw [if_pos ((hv (i,j,a,b)).2 h)]; -- check
    simp only [A,spinBeam,Horizons.Glass,carG,glare,CabN,chartP,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,_root_.id, SatinForce.cadence]; simp only [mul_one,Complex.ofReal_one,SatinForce.ride,Rail.cost]; rfl
 next h=> exact sum_eq_zero fun i _=> by unfold f craft; rw [if_neg ((hv i).mp.mt h), smul_zero]
-- zero-curvature piece kin with constant invariant table.Intertwiners species & gens. 
def SternQ (Q: Op SU.Slot): Prop:= ∀ i:SU.E, twist (SU.matter i) Q= Q
lemma spin_neutral (Q:Op SU.Slot)(h:SternQ Q)(K:Calibration)(y:ℝ): Tab.holds K y (spinBeam V F G Q):=by
 intro n g U; rw [spin_view,spin_view,show (simultaneous g U).1= gauge g U.1 from rfl]; by_cases p:blink (K.c n) V U.1; swap; · rw [if_neg p,if_neg ((blink_gauge (K.c n) _ g).mp.mt p),map_zero]
 rw [if_pos p,if_pos ((blink_gauge (K.c n) _ g).mpr p)]
 let v:= quantU (tradew (K.c n) g);
 change _ = θτ g _; nth_rw 1 [←h (g (Np (K.c n) o))]; rw [bind_cov,PairBud_turn]
#print axioms spin_view
#print axioms spin_neutral
end Garland
end SwitchC
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
