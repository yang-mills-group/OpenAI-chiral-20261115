import ForceSatin.Foliage
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
abbrev Sage:= SU.group.ColorIndex
abbrev roop (p:Face ℤ):Walk:= square p.2.val.1 p.2.val.2
-- paths on cover. Price using torsional shift.Mark pieces gauge clocks.
abbrev Arc (x y:Cover):={L:Walk//stop x L=y}
structure SpinSocket (o:Cover) where
 x : Cover
 spin : SpinIdx
 leg : Arc (nodeC x) o
structure CSocket (o:Cover) where
 p : Face ℤ
 leg : Arc o p.1
variable (t x y β e:ℝ){o:Cover}(N:Side) (U:Pane N) (g:Seat N→SU.E) (A F:SpinSocket o) (B B': CSocket o)
abbrev Np(N:Side):Cover → Seat N:= wrap (More N)
def arcT (N:Side)(U:Pane N) {x y:Cover} (u:Arc x y) :SU.E:= travel U (Np N x) u.val
abbrev courier (A:SpinSocket o)(U:Pane N):SU.E := arcT N U A.leg
abbrev riderT {a b:Cover}(L:Arc a b)(σ:ℕ):ℝ := ((visits a L.val).length*σ:ℕ) -- unneeded
lemma arc_cov {x y:Cover} (L:Arc x y): arcT N (gauge g U) L= g (Np N x)*arcT N U L *(g (Np N y))⁻¹:=by unfold arcT Np; rw [travel_gauge,← wrap_stop_cover,L.property] -- check args
abbrev cropT (B:CSocket o)(y:ℝ)(U:Pane N):SU.group.Color:= SU.group.adjoint (arcT N U B.leg) (y • SU.group.curvature (faceValue U (FaceN N B.p)))
lemma crop_cov : cropT N B y (gauge g U)= SU.group.adjoint (g (Np N o)) (cropT N B y U):= by rw [cropT, arc_cov, face_gauge, Gauge.curvature_conjugate]; change SU.group.adjoint _ (y • SU.group.adjoint (g (Np N B.p.1)) _) = _; rw [←map_smul,← Gauge.adjoint_mul, inv_mul_cancel_right, Gauge.adjoint_mul] -- check

-- actual kernels

abbrev speak (A:SpinSocket o)(b:Bool)(i:SU.Slot) : Bite:=⟨A.x,A.spin,i,b⟩
abbrev packet (A:SpinSocket o) (i:SU.Slot):FC (Single N):= vix N (speak A false i)
abbrev away (A:SpinSocket o) (i:SU.Slot):FC (Single N):= vix N (speak A true i)
-- local matter color implementation
lemma gaugeBasis (x:Cover)(i:SpinIdx)(b:SU.Slot): acts (tradew N g).val (basisC N x i b)= ∑ j:SU.Slot,(SU.matter (g (Np N (nodeC x)))).val j b • basisC N x i j:= by
  have he (x:Site N×SpinIdx): acts (tradew N g).val (basisKet (x,b))=∑ j:SU.Slot,(SU.matter (g (node x.1))).val j b • basisKet (x,j):=by
    apply PiLp.ext; rintro ⟨y,c⟩; rw [basis_act]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,mul_ite,mul_one,mul_zero]; rw [sum_eq_single c]; swap; · intro k _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
    swap; · simp
    change jump (Equiv.refl _) (fun p : Site N × SpinIdx=> (SU.matter (g (node p.1))).val) (y,c) (x,b)=_; rw [jump_apply]; simp only [Equiv.refl_apply,Prod.mk.injEq,and_true]; split_ifs with h; · rw [h]
    rfl
  unfold basisC; rw [map_smul]; unfold Lifted.index; rw [he,smul_sum]; refine sum_congr rfl fun j _=>?_ ; simp only [node_of]; exact smul_comm ..
abbrev θτ {N:Side}(g:Seat N→SU.E):= twist (quantU (tradew N g))
abbrev dG (g:Seat N→SU.E)(x:Cover):= (SU.matter (g (Np N x))).val
lemma throat (i:SU.Slot): θτ g (packet N A i)= ∑ j:SU.Slot,dG N g (nodeC A.x) j i • packet N A j:=by
 change twist _ (create (basisC _ _ _ _)) = ∑ j, dG N g _ j i • (create (basisC N _ _ _)); rw [twist_create,gaugeBasis,map_sum]; exact sum_congr rfl fun j _=> map_smul ..
lemma throat' (i:SU.Slot): θτ g (away N A i)= ∑ j:SU.Slot, star (dG N g (nodeC A.x) j i) • away N A j:=by
 change twist _ (Fock.remove (basisC _ _ _ _))=∑ j:SU.Slot,star (dG N g _ j i) • Fock.remove (basisC N _ _ _); rw [twist_remove,gaugeBasis]; unfold Fock.remove; rw [map_sum,star_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,star_smul]
-- bilinear kernel
abbrev PairBud (M0:Op SU.Slot):= (∑ i:SU.Slot,∑ j:SU.Slot, M0 i j • (packet N A i*away N F j))
lemma PairBud_turn (T:Op SU.Slot): θτ g (PairBud N A F T)= PairBud N A F (dG N g (nodeC A.x) * T * star (dG N g (nodeC F.x))):=by
 let x:= dG N g (nodeC A.x); let y:= dG N g (nodeC F.x); unfold PairBud; simp_rw [map_sum,θτ,twist_scalar,map_mul, show ∀ i:SU.Slot, twist _ (packet N A i)=_ from throat N g A, show ∀ i:SU.Slot, twist _ (away N F i) = _ from throat' N g F]; simp_rw [sum_mul,mul_sum,smul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
 -- after commute sums i j old & new. use simp^ elaboration
 let f(i j l m:SU.Slot):FC (Single N) := (T i j*(x l i* (star (y m j)))) • (packet N A l *away N F m)
 change ∑ i:SU.Slot,∑ j:SU.Slot,∑ l: SU.Slot, ∑ m:SU.Slot,f i j l m= ∑ i:SU.Slot,∑ j:SU.Slot,(x*T*star y) i j • (packet N A i * away N F j)
 have he(i j:SU.Slot): (x*T*star y) i j • (packet N A i*away N F j)= ∑ a:SU.Slot,∑ b:SU.Slot, f a b i j:=by
    simp_rw [Matrix.mul_apply, Matrix.star_apply,sum_mul,Finset.sum_smul]; rw [sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; unfold f; congr 1; ring
 simp_rw [he]; let Z(i:SU.Slot×SU.Slot)(j:SU.Slot×SU.Slot):=f i.1 i.2 j.1 j.2; have ht:(∑ i,∑ j,Z i j)=(∑ j,∑ i,Z i j):= Finset.sum_comm; simp_rw [Fintype.sum_prod_type (α₁:=SU.Slot) (α₂:=SU.Slot)] at ht; exact ht

abbrev rideC(N:Side)(U:Pane N)(A:SpinSocket o): Op SU.Slot:= (SU.matter (courier N A U)).val
abbrev bindN (U:Pane N) (A F:SpinSocket o)(T:Op SU.Slot) := rideC N U A*T*star (rideC N U F)
lemma ride_cov (U:Pane N): rideC N (gauge g U) A=dG N g (nodeC A.x)*rideC N U A*star (dG N g o):=by unfold rideC courier; rw [arc_cov,map_mul,map_mul,map_inv]; rfl
lemma bind_cov (U:Pane N)(X:Op SU.Slot): bindN N (gauge g U) A F (twist (SU.matter (g (Np N o))) X)=dG N g (nodeC A.x)*bindN N U A F X*star (dG N g (nodeC F.x)):=by
 unfold bindN; rw [ride_cov,ride_cov,twist_formula]; exact pay_form (dG N g (nodeC A.x)) (rideC N U A) (SU.matter (g (Np N o))).val (dG N g (nodeC F.x)) (rideC N U F) X (SU.matter (g (Np N o))).property
where
 pay_form (L A V R B X:Op SU.Slot)(p:V∈unitary (Op SU.Slot)) : (L*A*star V) * (V*X*star V) * star (R*B*star V)= L*(A*X*star B)*star R:=by
    have he:star V*V=1:=p.1;
    rw [star_mul,star_mul,star_star,show (L*A*star V)*(V*X*star V)*(V*(star B*star R))=L*A*(star V*V)*X*(star V*V)*star B*star R from (by simp only [mul_assoc])]; rw [he]; simp [mul_assoc]
#print axioms PairBud_turn
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
