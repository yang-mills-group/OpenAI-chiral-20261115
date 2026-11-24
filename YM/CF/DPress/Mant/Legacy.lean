import YM.CF.DPress.Mant.Repr
import YM.CF.DPress.Mant.Lapse
import YM.CF.DPress.Mant.Nar
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
 {x:ℝ}{C:Tew W}{β:ℝ}{t:Yds (mid P B)}{b:ℝ}{O:Shore0} {Q:Maud x C G S}(m:Penny Q O)
 (Y:Pony x C O){E G':Lobby Q O β}{D:ℝ}
open DPress.Analytic Salt Oise Quality Moral LinearT
-- output comparison.DF always $primeU.F only. fees sup tersely.
abbrev lev2 (P:BudgetPoint) := P.supportExponent+1+1
abbrev lev3 (P:BudgetPoint) := P.supportExponent+1+1+1
namespace Penny
lemma absoluteB(E:Lobby Q O β): PactF Q.X.p (lev3 Q.X.p) C.h (m.EP E) O.s∧XL Q.X.p C.h (lev3 Q.X.p) (m.BP E) O.K:=by
 obtain ⟨p,t,w⟩:=m.budget E; obtain ⟨ν,Q',v,y,A,xk,q,g,-⟩:=p.keep; exact ⟨⟨A,g,Sour.dutyK q⟩,(vouchers Q.X.p C.h _ C.uB _).2 ⟨m.pen E,fun i j k=> t.price i j (mem_filter.mp k).2.1 (mem_filter.mp k).2.2,w⟩⟩
lemma levZero (P:BudgetPoint): 0≤ lev2 P:= by unfold lev2; linarith [P.exponent_pos]
lemma levCash (P:BudgetPoint): 0≤ lev3 P:= by unfold lev3; linarith [P.exponent_pos]
variable (f:Lapse E G' D)
include f
section
lemma diffB : PactF Q.X.p (lev3 Q.X.p) C.h (m.EP G'-m.EP E) (εΔ O D*O.s) ∧ XL Q.X.p C.h (lev3 Q.X.p) (m.BP G'-m.BP E) (εΔ O D*O.K):=by
 rw [←f.rwCost, ←f.rwCost, ←congrArg m.EP f.start, ←congrArg m.EP f.last, ←congrArg m.BP f.start, ←congrArg m.BP f.last]; refine ⟨?_,?_⟩
 · exact gainLb f.curve m.EP Q.X.p (m.Edges f.reach) C.uB f.wide (fun z:Lobby Q O β=> (m.absoluteB z).1) (levCash Q.X.p)
 exact pressC1 f.curve m.BP Q.X.p (fun i j k=> m.Bb f.reach i j k) C.uB f.wide (fun z:Lobby Q O β=>(m.absoluteB z).2) (levCash Q.X.p)
lemma diffLunar : IncX primeU (m.Ty Y G'-m.Ty Y E) Q.X.p C.h (εΔ O D*C.Dstar O) ∧ ZL Q.X.p C.h (lev2 Q.X.p) (m.QL Y G'-m.QL Y E) (εΔ O D*C.CY x O):=by
 rw [←f.rwCost,←f.rwCost,←congrArg (m.Ty Y) f.start, ←congrArg (m.Ty Y) f.last, ←congrArg (m.QL Y) f.start, ←congrArg (m.QL Y) f.last]; exact ⟨approach Q.X.p C.uB (m.Ty Y ∘ f.curve) (fun i _=> m.yearX Y (f.curve i)) (fun i U' _=>m.χe Y f.reach i U') f.wide, Ξcare Q.X.p _ _ false C.uB (levZero _) (m.QL Y∘ f.curve) (fun z _=>(mantle _ _ _ C.uB _).2 (m.helps Y _).2) (fun i D _ Yb _=> m.Ξh Y f.reach i D Yb) f.wide⟩
lemma gPrice(i:Skye.Seat (mid N B)): tallB (fun j=>|(m.dρ G'-m.dρ E) j|) Q.X.p.B (lev2 Q.X.p) i≤ εΔ O D*(2*O.Pt):=by
 rw [←f.rwCost,←congrArg m.dρ f.start, ←congrArg m.dρ f.last]; exact representLb f.curve m.EP m.old ((1,m.Tp):Orbit (mid N B)) Q.X.p (fun i:Lobby Q O β=>(m.budget i).1) (m.Edges f.reach) (m.Eo f.reach) C.uB rfl f.wide i
lemma ΔEB : PactF Q.X.p (lev2 Q.X.p) C.h (m.Eb G'-m.Eb E) (6*(εΔ O D*O.Pt)):=by rw [←f.rwCost,←congrArg m.Eb f.start, ←congrArg m.Eb f.last]; exact presentLb f.curve m.EP m.old ((1,m.Tp):Orbit (mid N B)) Q.X.p (fun i:Lobby Q O β=>(m.budget i).1) (m.Edges f.reach) (m.Eo f.reach) C.uB rfl f.wide
end
-- R,K real at full Paying. Honest.
variable (v:HonestL E)(p:HonestL G')
include v p
lemma ΔTC : IncX primeU (m.TC Y G'-m.TC Y E) Q.X.p C.h (C.CB*C.φ x D):= m.priceC_sub Y E G' f.splitS rfl|>.symm ▸ m.worthC Y f.splitS (f.sect v p) f.pay
omit v p f
end Penny
namespace Tew
abbrev TΔ (C:Tew W)(x:ℝ)(O:Shore0)(D:ℝ):= εΔ O D*C.Dstar O+C.CB*C.φ x D
abbrev RΔ (C:Tew W)(x:ℝ)(O:Shore0)(D:ℝ) := C.CE * C.TΔ x O D + C.CR x * (6*(εΔ O D*O.Pt))
abbrev KΔ (C:Tew W)(x:ℝ)(O:Shore0)(D:ℝ):= C.CT*(εΔ O D*C.CY x O)+εΔ O D*(2*O.Pt)
end Tew
namespace Penny
-- full Sweeps on Δ Rb
variable (f:Lapse E G' D)(v:HonestL E)(p:HonestL G')
include v p f
lemma saltR : IncX Utrue (m.Rb Y G'-m.Rb Y E) Q.X.p C.h (C.RΔ x O D):=by
 have ht:IncX primeU (m.TL Y G'-m.TL Y E) Q.X.p C.h (C.TΔ x O D):=by rw [TL,TL,add_sub_add_comm]; exact (billP _ C.uB).add (m.diffLunar Y f).1 (m.ΔTC Y f v p)
 have hy: Sym_P (numbD (m.TL Y G'-m.TL Y E)):= SYp (m.lunar Y G' p).1 (m.lunar Y E v).1
 have hp:IncX Utrue _ _ _ (_* C.TΔ x O D +_*_) := addT Q.X.p (cup_R Q.X.p _ ht hy (zero_le_one.trans C.uB)) (receiptR C.uB m.Tp (Bsym (m.vFoam Y G' p).2.2 (m.vFoam Y E v).2.2) (TurfB (m.vFoam Y G' p).2.1 (m.vFoam Y E v).2.1) (m.ΔEB f)); rw [Rb,Rb,add_sub_add_comm,←LinearT.write,←stepUp]; rw [Q.stat.down.order,Q.stat.down.hK,Q.stat.fee] at hp; exact hp -- tune auto
omit v p
lemma saltK : ZL Q.X.p C.h (lev2 Q.X.p) (m.Kb Y G'-m.Kb Y E) (C.KΔ x O D):=by
 have hp:= LinearT.νForce C.uB (ksym (m.helps Y G').1 (m.helps Y E).1) (m.diffLunar Y f).2; have ht:= LinearT.νFuel C.uB (m.gPrice f); rw [Q.stat.down.order] at hp; rw [Kb,Kb,add_sub_add_comm,←LinearT.writes,←LinearT.fuel_p]; exact (νreg (n:=mid N B) _ _ _ false C.uB).add hp ht -- projection grade κ uses Δd via H not v p.
end Penny
end YM.CF.Py.Kay
