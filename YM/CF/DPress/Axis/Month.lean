import YM.CF.DPress.Axis.Revenue
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
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
namespace Campus.Urban
variable (D:Urban P_ Q O)(E:Lobby Q O β)(T:HonestL E)
local notation "Yq"=> pickQ m D
variable (G':Lobby Q O β)(T':HonestL G')(f:Lapse E G' b)
local notation "ε"=> εΔ O b
include D T T' f
lemma πpair : D.docks.Pair C.h ε (m.BP E) (m.BP G') (cipherK C.M₀):=by
 have he:=m.diffB f; exact ⟨f.εpos.le,f.εone,(winter m D E T).lane,(winter m D G' T').lane,(fortune (n:=mid N B) _ _ _ C.uB).toReceipt.relax he.1 (mul_le_mul_of_nonneg_left D.easeE f.εpos.le),(νreg (n:=mid N B) _ _ _ true C.uB).toReceipt.relax he.2 (mul_le_mul_of_nonneg_left D.easeK f.εpos.le),fun p=> (f.εpos.ne' p).elim⟩
local notation "H"=> D.TutorP
local notation "MX"=> RadP Q.X.p P_.Wk C.h (C.master O)
local notation "M'"=> mid N B
local notation "uF"=> winter m D E T
local notation "uP"=> winter m D G' T'
local notation "c'"=> seatq Q
local notation "tV"=> G_t m D E
local notation "vT"=> G_t m D G'
omit D T T' in
lemma μhold : C.master O* εΔ O b=4*C.pay b:=by
 have hp:= f.δpos; let K:=C.ζCA*(R.L.val:ℝ)⁻¹; change K*O.δ*(4*b/O.δ)=4*(K*b); rw [mul_assoc,show O.δ*(4*b/O.δ)=4*b from (by rw [mul_comm, div_mul_cancel₀ _ hp.ne'])]; ring -- 
lemma slender : IncX Utrue ((m.Rb D.star G')-(m.Rb D.star E)) Q.X.p C.h (C.master O* ε /4):=by
 have hd:= D.payable; refine Tutor.loosen (m.saltR D.star f T T') ((D.pawn.reserve_p f.money.le).trans ?_); have hp: C.shade ≤ C.ζCA:= le_add_of_nonneg_right zero_le_one; have hL: (0:ℝ)<R.L.val:=by positivity
 refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hL.le)) f.money.le).trans_eq ?_; rw [μhold E G' f]; unfold Tew.pay; ring -- ring tune
lemma Φδ : hΔ ((Yq) G' T') ((Yq) E T) ≤ 2*ε:= Resident.σοl D.A D.hope (G_t m D E) m.Tp K.j Q.X.J.M (c') H D.pure D.payable D.rideP (canonical (Q:=Q)).le D.costR P_.tk Θlive uF _ _ uP (G_t m D G') (slender m D E T G' T' f) (πpair m D E T G' T' f) (settle m D E T) (settle m D G' T') -- tune args
lemma νops : ‖ζy m D G' T'-ζy m D E T‖ ≤ 2* ε *(P_.rM O):= by rw [←canonical (Q:=Q)]; exact (div_le_iff₀ (D.TutorP.bright D.payable)).mp (Φδ m D E T G' T' f)
lemma Bf' : PactF Q.X.p (ρL Q.X.p) C.h (EmptyD (B' m D G' T')- EmptyD (B' m D E T)) (3*ε*D.docks.Γ) ∧ XL Q.X.p C.h (ρL Q.X.p) (B' m D G' T' - B' m D E T) ((D.docks.κ⁻¹*D.docks.Γ)*(3*ε)) :=by
 have he:=πpair m D E T G' T' f; let S:= (canonical (P_:=P_) (O:=O) (Q:=Q)).le; let g:=(H).bright D.payable; let V:= (Yq) E T; let V':=(Yq) G' T'; have hx:= curvePower D.A D.hope he V V' g (D.TutorP.generous D.A D.hope g S D.rideP); have hK: Flight.debt V' V ε≤ 3*ε:= by have ht:hΔ V' V≤2*ε:= Φδ m D E T G' T' f; let g:=hΔ V' V; apply (add_le_add (le_refl ε) ht).trans_eq; ring
 have hz:0≤D.docks.κ⁻¹:=inv_nonneg.mpr (zero_le_one.trans D.docks.unitK); have hq:= D.docks.Γp; exact ⟨(fortune (n:=M') _ _ _ C.uB).toReceipt.relax hx.zeroE ((mul_le_mul_of_nonneg_left hK hq.le).trans_eq (mul_comm ..)),(νreg (n:=M') _ _ _ true C.uB).toReceipt.relax hx.fullE (mul_le_mul_of_nonneg_left hK (mul_nonneg hz hq.le))⟩
lemma R_out' : IncX Utrue (Rout m D G' T' - Rout m D E T) Q.X.p C.h (P_.tax b):=by
 refine Tutor.loosen (Resident.σωl D.A D.hope (G_t m D E) m.Tp K.j Q.X.J.M (c') H D.pure D.payable D.rideP (canonical (Q:=Q)).le D.costR P_.tk Θlive uF ((Yq) E T) ((Yq) G' T') uP (G_t m D G') (slender m D E T G' T' f) (πpair m D E T G' T' f) (settle m D E T) (settle m D G' T')) ?_
 let v:= (4* C.pay b); let K:= C.master O; have hv:v=K* ε:= (μhold E G' f).symm -- tune
 have hz:0<C.h:=zero_lt_one.trans_le C.uB; have he: MX=(8*(P_.Ct)*K)/C.h^2:=by unfold RadP; rw [P_.tall_x Q]
 have hp:v>0:= hv ▸ mul_pos D.payable f.εpos
 change K* ε+ _ ≤ _; rw [he,show Sp Q.X.p=P_.ρB from by rw [← P_.mentor Q]; exact P_.spotP _]; rw [show P_.tax b=v*(2+16*P_.Ct*P_.ρB) from (by unfold tax v CA Tew.pay; ring)]; apply le_of_eq_of_le (_: _=v*(1+16*P_.Ct*P_.ρB)) (mul_le_mul_of_nonneg_left (by linarith) hp.le); rw [hv]; field_simp; ring
omit T' f
lemma abs_B : PactF Q.X.p (ρL Q.X.p) C.h (EmptyD (B' m D E T)) D.docks.Γ ∧ XL Q.X.p C.h (ρL Q.X.p) (B' m D E T) (D.docks.κ⁻¹ * D.docks.Γ):=by
 let U:= m.BP E; obtain ⟨I,p',g⟩:=(winter m D E T).tickets C.uB; exact growth p' (D.TutorP.allowance D.A D.hope (D.TutorP.bright D.payable).le (canonical (Q:=Q)).le D.rideP) C.uB g (Heath.Kernel.realPitch D.A D.hope _ ((Yq) E T)) -- tune
omit T
end Campus.Urban
end YM.CF.Py.Kay
