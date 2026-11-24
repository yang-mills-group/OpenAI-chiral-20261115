import YM.CF.DPress.Dens.Studio
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
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Cap Graph Window Mint Period
namespace Quant
local notation "wm" =>cashU W.C
local notation "n_" =>cell M B R.L i
local notation "hx" =>hat R.L x i
local notation "Tc"=>taxY (More (cell M B R.L i))
abbrev Tc0 (j:ℕ):= Graph.taxY (More (cell M B R.L j)) (2*hat R.L x j) (Δ.a j).threshold K.top.paths V.W.bar
abbrev Cm (v:ℝ):= flagBill (cell M B R.L i) v v (cashU W.C)
abbrev meterY (v:ℝ):= Real.exp (Tc0 (Δ:=Δ) (M:=M) i+Cm (W:=W) (M:=M) (i:=i) v)
variable {b v:ℝ}(L0: LogH (cell M B R.L i)) (g: matchedX (hat R.L x i) v)(p:AccountY (Δ.a i) C.h L0.fuel b)
local notation "Q"=> (render D i L0 v)
lemma ℓp (b:ℝ): (D.render i L0 b).path.Bounds K.top.clip K.top.width K.top.paths V.W.bar:= V.L.mood _ -- synt Supp no
include D in
lemma βpos : matchedX hx v → 0 ≤ v:= fun g=> le_trans (div_nonneg (F.now i).le (by norm_num)) g.1
include g p
lemma flight : Graph.Ledger C.h b b (levelQ W.C) (cashU W.C) (render D i L0 v):= frostQ (⟨p.E,rfl,p.K⟩:LotR (render D i L0 v) C.h b b) (zero_le_one.trans C.uB) ((W.arm ..).sound i)
variable (z:Orbit (cell M B R.L i))
omit p in
lemma liftv : taxY (More (cell M B R.L i)) v (Δ.a i).threshold K.top.paths V.W.bar ≤ Tc0 (Δ:=Δ) (M:=M) i:=by unfold Tc0 taxY; refine add_le_add_left (mul_le_mul_of_nonneg_right g.2 ?_) _; have ht:= wing_budget V; have hp:0 < (Δ.a i).threshold:= (Δ.a i).threshold_pos; positivity
include D in
abbrev baseR(J:Robes M' V W)(F:RoomF J Λ M Δ) (i:ℕ):Roof (cell M B R.L i) J.k d J.n (F.Y i):= let t:=(F.rocket i).paid; {t with paid:=fun j=> (t.paid j).shrink J.hr.le}
lemma true_ : ‖recX U (render D i L0 v) (F.Y i) z‖ ≤ meterY (Δ:=Δ) (M:=M) (i:=i) b:= by
 let G' := baseR J F i; refine (Window.extensive_price (render D i L0 v) (F.Y i) G' U (J.gran.trans (F.rocket _).size) (flight D L0 g p) (ℓp D L0 v) (level_p _).le C.uB (cash_v W.C) (βpos D g) z).trans ?_
 unfold meterY; rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (liftv (Δ:=Δ) g)) (Real.exp_pos _).le -- check inclusion orientation
section
local notation "Vn"=> (cell M B R.L i)
omit g
abbrev νr : Op (Single (cell M B R.L i)):= spar K.j (D.venue i).J.M (F.Y i z)
local notation "νT"=> νr (i:=i) D z
include D
omit p
lemma ιv :IsStarProjection (νr (i:=i) D z):=(U.broadness _ (J.gran.trans (F.rocket i).size) _).projection _ ((baseR J F i).paid z)
include g p
abbrev ώr:ℝ:=Real.exp (pittance (cell M B R.L i) 2 (cashU W.C) + doorF (cell M B R.L i) 2 (cashU W.C)) -- implicit n? crisp
lemma gaugeU : ‖ Complex.exp (- Pec.pigment (D.venue i).J.I (F.Y i z))‖ * ‖exp (dg (actF K.j (D.venue i) (F.Y i) z))‖ ≤ ώr (W:=W) (i:=i) (M:=M):=by
 let e:=levelQ W.C; let ht:= (level_p W.C).le; have he:= Graph.aurP (F.Y i z) (D.venue i).J.I (flight D L0 g p).field.2 (railT _ _ ht) (by positivity); have hX:= Window.thermalCap (render D i L0 v) (F.Y i) (flight D L0 g p) z ht K.j (ιv D z) (by norm_num : 0≤(2:ℝ)) (railT _ _ ht)
 unfold ώr; rw [Real.exp_add]; exact mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_monotone ((norm_neg _).trans_le he))) ((Graph.bootC _).trans (Real.exp_monotone (show ‖dg (actF K.j (D.venue i) (F.Y i) z)‖≤_ from hX))) (norm_nonneg _) (Real.exp_pos _).le -- $L0$ not included signature p. Typeclass
lemma recB (K0:LogH (cell M B R.L i)): ‖Graph.recX U (render D i K0 v) (F.Y i) z - Graph.recX U (render D i L0 v) (F.Y i) z‖ ≤ Real.exp (Tc0 (Δ:=Δ) (M:=M) i)* ώr (W:=W) (i:=i) (M:=M)* ‖Studio.BoardV (Δ.a i) z K0.fuel νT-Studio.BoardV (Δ.a i) z L0.fuel νT‖:=by
 let X:GramM Vn:=render D i L0 v; let X':GramM Vn:=render D i K0 v; let R0:= Real.exp (Tc0 (Δ:=Δ) (M:=M) i); let Z:=ώr (W:=W) (i:=i) (M:=M); let r0:= Graph.past X z.1; have hp:0 ≤ r0:= (Real.exp_pos _).le
 let J_:= F.Y i; let t:= changeM (m:=Vale.mesh M R.L i) U (J_ z) (X.J.M); have gx: -X.path.inChannels X.funds X.p X.beta z.1 ≤ _:= neg_le.mp (Window.energy_low X.p X.path X.funds (ℓp D L0 v) (βpos D g) z.1)
 have he: r0≤ R0:=Real.exp_monotone (gx.trans (liftv (Δ:=Δ) g))
 let u:= mile K.j X J_ z; let vΓ:=mile K.j X' J_ z; have hv : recX U X' J_ z-recX U X J_ z = r0 • acts (vΓ-u) t:=by rw [Graph.porch,Graph.porch,act_sub,smul_sub]; rfl
 let Qd:=fun f:Yds Vn=> Studio.BoardV (Δ.a i) z f (νr (i:=i) D z); let gP:=Complex.exp (-Pec.pigment (D.venue i).J.I (F.Y i z)); let hP:= exp (dg (actF K.j (D.venue i) J_ z)); let S:= Qd K0.fuel - Qd L0.fuel; have hH: vΓ-u=gP • (S*hP):=by unfold vΓ u Graph.mile; rw [Studio.actuator _ z _ X rfl rfl, Studio.actuator _ z _ X' rfl rfl]; change gP • (Qd K0.fuel*hP)-gP • (Qd L0.fuel*hP)=gP • (_*hP); rw [←smul_sub, ←sub_mul]
 have hh: ‖vΓ-u‖≤ Z*‖S‖:=by
    rw [hH,norm_smul]; refine (mul_le_mul_of_nonneg_left (norm_mul_le ..) (norm_nonneg gP)).trans ((le_trans (le_of_eq (by ring : ‖gP‖* (‖S‖ * ‖hP‖)=‖gP‖ * ‖hP‖ * ‖S‖)) ?_) ); exact mul_le_mul_of_nonneg_right (gaugeU D L0 g p z) (norm_nonneg _)
 have hhh:‖t‖=1:= (sea_g (J.gran.trans (F.rocket i).size) (F.Y i z) ((baseR J F i).paid z) _).2
 change ‖Graph.recX U X' J_ z - Graph.recX U X J_ z‖ ≤ R0*Z* ‖S‖; rw [hv,norm_smul,Real.norm_of_nonneg hp,mul_assoc]; apply mul_le_mul he _ (norm_nonneg _) (hp.trans he); exact (Graph.spentS _ _ _).trans (le_trans (le_of_eq (by rw [hhh,mul_one])) hh) -- tune he binder unknown
end
end Quant
end Crib
end FitD
end YM.CF.Py.Kay
