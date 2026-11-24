import GaugeFieldConstruction.Lazur
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
variable (M:Male)(o)
-- regroup for covariance
lemma streamS (u:Op (Single n))(h:ℝ)(v:Views) : streamF o u h v= ∑ i:Site n,∑ j:Site n,(( (PayS (κviews o i j) v * (h:ℂ)^2) * Caller o i * Caller o j) • matPH u i j):=by
 let p(i j:Site n):= (PayS (κviews o i j) v * (h:ℂ)^2) * Caller o i * Caller o j; let f(i j:Single n):= flare_one (portB i) (portB j) (PayS (κviews o i.1.1 j.1.1) v * hill_Z o u h i j);
 have he (f:Single n → Pal): (∑ i: Single n,f i)=∑ i:Site n,∑ j:Hove.Kt, f (Moto.hailV i j):=by
    rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl
 change (∑ z:Single n×Single n,f z.1 z.2)= _; rw [Fintype.sum_prod_type]; simp_rw [he]; apply sum_congr rfl; intro x _; rw [sum_comm]; apply sum_congr rfl; intro y _; change (∑ i:Hove.Kt, ∑ j:Hove.Kt,f (Moto.hailV x i) (Moto.hailV y j))=p x y • _
 nth_rw 1 [flare_draw (p x y • matPH u x y)] -- only rhs
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; apply congr_arg (flare_one i j); change PayS (κviews o x y) _ *((↑h)^2* _ * _ *u _ _)=p x y* u (Moto.hailV x i) (Moto.hailV y j); unfold p; dsimp only [Moto.hailV]; ring
lemma BinWin (V:Op (Single n))(p: MarkPH V)(g:SU.E)(x:Views): Commute (streamF o V h x) (KinX g):=by
 rw [streamS]; unfold Commute SemiconjBy; simp_rw [Matrix.sum_mul,Matrix.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; exact (Commute.smul_left (p g i j) _).eq
lemma kin_s (g:SU.E)(x:Views)(b:Bool): Commute (fellP M b x) (KinX g):=by
 cases b
 · apply Commute.sub_left (Commute.one_left _) ; unfold Commute SemiconjBy KinX Tap.boot; rw [op_kron_mul, op_kron_mul, mul_one,one_mul,one_mul, mul_one]
 unfold fellP Commute SemiconjBy KinX binor Tap.boot; simp only [ite_true]; rw [op_kron_mul, op_kron_mul,mul_one,one_mul,one_mul, mul_one]
lemma win_commute (V:Op (Single n))(p: MarkPH V)(g:SU.E)(x:Views): Commute (TabX o M h V x) (KinX g):= (stake_M g false).mul_left ((kin_s M g x false).mul_left ((BinWin o V p g x).mul_left ((kin_s M g x true).mul_left (stake_M g true))))
private def soakL : Pal→L[ℝ]Pal:= ((ContinuousLinearMap.mul ℝ Pal).flip (baseF true)).comp (ContinuousLinearMap.mul ℝ Pal (baseF false))
private def diff_K (g: SU.E): Pal→L[ℝ] Pal:= (ContinuousLinearMap.mul ℝ Pal).flip (KinX g) - ContinuousLinearMap.mul ℝ Pal (KinX g)
structure SheetQ(f:Pal):Prop where
 bin: baseF false*f* baseF true=f
 tax(g:SU.E): Commute f (KinX g)
def JetX(p:PalOne):Prop:= SheetQ p.1 ∧ (∀ i:Views, SheetQ (p.2.1 i)) ∧ ∀ i j:Views,SheetQ (p.2.2.val i j)
lemma fromJ {F A:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup A][NormedSpace ℝ A] {v: Ole A F} {f:A→F}(p:AptK f v)(g:F→L[ℝ]F)(h:∀ x, g (f x)=f x) :postF v g=v:= (p.geomF g|>.equal (Eventually.of_forall h)).unique p
lemma fromZ {F A:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup A][NormedSpace ℝ A] {v: Ole A F} {f:A→F}(p:AptK f v)(g:F→L[ℝ]F)(h:∀ x, g (f x)=0): postF v g= (show Ole A F from (0,0,0)):= ((p.geomF g).equal (show _ =ᶠ[𝓝 0] (fun _=> (0:F)) from Eventually.of_forall h)).unique (AptK.const 0)
lemma year_n (V:Op (Single n))(p:MarkPH V): JetX (winJ o M h V):=by
 let P:=winJ o M h V; let f:=TabX o M h V; have he: postF P soakL=P:=fromJ (tab M V) _ (fun i=> soak_X M V i); have ht(g): postF P (diff_K g) =(0,0,0):=fromZ (tab M V) _ (fun i=> sub_eq_zero.mpr (win_commute o M V p g i).eq) -- tune explicit order
 have hy(P₀:PalOne→ Pal)(x:Pal)(hp:∀ L:Pal→L[ℝ] Pal,P₀ (postF P L)= L x) (e:P₀ P=x)(v:P₀ (0,0,0)=0): SheetQ x:=by
    constructor
    · exact (hp soakL).symm.trans ((congrArg P₀ he).trans e)
    intro g; exact sub_eq_zero.mp ((hp (diff_K g)).symm.trans ((congrArg P₀ (ht g)).trans v))
 exact ⟨hy (fun i=>i.1) P.1 (fun L=>rfl) rfl rfl, fun i=>hy (fun p=>p.2.1 i) _ (fun L=>rfl) rfl rfl,fun i j=>hy (fun p=>p.2.2.val i j) _ (fun L=>rfl) rfl rfl⟩
lemma whiskey (p':PressB p X Q h c)(t:0≤ h) : JetX (winJ o M h (orbitPH (Q 1))):=year_n o M _ (worth_Φ X Q p')
abbrev mintPay(v:ℝ):ℝ:=4*CostOle (bladeL false)*(4*BasePrice false*(4*v*(4*BasePrice true*CostOle (bladeL true))))
lemma Ole_non {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](v:Ole E F):0 ≤ CostOle v:= norm_nonneg v
lemma costmint (V:Op (Single n)){c:ℝ}(p:CostOle (markJet o V h) ≤ c): CostOle (winJ o M h V)≤ mintPay c :=by
 let X:=wheelP M false; let Y:=wheelP M true; let v:=markJet o V h; let z:=palCart Y (bladeL true); let w:=palCart v z; let H:=palCart X w
 have hc:0≤ c:= (Ole_non v).trans p
 have he : CostOle z ≤ 4*BasePrice true*CostOle (bladeL true):=by apply (pal_cost ..).trans; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (wheel_C M true) (by norm_num)) (Ole_non _)
 have hz : CostOle w ≤ 4*c*(4*BasePrice true*CostOle (bladeL true)):=by apply (pal_cost ..).trans; exact mul_le_mul (mul_le_mul_of_nonneg_left p (by positivity)) he (Ole_non z) (by positivity)
 have hx : CostOle H ≤ 4*BasePrice false*(4*c*(4*BasePrice true*CostOle (bladeL true))):=by apply (pal_cost ..).trans; exact mul_le_mul (mul_le_mul_of_nonneg_left (wheel_C M false) (by norm_num)) hz (Ole_non w) (mul_nonneg (by positivity) (BP_u _))
 exact (pal_cost (bladeL false) H).trans (mul_le_mul_of_nonneg_left hx (mul_nonneg (by positivity) (Ole_non _)))
local notation "γ"=> X.val.1
lemma winκ (p':PressB p X Q h c)(t:0≤h) : CostOle (winJ γ M h (orbitPH (Q 1))) ≤ mintPay (caboose*16)*c := (costmint γ M _ (lofty p' t)).trans_eq (by unfold mintPay; ring)
end Lenten
end YM.CF.TableF
end
