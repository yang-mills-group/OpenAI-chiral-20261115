import GaugeFieldConstruction.Fellow
/-!
# The exact matrix periodization, landing power.
-/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side} {σ Y B:Bool → ℝ}{G:Ratio c f}{M:Male}{A:Site f}{o:Skye.Seat f}{T: Script Male}{p:BudgetPoint}{Q:Op (Single f)}{k m r:ℕ}
abbrev SM (n:Side):=Single n × Single n
abbrev sliceAB (G:Ratio c f)(A:Site f)(x:SM c)(y:DiamP):ℂ:= Event G A x.1 y.1*Event G A x.2 y.2
def remTag (G:Ratio c f)(A: Site f)(X: DiamP →ℂ)(x y:Single c): ℂ:= ∑' i, sliceAB G A (x,y) i * X i
lemma eventPair (G:Ratio c f)(A:Site f)(x: SM c)(y:DiamP):‖sliceAB G A x y‖ ≤1:=by rw [sliceAB,norm_mul]; exact mul_le_one₀ (event_origin ..).2 (norm_nonneg _) (event_origin ..).2
lemma remCash {X:DiamP→ℂ}(h: Summable fun i=>‖X i‖)(x y:Single c): Summable fun i=> sliceAB G A (x,y) i*X i:= Summable.of_norm_bounded h fun i=> by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (eventPair ..)
lemma E_exist (F H:Mill→ℂ)(u: Summable fun i=>‖F i‖)(v:Summable fun i=>‖H i‖)(i j:Single c) : let P:=ThetaS F H; Summable (fun x=>‖P x‖)∧ remTag G A P i j=star (bowling G A F i)*bowling G A H j:=by
 intro P; have hx: Summable fun t=>‖P t‖:=by
    have he: ∀ i:DiamP, ‖P i‖=‖F i.1‖ *‖H i.2‖:= by intro i; unfold P ThetaS; rw [norm_mul,norm_star]
    rw [funext he]; exact (summable_prod_of_nonneg (show 0 ≤ (fun i:DiamP=> ‖F i.1‖ * ‖H i.2‖) from fun i=> mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ⟨fun i=> v.mul_left (‖F i‖),by change Summable fun i=> _; simp_rw [tsum_mul_left]; exact u.mul_right _⟩ -- tune use SBprod
 refine ⟨hx,?_⟩; let f:= fun v=> sliceAB G A (i,j) v * P v; let g(v):=Event G A i v*F v; let z(v):= Event G A j v*H v; have he(x y):f (x,y) = star (g x)* z y:=by unfold f P ThetaS sliceAB g z; rw [star_mul,(event_origin ..).1]; ring
 change tsum f=star (tsum g)*tsum z; rw [(remCash hx i j).tsum_prod]; -- rw tune
 change (∑' x:Mill, ∑' y:Mill,f (x,y))=_; simp_rw [he,tsum_mul_left,tsum_mul_right, ← tsum_star]
abbrev oututi (G: Ratio c f)(e:Odd G.count.val)(T: Script Male)(M:Male)(U:Op (Single f)) :Op (Single c):= totF 4 G e T M U
variable (G o)
lemma θ_summon (u:Silks σ Y B m)(e:Odd G.count.val)(x y:Single c)(h:Use 4 G.count T): remTag G (AnchorN o) (CoverPull M G o Q) x y=oututi G e T M Q x y :=by
 let A:=AnchorN o; let L:=CoverPull M G o Q; let J:= sliceAB G A (x,y); let M'(i:SM f):= ThetaS (Θfull M G o false i.1) (Θfull M G o true i.2); let Z(i:SM f):=HyT o Q i.1 i.2
 have ht (b) (i:Single f): Summable (fun z=> ‖Θfull M G o b i z‖):=by have he:=(SB_paws (u.kw G e M b) (u.light _) (u.minor _) A (μPose o i) (portB i) 0).2.1; simp_rw [wl0,one_mul] at he; exact he
 let P(i:SM f):=E_exist (G:=G) (A:=A) _ _ (ht false i.1) (ht true i.2) x y
 let H(c:SM f) z:= Z c * (J z * M' c z); have he(z): J z*L z=∑ i:SM f,H i z:=by unfold L; rw [CoverPair,mul_sum]; exact sum_congr rfl fun i _=> mul_left_comm ..
 have hh(i:SM f):Summable (H i):=(remCash (G:=G) (A:=A) (P i).1 x y).mul_left (Z i)
 let W(b) := lensF G e T 4 b M; have hx(i:SM f): ∑' z,H i z= star (W false i.1 x) * Q i.1 i.2 * W true i.2 y:=by
    rw [show (∑' z,H i z)=(Z i)* remTag G A (M' i) x y from tsum_mul_left,(P i).2]; have hf (b) (x:Single c) y := point_tag (o:=o) (u.kw G e M b) e (u.light _) (u.minor _) h x y
    rw [hf,hf]; unfold Z HyT; let t:=Caller o i.1.1.1; let v:= Caller o i.2.1.1; change (t*v*Q i.1 i.2)*(star (t*W false i.1 x)*(v*W true i.2 y))=_; have ht:t^2=1:=by rw [pow_two]; exact fee_one _
    have hv:v^2=1:=by rw [pow_two]; exact fee_one _
    rw [star_mul,show star t=t from fee_real _]; ring_nf; rw [ht,hv]; ring
 change (∑' z,J z*L z)= _; simp_rw [he]; rw [Summable.tsum_finsetSum (fun i _=>hh i)]; simp_rw [hx]; unfold oututi totF; rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Finset.sum_mul]; rw [Fintype.sum_prod_type,sum_comm]; rfl
variable {G o}
-- tariff near center max option exactly
abbrev opEnd (o:Skye.Seat f)(x:SM f):=endL o (Haro.tray x.1 x.2)
lemma E_card (p:BudgetPoint)(o:Skye.Seat f)(h:ℝ)(x:SM f): tariff p o h (Haro.tray x.1 x.2)=(1+(opEnd o x:ℝ))^p.power*h^2:=by simp [tariff,Haro.tray,opEnd] -- tune h Bool
lemma EndC (o:Skye.Seat f)(x:SM f): opEnd o x=max (separation (node x.1.1.1) o) (separation (node x.2.1.1) o):=by unfold opEnd endL Haro.tray; simp only [Finset.sup_insert,Finset.sup_singleton]; rw [separation_comm _ o,separation_comm (node _) o] -- tune
lemma tax_prod (v:Odd G.count.val)(x: DiamP)(o:Skye.Seat f): let Z:SM c:=(ηtag G (AnchorN o) x.1, ηtag G (AnchorN o) x.2); (1+(opEnd (downT G o) Z:ℝ))^3 ≤ (24:ℝ)^3 *ThetaX x:=by
 intro Z; rw [EndC,Nat.cast_max, show ∀ x y:ℝ,1+max x y=max (1+x) (1+y) from fun i j=>by by_cases h:i≤ j <;> simp [max_def,h]] -- tune name
 have hp(i:Mill): (1+(separation (node (ηtag G (AnchorN o) i).1.1) (downT G o):ℝ))^3 ≤24^3*wagN 3 i:=by exact (pow_le_pow_left₀ (by positivity) (tag_spend v _ i) 3).trans_eq (mul_pow ..)
 rcases le_total ((1:ℝ)+ ↑(separation (node Z.1.1.1) (downT G o))) (1+↑(separation (node Z.2.1.1) (downT G o))) with t|t
 · rw [max_eq_right t]; refine (hp x.2).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (zero_le_one.trans (wagE ..))) (by positivity))
 rw [max_eq_left t]; refine (hp x.1).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (zero_le_one.trans (wagE ..))) (by positivity))
lemma tax_in (x:SM f)(o:Skye.Seat f): AnchorIn o x≤10*(1+(opEnd o x:ℝ)):=by
 rw [EndC,Nat.cast_max]; apply max_le; · apply (spotLength_B _ o x.1.1.1).trans; gcongr; exact le_max_left ..
 apply (spotLength_B _ o x.2.1.1).trans; gcongr; exact le_max_right ..
def WhX (r:ℕ)(u: Single f× Single f→ℝ)(o:Skye.Seat f):=∑ i:SM f,(1+ (opEnd o i:ℝ))^r*u i
lemma sell_w {u:Single f× Single f→ℝ}(s:∀ i,0≤ u i): warpTax o u ≤(10:ℝ)^3*WhX 3 u o:=by unfold warpTax WhX; rw [mul_sum]; refine sum_le_sum fun i _=> ?_ ; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ AnchorIn o i from zero_le_one.trans ((ladE _).trans (le_max_left ..))) (tax_in ..) _) (s i)).trans_eq; ring
end Boom
end YM.CF.TableF
end
