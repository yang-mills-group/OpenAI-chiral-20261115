import GaugeFieldConstruction.Dali
/-!
# Joint on/off power from earned Cloth, aligned Thin Leaf.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
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
variable {f c:Side}{G:Ratio c f}{M:Male} {o:Skye.Seat f}{b:Bool}{U:Op (Single f)}{Q:Op (Single f)}{σ: Bool→ℝ}{B Y: Bool→ℝ}{h:ℝ}{m k r:ℕ}
-- compressed tariff on input literal matrix rather than PH Mom. exact pricing at ports wXX
abbrev μPose(o:Skye.Seat f)(x:Single f):= spot o x.1.1
abbrev AnchorIn(o:Skye.Seat f)(x:Single f × Single f):ℝ:= max (Ladder (μPose o x.1)) (Ladder (μPose o x.2))
abbrev warpTax (o:Skye.Seat f) (f':Single f×Single f→ℝ):=∑ i:Single f×Single f, f' i * AnchorIn o i ^3
abbrev Θfull (M:Male)(G:Ratio c f)(o:Skye.Seat f)(b:Bool)(x:Single f):= Sister M G b (AnchorN o) (μPose o x) (portB x)
def ΘRest (M:Male)(G:Ratio c f)(o:Skye.Seat f)(b:Bool)(x:Single f)(i:ℕ):= Stove M G (AnchorN o) b i (μPose o x) (portB x)
abbrev DiamP:= Mill ×Mill
abbrev RollPair (M:Male)(G:Ratio c f)(o:Skye.Seat f)(x:Single f×Single f) (m:ℕ): DiamP→ℂ:= θLook (ΘRest M G o false x.1) (ΘRest M G o true x.2) m
abbrev PeekE (M:Male)(G:Ratio c f)(o:Skye.Seat f)(x:Single f×Single f):= ThetaS (Θfull M G o false x.1) (Θfull M G o true x.2)
abbrev GapJr (M:Male)(G:Ratio c f)(o:Skye.Seat f)(x:Single f×Single f)(m:ℕ):= PeekE M G o x-RollPair M G o x m
def CoverPull (M:Male)(G:Ratio c f)(o:Skye.Seat f)(Q:Op (Single f))(v:DiamP):ℂ:= PJ_act Q o (fun i=> Θfull M G o false i v.1) (fun i=> Θfull M G o true i v.2)
lemma CoverPair (v:DiamP): CoverPull M G o Q v= ∑ i:Single f ×Single f, HyT o Q i.1 i.2 * PeekE M G o i v:=by unfold CoverPull PJ_act; apply sum_congr rfl; intro i _; unfold PeekE ThetaS; ring
-- vanish full sub from PN
lemma unstep (v:SentK o Q)(t:quote_B M Q o h r)(w:100<f.val)(g:h≠0)(p:r≤3)(i:DiamP):∑ x:Single f ×Single f, HyT o Q x.1 x.2 * RollPair M G o x r i=0:=by
 let U:=Single f×Single f
 let K(x:U)(u l:ℕ):= HyT o Q x.1 x.2 * ThetaS (ΘRest M G o false x.1 u) (ΘRest M G o true x.2 l) i; unfold RollPair θLook; simp_rw [Finset.sum_apply,mul_sum]; change ∑ x:U,∑ j∈range r,∑ l∈range (r-j),K x j l=0
 rw [sum_comm]; refine sum_eq_zero fun j hv=> ?_; rw [sum_comm]; apply sum_eq_zero; intro l hk; have he:=mem_range.mp hv; have hz:=mem_range.mp hk
 let QL(x:Single f):= ΘRest M G o false x j i.1; let QR(x:Single f):= ΘRest M G o true x l i.2; have ht: PJ_act Q o QL QR=0:=twoStroke v t w g (RightCH j (by omega) false G i.1) (RightCH l (by omega) true G i.2) (by omega) p
 apply Eq.trans (_ : _= PJ_act Q o QL QR) ht; refine sum_congr rfl fun x _=> ?_; unfold K ThetaS QL QR; ring
lemma pull_twig (v:SentK o Q)(t:quote_B M Q o h r)(w:100<f.val)(g:h≠0)(p:r≤3): CoverPull M G o Q= fun i:DiamP=> ∑ x:Single f ×Single f, HyT o Q x.1 x.2 * GapJr M G o x r i:=by funext i; simp_rw [GapJr,Pi.sub_apply,mul_sub,sum_sub_distrib,unstep v t w g p,sub_zero,← CoverPair]
local notation "ρ"=> αN G.count
structure Silks (σ U B:Bool→ ℝ)(L:ℕ):Prop where
 real(i:Bool):1≤B i
 light(b:Bool):0<U b
 minor(b:Bool):0<σ b
 kw : ∀ {c f:Side}(G:Ratio c f)(p:Odd G.count.val)(M:Male)(b:Bool), Honed G.count M b (U b) (σ b)
 fast: ∀ {c f:Side}(G:Ratio c f)(p:Odd G.count.val)(b:Bool)(n k:ℕ), n ≤L → k ≤ L → EraM b n G (U b) (σ b) k≤ B b*wool G.count []
lemma buy_Silk (L:ℕ):∃ σ U B :Bool→ℝ,Silks σ U B L:=by
 choose B U σ f l e A using fun i:Bool=> legWay L i; refine ⟨σ,U,B,⟨f,l,e,fun G h M b=> (A b G h).1 _,fun G h b j k s t=> (A b G h).2 j k s t⟩⟩
variable (p: Silks σ Y B m)(s:3 ≤ m)
def γE_0 (G:Ratio c f)(B:Bool→ℝ):= B false*wool G.count []
def γE_1 (G:Ratio c f)(B:Bool→ℝ):= B true*wool G.count []
abbrev wageX (G:Ratio c f)(B:Bool→ℝ)(r:ℕ):= 1800*γE_0 G B * γE_1 G B*αN G.count ^ r
lemma OvKos (r:ℕ): wageX G B r=1800* B false *B true*(HarmP.SpanL G.count)^2 * ρ^(3+r):=by
 unfold wageX γE_0 γE_1 wool; let v:ℝ:=G.count.val; have hx:0<v:=Nat.cast_pos.mpr G.count.property; unfold αN; simp only [List.length_nil,Nat.zero_add]; rw [pow_add]; change _ * v⁻¹ ^ r= _; have he: Real.sqrt G.count.val^2=v:= Real.sq_sqrt hx.le; unfold v at *; field_simp; -- audit syntax
 ring_nf; rw [Real.sq_sqrt hx.le]; ring
include p s
lemma TornNear (e:Odd G.count.val)(x:Single f ×Single f)(o:Skye.Seat f)(M:Male)(r:ℕ)(k:r≤3): chime ThetaX (GapJr M G o x r) (wageX G B r* AnchorIn o x ^3):=by
 have he (b) (x:Single f)(t:ℝ)(l:Ladder (μPose o x)≤t): Upk (ΘRest M G o b x) (Θfull M G o b x) (B b*wool G.count []) t ρ:=RankingB (G:=G) (p.kw _ e M b) (p.light b) (p.minor b) e _ _ _ t l (fun i hi j hj=>p.fast G e b i j (hi.trans s) (hj.trans s))
 let A:=AnchorIn o x; have ha:1≤A:= (ladE _).trans (le_max_left ..)
 let L:=γE_0 G B; let H:=γE_1 G B
 have hx:0 < L:= (EP_V false 0 G _ _ 0 (p.light _) (p.minor _)).trans_le (p.fast G e false 0 0 (by omega) (by omega)); have hz:0 < H:= (EP_V true 0 G _ _ 0 (p.light _) (p.minor _)).trans_le (p.fast G e true 0 0 (by omega) (by omega))
 have hv:= he false x.1 A (le_max_left ..); have hf := he true x.2 A (le_max_right ..)
 by_cases hl :ρ*A ≤1
 · exact κ_near L A ρ H hv hf hx hz (α_pos _) hl ha r k
 exact κ_outer L A ρ H hv hf hx hz (α_pos _) (not_le.mp hl).le (αsmall _) ha r k
omit p s
def Slit (M:Male)(G:Ratio c f)(o:Skye.Seat f)(t: Single f ×Single f→ ℝ)(r:ℕ): DiamP→ℝ:= ∑ x:Single f ×Single f,t x • fun i:DiamP=> ‖GapJr M G o x r i‖ -- tune syntax
include p s
lemma SlitPay (r:ℕ)(v:r≤3)(M:Male)(o:Skye.Seat f)(g:Odd G.count.val)(t:Single f× Single f→ℝ) (ht:∀x,0≤t x): (∀ i,0≤ Slit M G o t r i)∧ SumBudget (fun i=> ThetaX i* Slit M G o t r i) (wageX G B r * warpTax o t):=by
 let K(i):=GapJr M G o i r; let J(i):= t i • fun v:DiamP=>‖K i v‖; let Y(i):= Slit M G o t r i
 refine ⟨fun i=>?_ ,?_⟩; · unfold Slit; rw [Finset.sum_apply]; exact sum_nonneg (fun a _=>mul_nonneg (ht a) (norm_nonneg _))
 let H(i):= t i*(wageX G B r*AnchorIn o i^3); have hx:SumBudget (fun i=>ThetaX i*Y i) (∑ i,H i):=by
    apply SBqual (SBfin (f:=fun i j=> t i*(ThetaX j*‖K i j‖)) univ H (fun i _=> SBscale (TornNear p s g i o M r v) (ht i))) (fun i=> ?_) (fun i=>?_)
    · exact mul_nonneg (θPos _) (by unfold Y Slit; rw [Finset.sum_apply]; exact sum_nonneg fun a _=>mul_nonneg (ht a) (norm_nonneg _))
    refine le_of_eq ?_; unfold Y Slit; rw [Finset.sum_apply, mul_sum]; exact sum_congr rfl fun i _=> mul_left_comm .. -- tune
 apply SBmono hx; unfold warpTax; rw [mul_sum]; exact le_of_eq (sum_congr rfl (fun i _=>by unfold H; ring))
omit p s
lemma Slit_receipt(r:ℕ)(k:r≤3)(g: SentK o Q)(T:100<f.val)(v:h≠0)(u:quote_B M Q o h r)(t: Single f×Single f→ ℝ)(a:∀ x, ‖Q x.1 x.2‖≤ t x) : ∀ i,‖CoverPull M G o Q i‖≤ Slit M G o t r i:=by
 intro i; rw [pull_twig g u T v k]; unfold Slit; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro k p; rw [HyT,norm_mul,norm_mul,norm_mul, call_bit, call_bit, one_mul, one_mul]; exact mul_le_mul_of_nonneg_right (a k) (norm_nonneg _)
end Boom
end YM.CF.TableF
end
