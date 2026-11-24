import GaugeFieldConstruction.Rook
/-! Compare *test locations* not pressure footprints. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
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
variable {f c:Side}{G:Ratio c f}{A:Site f}{o: Skye.Seat f}{p:Odd G.count.val}{Q:Op (Single f)}{M:Male}{h:ℝ}{S: DiamP→ℂ}
def gated(i j:Kt)(h:ℝ)(S:DiamP→ℂ)(x:DiamP):ℂ:= if (i,j)=(x.1.2,x.2.2) then (h^2:ℂ)*S x else 0
-- coefficient of coded independently lifted informative window; physical h retained
noncomputable def RawInfinity(G:Ratio c f)(o:Skye.Seat f)(S:DiamP→ℂ)(h:ℝ) (v:Views) : Pal:= Matrix.of fun i j=>∑' x:DiamP,PayS (pairF G o x) v * gated i j h S x
abbrev Pier(h:ℝ)(c:Side)(t:ℝ):=1000*(96:ℝ)^2/c.val*h^2*t
def closePay (G:Ratio c f)(o:Skye.Seat f)(s:DiamP):Views→L[ℝ]ℝ:= let z:=downT G o; let k:=peakV G (AnchorN o) s; κviews z k.1.1.1 k.2.1.1
def neo (G: Ratio c f)(o:Skye.Seat f)(x:DiamP):ℂ:= let A:=AnchorN o; let c:=downT G o; let v:=peakV G A x; Caller c v.1.1.1*Caller c v.2.1.1*sliceAB G A v x
lemma neo_bound(x:DiamP): ‖neo G o x‖≤1:=by unfold neo; simp only [norm_mul,call_bit, one_mul]; exact mul_le_one₀ (event_origin ..).2 (norm_nonneg _) (event_origin ..).2
-- finite stream entries in basis
lemma Stream_i (G: Ratio c f)(U:Op (Single c))(o:Skye.Seat c)(h:ℝ)(i j:Kt) (v:Views): streamF o U h v i j=∑ x: SM c, if (i,j)=(portB x.1,portB x.2) then PayS (κviews o x.1.1.1 x.2.1.1) v * hill_Z o U h x.1 x.2 else 0:=by
 unfold streamF; rw [Matrix.sum_apply]; apply sum_congr rfl; intro l _; let Z:=PayS (κviews o l.1.1.1 l.2.1.1) v* hill_Z o U h l.1 l.2; change Matrix.single (portB l.1) (portB l.2) Z i j= _; rw [Matrix.single_apply]; split_ifs with p h t <;> first|rfl|simp_all [Prod.ext_iff,eq_comm]
variable (p:Odd G.count.val)(o)
private abbrev Brand (o:Skye.Seat f)(A: DiamP→ℂ): Prop:= Summable (fun i=> ThetaX i *‖A i‖)
lemma shore0 {Z: DiamP →ℂ}(w: Brand o Z): Summable (fun i=>‖Z i‖):= w.of_nonneg_of_le (fun i=> norm_nonneg _) fun i=>le_mul_of_one_le_left (norm_nonneg _) (θPay i)
lemma Fshore (w: Brand o S)(i j:Kt)(v:Views)(h:ℝ)(U: Op (Single c))(wU:∀ k l: Single c,U k l=remTag G (AnchorN o) S k l):streamF (downT G o) U h v i j= ∑' x:DiamP,PayS (closePay G o x) v*(neo G o x*gated i j h S x):=by
 let T:=downT G o; let Q:= AnchorN o; let Z(x:SM c):=Caller T x.1.1.1*Caller T x.2.1.1; let E(x:SM c):=PayS (κviews T x.1.1.1 x.2.1.1) v
 let F(s:SM c)(x:DiamP) := (if (i,j)=(portB s.1,portB s.2) then E s*Z s*(h^2:ℂ) else 0) * (sliceAB G Q s x * S x)
 have he(s:SM c): Summable (F s):= Summable.mul_left _ (remCash (G:=G) (A:=Q) (shore0 o w) s.1 s.2)
 rw [Stream_i (f:=f) G];
 have hx(x: SM c): (if (i,j)=(portB x.1,portB x.2) then PayS (κviews T x.1.1.1 x.2.1.1) v* hill_Z T U h x.1 x.2 else 0) =∑' y,F x y:=by
    unfold F; rw [tsum_mul_left]; split
    next h=> unfold hill_Z E Z; rw [wU]; unfold remTag; unfold Q T; ring -- tune
    next h=> rw [zero_mul]
 change (∑ x: SM c, (if (i,j)=_ then PayS (κviews T _ _) _ * hill_Z T U h x.1 x.2 else 0))= _; rw [sum_congr rfl (fun x _=> hx x),← Summable.tsum_finsetSum (fun i _=>he i)]
 refine tsum_congr fun x=>?_ ; let z':=peakV G Q x; rw [sum_eq_single z'];
 · unfold F; change (if (i,j)= (x.1.2,x.2.2) then E z'*Z z'*(h^2:ℂ) else 0)* (sliceAB G Q z' x*S x)= E z'*( (Z z'* sliceAB G Q z' x)*gated i j h S x); unfold gated; split <;> ring
 · intro a _ h; unfold F; rw [vanish_ev _ _ h,zero_mul,mul_zero]
 simp
-- bounds tail costs on each scalar window; normalize missing σ factor
lemma γG (i j:Kt)(x:DiamP) : ‖gated i j h S x‖≤ h^2 * ‖S x‖:=by
 unfold gated; split; · rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_eq_abs,sq_abs]
 rw [norm_zero]; positivity
variable {E:Type}
private abbrev BasisF:= Ole Views ℂ
abbrev deltaM (i:DiamP):ℝ:=96*δBase i
lemma δMP(i:DiamP):1 ≤ deltaM i:= le_trans (δBase_p i) (le_mul_of_one_le_left (zero_le_one.trans (δBase_p i)) (by norm_num))
lemma boundS (F:DiamP→ℂ)(u:Summable fun i=> (deltaM i)^2*‖F i‖)(x:DiamP→Views→L[ℝ]ℝ) (p:∀ i,‖x i‖≤deltaM i): ∃ v:BasisF,AptK (fun t=>∑' i:DiamP,PayS (x i) t * F i) v∧ CostOle v ≤ ∑' i:DiamP,(deltaM i)^2*‖F i‖:=by obtain ⟨V,v,b,_⟩:=mainStream F x deltaM p δMP u; exact ⟨V,v,b⟩
omit o
open scoped Classical
abbrev TimelyPair (c:Side)(i:DiamP):Prop:= Timely c i.1∧ Timely c i.2
lemma FarOff (i:DiamP)(p:¬TimelyPair c i): c.val ≤1000*δBase i:=by
 unfold TimelyPair Timely at p; push Not at p
 let T (k:Mill):ℕ:=1000*(1+lateral k.1);
 have hp(k:Mill)(t:c.val ≤T k): (c.val:ℝ) ≤ 1000* Ladder k.1:=by unfold Ladder; exact_mod_cast t
 by_cases h:T i.1 < c.val; · apply le_trans (hp i.2 (p h)); exact mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity)
 apply le_trans (hp i.1 (Nat.le_of_not_lt h)); exact mul_le_mul_of_nonneg_left (le_max_left ..) (by positivity)
def payAble (ι:DiamP → ℝ) (u:ℝ):Prop:= ∑' i,ι i ≤u
lemma tax_Fu (x: DiamP):δBase x^2 ≤ ThetaX x:= (pow_le_pow_right₀ (δBase_p x) (by decide:2≤3)).trans (thetaRange x)
lemma Γjoint {a:ℝ}(e: FlightFlux.chime ThetaX S a)(P:DiamP→ℂ)(v:∀ x, ‖P x‖≤ h^2*‖S x‖) : SumBudget (fun i=> deltaM i^2*‖P i‖) ((96:ℝ)^2*h^2*a):=by
 apply SBqual' (SBscale e (t:=96^2*h^2) (by positivity)) _ le_rfl _; · intros; positivity
 intro i; apply (mul_le_mul_of_nonneg_left (v i) (sq_nonneg _)).trans; unfold deltaM; rw [mul_pow]; exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (tax_Fu i) (by positivity)) (by positivity)) (le_of_eq (by ring))
lemma Γfar {a:ℝ}(h:ℝ)(e: FlightFlux.chime ThetaX S a)(P:DiamP→ℂ)(v:∀ x, ‖P x‖≤ h^2*‖S x‖) (c:Side) (w:∀ x,TimelyPair c x → P x=0) : SumBudget (fun i=> deltaM i^2*‖P i‖) (Pier h c a):=by
 let C:= (c.val:ℝ); have hp:0 < C:=Nat.cast_pos.mpr c.property; apply SBqual' (SBscale e (t:=(1000*(96:ℝ)^2/C)*h^2) (by positivity)) _ le_rfl _; · intros; positivity
 intro i; by_cases g: TimelyPair c i; · rw [w i g,norm_zero, mul_zero]; have he:= θPos i; positivity
 apply (mul_le_mul_of_nonneg_left (v i) (sq_nonneg _)).trans;
 let V:=δBase i; have hv:0 ≤ V:=zero_le_one.trans (δBase_p i) -- shadows h ℝ
 have ht:deltaM i^2 ≤ 1000*(96:ℝ)^2/C * ThetaX i:=by
    change (96*V)^2 ≤ _; rw [mul_pow, div_mul_eq_mul_div, le_div_iff₀ hp]; have hu:=FarOff i g; have hx: 1000*V ≥ C:= hu
    calc _ ≤ 96^2*V^2*(1000*V):=by exact mul_le_mul_of_nonneg_left hx (by positivity)
         _ = 1000 * (96:ℝ)^2*V^3:=by ring
         _ ≤ _:=mul_le_mul_of_nonneg_left (thetaRange i) (by positivity)
 exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq (by ring)
end Boom
end YM.CF.TableF
end
