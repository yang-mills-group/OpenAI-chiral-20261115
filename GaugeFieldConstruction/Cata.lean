import GaugeFieldConstruction.Lunch
/-!
# Every torus endpoint envelope for PH Burn.
-/
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
variable {f c:Side} {M:Male}{G: Ratio c f}{A:Site f}{o:Skye.Seat f}{T:Script Male}{U σ B:Bool→ℝ}{V:Op (Single f)}{X:SM f→ℝ}{h b C:ℝ}{r m n:ℕ}
abbrev peakV (G:Ratio c f)(A:Site f)(y:DiamP):SM c:= (ηtag G A y.1,ηtag G A y.2)
lemma vanish_ev (y:DiamP)(x:SM c)(e:x≠peakV G A y): sliceAB G A x y=0:=by -- binder A
 unfold sliceAB Event; split <;> split; · rename_i p q; exact False.elim (e (Prod.ext p.symm q.symm))
 · rw [mul_zero]
 · rw [zero_mul]
 rw [mul_zero]
def Reperiod (G: Ratio c f)(A:Site f)(F: DiamP →ℝ)(x:SM c):= ∑' y, ‖sliceAB G A x y‖*F y
lemma Rep_nonneg {F:DiamP→ℝ}(p:∀ i,0≤ F i)(x:SM c)(A:Site f): 0≤ Reperiod G A F x:=tsum_nonneg fun i=>mul_nonneg (norm_nonneg _) (p _)
lemma θPay(x:DiamP):1≤ThetaX x:=by unfold ThetaX; exact (wagE ..).trans (le_add_of_nonneg_right (zero_le_one.trans (wagE ..)))
lemma θ_minor {F:DiamP→ℝ}(p:SumBudget (fun i=>ThetaX i * F i) C)(f:∀ i,0≤F i): SumBudget F C:= SBqual p f (fun i=>le_mul_of_one_le_left (f i) (θPay _))
lemma seglet {F:DiamP→ℝ}(p:SumBudget (fun i=>ThetaX i * F i) C)(ff:∀ i,0≤F i)(u:Odd G.count.val)(o:Skye.Seat f): WhX 3 (Reperiod G (AnchorN o) F) (downT G o) ≤ (24:ℝ)^3 *C:=by -- fix binder names
 let A:=AnchorN o; let K(v:SM c)(x):= ‖sliceAB G A v x‖ * F x; let W(v:SM c):= (1+ (opEnd (downT G o) v:ℝ))^3; have he:0≤ W:=fun _=> pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (Nat.cast_nonneg _))) _
 have ht(v:SM c):∀ i,0≤ K v i:=fun i=>mul_nonneg (norm_nonneg _) (ff _)
 have hp(v:SM c): SumBudget (K v) C:= SBqual (θ_minor p ff) (ht v) fun i=> mul_le_of_le_one_left (ff i) (eventPair ..)
 let V(i:DiamP):=∑ x:SM c,W x*K x i; have hx:Summable (fun x=>V x):= summable_sum (s:=univ) (fun i (_:i∈ (univ:Finset (SM c)))=>(hp i).2.1.mul_left (W i))
 have hh: WhX 3 (Reperiod G A F) (downT G o)= ∑' i,V i:=by unfold V; rw [Summable.tsum_finsetSum (fun i _=>(hp i).2.1.mul_left (W i))]; apply sum_congr rfl; intro i _; exact tsum_mul_left.symm
 have hv : SumBudget V ((24:ℝ)^3*C):=by
    apply SBqual (SBscale p (t:=24^3) (by positivity)) (fun i=>sum_nonneg (fun j _=>mul_nonneg (he j) (ht j i))); intro i; let k:=peakV G A i
    rw [sum_eq_single k]; refine (mul_le_mul (tax_prod u i o) (mul_le_of_le_one_left (ff i) (eventPair ..)) (ht k i) (mul_nonneg (by positivity) (θPos _))).trans_eq (mul_assoc ..); intro x _ q; unfold K; rw [vanish_ev _ _ q,norm_zero,zero_mul,mul_zero]; simp
 exact hh.trans_le hv.2.2
lemma remit {V:DiamP→ℂ}{F:DiamP→ℝ}(p:Summable F)(h:∀ i, ‖V i‖ ≤ F i)(A:Site f)(i:SM c): ‖remTag G A V i.1 i.2‖≤ Reperiod G A F i :=by
 let K:=sliceAB G A i; have he(t):=eventPair G A i t
 have hv : Summable (fun t=>‖K t‖*F t):=p.of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (h i))) fun i=>mul_le_of_le_one_left ((norm_nonneg _).trans (h i)) (he i)
 have hh(t): ‖K t*V t‖≤‖K t‖*F t:=by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)
 have hz:= hv.of_nonneg_of_le (fun x=> norm_nonneg _) hh; exact (norm_tsum_le_tsum_norm hz).trans (hz.tsum_le_tsum hh hv)
def Γrep (G:Ratio c f)(M:Male)(o:Skye.Seat f)(X:SM f→ℝ)(r:ℕ): SM c→ℝ:=Reperiod G (AnchorN o) (Slit M G o X r)
variable (p: Silks σ U B m)(u:3 ≤ m)(e:Odd G.count.val) (g:∀ i,0 ≤ X i)
include p u e g
abbrev ScoreBB (B:Bool→ℝ)(G: Ratio c f)(k:ℕ):=24^3 *10^3 * wageX G B k
lemma MajorV (v:r≤3)(o:Skye.Seat f)(M:Male): (∀ j,0≤ Γrep G M o X r j) ∧ WhX 3 (Γrep G M o X r) (downT G o) ≤ ScoreBB B G r * WhX 3 X o:=by
 let J:=Slit M G o X r; obtain ⟨h₀,F⟩:= SlitPay p u r v M o e X g; let w:=wageX G B r; have hh:0 ≤w:=by
    unfold w wageX; have he:=p.real; have hp:= Thorn.wool_pos G.count []; have ht:= α_pos G.count; have hc:0≤γE_0 G B:=mul_nonneg (zero_le_one.trans (he false)) hp; have hx:0 ≤ γE_1 G B:=mul_nonneg (zero_le_one.trans (he true)) hp; positivity
 refine ⟨fun i=> Rep_nonneg h₀ _ _,(seglet F h₀ e o).trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sell_w g) hh) (by positivity)).trans_eq (by unfold ScoreBB; unfold w; ring))⟩
lemma RemAni (sk:SentK o V)(hC:quote_B M V o h r)(v:100 < f.val)(u':r ≤3)(d:h≠0)(h:∀ i, ‖V i.1 i.2‖≤ X i)(L: Use 4 G.count T)(x:SM c): ‖Hove.totF 4 G e T M V x.1 x.2‖ ≤ Γrep G M o X r x:=by
 obtain ⟨v0,vT⟩:= SlitPay p u r u' M o e X g
 rw [show totF 4 G e T M V x.1 x.2=_ from (θ_summon G o p e x.1 x.2 L).symm]; exact remit (θ_minor vT v0).2.1 (Slit_receipt r u' sk v d hC _ h) _ _
-- gifts and casts needed later.
omit p u e g
lemma Wh_charge (p:BudgetPoint)(v:p.power=3)(h:ℝ)(V:SM c→ℝ)(o:Skye.Seat c): ∑ i:SM c, V i *tariff p o h (tray i.1 i.2)=h^2*WhX 3 V o:=by
 unfold WhX; rw [mul_sum]; refine sum_congr rfl fun i _=>?_; rw [E_card,v]; ring
lemma input_chime (p: BudgetPoint)(v:p.power=3)(h:ℝ)(o:Skye.Seat f)(κ:Finset (Dwell f)→ℝ)(k:∀ i,0≤κ i)(s:0 ≤ h): h^2*WhX 3 (fun i=>κ (tray i.1 i.2)) o ≤ ∑ i:Finset (Dwell f), tariff p o h i*κ i:=by
 rw [← Wh_charge p v]; let P(i:SM f):=Haro.tray i.1 i.2; refine le_trans (b:=∑ i∈ univ.image P,tariff p o h i*κ i) ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>?_); · rw [sum_image tray_in.injOn]; exact le_of_eq (sum_congr rfl fun i _=>mul_comm ..)
 exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg s _)) (k _)
end Boom
end YM.CF.TableF
end
