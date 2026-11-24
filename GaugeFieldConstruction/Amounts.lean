import GaugeFieldConstruction.Cookbook
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
open SeasonH
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
open SeasonH
-- aggregate paid ledgers & height-coherence
open Py.Rate.Pitching.Focus.CoeffArc Py.Riant Oath Py TableF
-- Ep Cost.Invoice Uniform.core. t0 all m.Price threshold Portfolio.
open NormedSpace
namespace VentureW
abbrev K7 :ℝ:=2^(6:ℕ)
abbrev Zeta :ℝ:=3/2 -- exp book
abbrev WidthW :ℝ:=8
abbrev Kerpu: ℝ:= Real.exp ((1:ℝ)*49^4)
lemma positiv_Vport(p k:ℕ):0≤VPort p k:=by unfold VPort; positivity
-- pre L $s fees after arbitrary roots stage. choose ζ threshold to give full Books
abbrev PreMeal (L: Side)(C:ℝ):Prop:=1≤ C ∧ (Real.exp Zeta * VPort 3 6*(max 1 (K7^2))+1)*(WidthW * Kerpu*C) + 1 ≤(RamoK L)/8
lemma pre_θ (C:ℝ)(v:1≤C): ∃ n:ℕ,∀ S:Side,n≤S.val →PreMeal S C:=by
 let T:=(Real.exp Zeta * VPort 3 6*(max 1 (K7^2))+1)*(WidthW*Kerpu*C)+1; have he:= (tendsto_rpow_atTop (show 0<Alto by unfold Alto; norm_num)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)); obtain ⟨i,h⟩:= Filter.eventually_atTop.mp (he.eventually_ge_atTop (8*T)); refine ⟨i,fun S p=>⟨v,?_⟩⟩; have hx :8*T ≤ RamoK S:= h _ p; change T ≤ RamoK S/8; linarith
variable (L:Side)(p:ℕ)(a c d k A B D C:ℝ)(hl:PreMeal L C)
-- before h.Typical absorption cost post<h.
abbrev pulse_H(L: Side)(c h A:ℝ):Prop:=1≤h ∧ c*Zell L.val Zeta*(K7^2*A/h^2) ≤1
lemma pulse_g (v:0≤ c)(t:0≤A):∀ᶠ h:ℝ in atTop,pulse_H L c h A:=by
 let u:= c*Zell L.val Zeta*(K7^2*A); filter_upwards [eventually_ge_atTop u,eventually_ge_atTop (1:ℝ)] with x h t
 refine ⟨t,?_⟩; rw [←mul_div_assoc]; have hp:0<x:=zero_lt_one.trans_le t; apply (div_le_iff₀ (by positivity:x^2>0)).mpr; rw [one_mul]; change u≤_; exact h.trans (by nlinarith)
-- row small functions.Assemble.Uc constant.
abbrev QpB(a D:ℝ)(k:ℕ)(x:ℝ):ℝ:= UVNext.PricedKernels.basin a * k * x -- use tune
variable (w:0<a)(v:a≤1)(ht:0≤ d)(hv:a≥2*d)(hk:2*a ≤ k)(e:0≤c)(htC:1 ≤ C)(tD:D≥0)(hA:0≤A)(hB:0≤B)
lemma G_c : 0≤ K7:=by unfold K7; positivity
include w
lemma QpB_p : 0≤UVNext.PricedKernels.basin a:=by
 let y:Site (1:Side):=0
 apply le_trans _ (UVNext.PricedKernels.funnel w y); exact Finset.sum_nonneg fun _ _=> (Real.exp_pos _).le
variable (m:ℕ)(Q h x:ℝ)
local notation "S0" Q:max V:max=> RhoP k WidthW (C * Q) V (UVNext.PricedKernels.basin a) p
-- table.BudgetClocks only cres.Q t.P. pay input scale. Frame $NoThreshold required ratio update w vertices.SL.C$
include htC
lemma QuantPos (pQ:0≤Q)(y:ℝ)(h:0≤y):0≤ S0 Q y:=by
 unfold RhoP Petro; have ht:0≤C:=zero_le_one.trans htC; have hp:= QpB_p a w; have hs:0 ≤ WidthW:=by norm_num [WidthW]
 positivity
lemma QuantUpper (pQ:0≤Q)(y:ℝ)(h:y≤Q): S0 Q y ≤ S0 1 1*Q:=by
 unfold RhoP Petro; have ht:= QpB_p a w; refine le_trans ?_ (le_of_eq (show UVNext.PricedKernels.basin a*p*(WidthW*Real.exp (k*49^4)*(C*Q)+WidthW*Q)=_ from (by ring))) -- tune
 gcongr -- width nonneg
omit w htC
-- ΔBorn uses r,k etc prove any D ≤1
abbrev Ωμ (a b:ℝ):= ΔBorn K7 (RadBill K7 a 1) a b 1 (Tax_D K7 a b 1)
include hA hB
lemma Ω_p : 0≤ Ωμ A B:=by
 let R:= RadBill K7 A 1; unfold Ωμ ΔBorn; have ht:0≤R:=by unfold R RadBill; have hp:= G_c; positivity; -- no extra args?
 have hv:0≤ Tax_D K7 A B 1:=by unfold Tax_D; have ht:= G_c; positivity
 have hp :0≤αR K7 (RadBill K7 A 1) A:=zero_le_one.trans (le_max_left ..); have h:= G_c; change 0≤ _ +K7*(_+ _*(K7*R*B)); unfold Δ_R; change 0 ≤ _+K7*(_*(_*(K7*R+_))+_ * (_ * (K7 *R+_))+ _); positivity
lemma Fund_growth (D C:ℝ)(p:0 ≤ D)(h:D≤1)(u:0≤C): ΔBorn K7 (RadBill K7 A D) A B C (Tax_D K7 A B D) ≤ C* Ωμ A B:=by
 let x:=K7; let r:= RadBill x A D; let R:= RadBill x A 1; let t:= Tax_D x A B D; let T:= Tax_D x A B 1
 have P0:0 ≤ K7:=G_c; have P:0≤x:= G_c; have hk:0≤r:=by unfold r RadBill; positivity
 have hf: r≤ R:=by unfold r R RadBill; gcongr
 have ht:0 ≤ t:=by unfold t Tax_D; positivity
 have hu:t≤ T:=by unfold t T Tax_D; gcongr
 have hv:0≤ R:= hk.trans hf; have he :0 ≤ T:= ht.trans hu
 have h1: αR x r A ≤ αR x R A:=by unfold αR ΘsF; gcongr -- lf
 have h2: Δ_R x r A t ≤ Δ_R x R A T:=by unfold Δ_R; gcongr
 unfold Ωμ ΔBorn; simp only [one_mul,mul_one]; apply le_trans (b:=αR x R A*C+x*(C*Δ_R x R A T+C*Δ_R x R A T+C*(x*R*B))) ?_ (le_of_eq (by unfold x R T; ring)); exact add_le_add (mul_le_mul_of_nonneg_right h1 u) (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 u) (mul_le_mul_of_nonneg_left h2 u)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf P) hB) u)) P)
abbrev QMaj (α p0:ℝ)(m:ℕ)(a k A B:ℝ):ℝ:= Ωμ A B *RhoP k WidthW p0 1 (UVNext.PricedKernels.basin α) m
include htC w
lemma MassPos:0≤ QMaj a C p a k A B:=mul_nonneg (Ω_p _ _ hA hB) (by simpa only [mul_one] using QuantPos p a k C w htC 1 zero_le_one 1 zero_le_one) -- arg order check
variable (hQ:0≤Q)(hF:0≤h)
include hQ
lemma crownPrice(y:ℝ)(b:0≤y)(u:y≤1)(g: QMaj a C p a k A B* Q≤1): let D:= QMaj a C p a k A B*Q; let V:= S0 Q (y*Q); 0 ≤ V∧ ΔBorn K7 (RadBill K7 A D) A B V (Tax_D K7 A B D)≤D:=by
 intro D V; have hp: 0≤D:=mul_nonneg (MassPos p a k A B C w htC hA hB) hQ; have hv:0≤V:=QuantPos _ _ _ _ w htC Q hQ _ (mul_nonneg b hQ)
 refine ⟨hv,(Fund_growth A B hA hB D V hp g hv).trans ?_⟩; have he: V ≤_:= QuantUpper p a k C w htC Q hQ (y*Q) (mul_le_of_le_one_left hQ u); exact (mul_le_mul_of_nonneg_right he (Ω_p _ _ hA hB)).trans_eq (by unfold D QMaj; rw [mul_comm _ (Ωμ ..),mul_one, ←mul_assoc]) -- tune match
include hl v e
abbrev port_W(L:Side)(a b c:ℝ):ℝ:= b*Zell L.val Zeta*tuneG K7 a*WidthW -- trim c
lemma debt_Tale (u:pulse_H L c h A)(t s:ℕ)(p:BudgetPoint)(f:p.power=3)(hp:p.order=6)(k:ℝ)(ke: c*Zell L.val Zeta * tuneG K7 A*WidthW*k ≤1): TaleX a WidthW h c d Zeta (k*Q) K7 A (C*Q) (VPort p.power p.order) L.val ≤ RamoK L /8 * Q:=by
 unfold TaleX
 let V':=WidthW*Real.exp (a*49^4)*C; let F:= Real.exp Zeta * VPort 3 6* max 1 (K7^2); let R:=c*Zell L.val Zeta*tuneG K7 A; let T:=c*Zell L.val Zeta *(K7^2*A/h^2)
 have ht': F+T ≤ F+1:=add_le_add le_rfl u.2; have hV:V'≤WidthW*Kerpu*C:=by unfold V'; apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans htC); apply mul_le_mul_of_nonneg_left _ (by norm_num [WidthW]); exact Real.exp_monotone (mul_le_mul_of_nonneg_right v (by positivity))
 have hv:0≤ V':=by unfold V'; have h:0≤C:=zero_le_one.trans htC; unfold WidthW; positivity
 rw [f,hp]; change (F+T)*(_*(C*Q))+ R*(WidthW*(k*Q))≤_
 have hu:0≤F+1:=by unfold F; have hx:=positiv_Vport 3 6; exact add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hx) (zero_le_one.trans (le_max_left ..))) zero_le_one
 have he:R*WidthW*k≤1:=ke; refine le_trans (b:= ((F+1)*(WidthW*Kerpu*C)+1)*Q) ?_ (mul_le_mul_of_nonneg_right hl.2 hQ); rw [add_mul ((F+1)*_) 1 Q]; apply add_le_add
 · rw [←mul_assoc (_*Real.exp _) C, mul_assoc (F+1)]; exact mul_le_mul ht' (mul_le_mul_of_nonneg_right hV hQ) (mul_nonneg hv hQ) hu
 rw [show R*_ =R*WidthW*k*Q from (by ring)]; exact mul_le_mul_of_nonneg_right he hQ
abbrev growthQ(L:Side)(c a V:ℝ): ℝ:= c*Zell L.val a* V+(Fintype.card TiltI:ℝ)*(c*Zell L.val a*V)
abbrev FullC(k:ℕ)(Y:BudgetPoint)(V:ℝ):ℝ:=Zell k Y.supportExponent -- tune trim
include ht hk hv
lemma Still_G (n:Side)(Ht:pulse_H L c h A)(W0:ℝ)(W₁:0≤W0)(T0:ℝ)(vW:W0≤1)(TQ:QMaj a C p a k A B*Q ≤1)(S_w: port_W L A c Zeta*W0 ≤1)(hB':BigE L.val c Zeta (QMaj a C p a k A B)≤ T0/8)(P:BudgetPoint)(pY:2*(ThermalH L.val*P.B) < (More n).val)(pV:24 ≤ P.B)(u:buyV P d c)(hv0: P.order=6)(pU:P.power=3)(Z: Zeta*2*(Yaw.χ (ThermalH L.val)) ≤↑P.B*d) :FellowC P (More n).val L.val p K7 a WidthW Zeta c d k h A B (QMaj a C p a k A B*Q) (C*Q) (W0*Q) (T0/8*Q) (RamoK L/8*Q):=by

 let q:=QMaj a C p a k A B; have he:BigE L.val c Zeta (q*Q)≤ T0/8*Q:= (le_of_eq (show BigE L.val c Zeta (q*Q)=BigE L.val c Zeta q*Q from by unfold BigE; ring)).trans (mul_le_mul_of_nonneg_right hB' hQ)
 have hε:K7=Γ0 P:=by rw [Γ0,hv0]
 refine ⟨pV,by norm_num [WidthW],w,Ht.1,(by norm_num [Zeta]),e,hε, mul_nonneg (zero_le_one.trans htC) hQ,mul_nonneg W₁ hQ,hv,ht,hk,Z,pY,hA,u,mul_nonneg (MassPos p a k A B C w htC hA hB) hQ,crownPrice p a k A B C w htC hA hB Q hQ W0 W₁ vW TQ,he,debt_Tale L a c d A B C hl w v e htC hA hB Q h hQ Ht p p P pU hv0 W0 S_w⟩ -- order pup band see
#print axioms debt_Tale
#check crownPrice
#check debt_Tale
end VentureW
end MintB
end MastTin
end YM.CF.XGarden
end
