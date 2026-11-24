import GaugeFieldConstruction.BankLight
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
open Lenten Layout Fren FlightFlux Fluxim
open Planned.PrimaryIntegral295 Carrier
namespace PinRack
variable (P:PinRack)(L:Side)
abbrev Floating(P:PinRack)(L:Side)(c:ℝ):=P.mass*P.rising*c
abbrev ArcRise (P:PinRack):= P.mass*P.rising+2*P.rising
abbrev SummitH (P:PinRack)(L:Side):= stipe P.Fc P.B L
abbrev GainH(P:PinRack)(L:Side):= P.ArcRise + P.SummitH L * (P.rising+1+2*Hcost)
lemma primary : SlowP P.GainH:= (SlowP.level _).join ((stipeS P.Fc P.B).prod (SlowP.level _))
lemma rising_nn:0 ≤ P.rising:=add_nonneg (zero_le_one.trans P.planet.2.2.2.2.2.1) (by norm_num)
lemma arcNN:0 ≤ P.ArcRise:=by unfold ArcRise; have hp:=P.rising_nn; have he:= P.floored; positivity
lemma SummitH_nn:0 ≤ P.SummitH L:=by unfold SummitH stipe; positivity
lemma Gain_nn:0 ≤ P.GainH L:=by unfold GainH; have hp:= P.SummitH_nn L; have he:=P.rising_nn; have hv:=P.arcNN; have hs:= HC_pos; positivity
lemma existα (a b:ℕ)(p:a ≤ b):αN L^b ≤ αN L^a:=pow_le_pow_of_le_one (α_pos _).le (αsmall L) p
lemma Silence(j:ℕ)(p:j≤3)(c:ℝ)(hc:0≤c)(b:ℝ):P.σGrow j L b c ≤ P.GainH L * (αN L^(3+j) * c):=by
 have hv:=existα L (3+j) 6 (by omega); have hy:0≤ αN L:=(α_pos _).le; let s:=P.SummitH L; have hs:0≤ s:= P.SummitH_nn L; have hb:= P.rising_nn; let U:=P.ArcRise;
 calc
    _= U*(αN L^6*c) + (s*P.rising)*(αN L^(3+j)*c):=by unfold σGrow DeepL SaltL SPart U ArcRise Plough s SummitH; ring
    _≤ U*(αN L^(3+j)*c)+ s*(P.rising+1+2*Hcost)*(αN L^(3+j)*c):=by apply add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv hc) P.arcNN); refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hs) (mul_nonneg (pow_nonneg hy _) hc); have ht:= HC_pos; linarith
    _=_:=by rw [←add_mul] -- tune rfl
lemma SplitLead(j:ℕ)(p:j≤2)(c q v:ℝ)(t:0≤c)(r:0≤q):P.Splitμ L v q c j ≤ P.GainH L * (αN L^(3+j)*c + αN L^(3+(j+1))*q):=by
 have hJ:=existα L (3+(j+1)) 6 (by omega); let g:=αN L; have hg:0 ≤g:=(α_pos _).le
 let s:=P.SummitH L; have hs:0≤ s:=P.SummitH_nn L
 let W:= g^(3+(j+1)); let U:=g^(3+j); let B:=Hcost; have hB:0 ≤ B:= HC_pos; have hp0:0 ≤ P.rising:=P.rising_nn; have he:=P.arcNN; have hU:0≤U:=pow_nonneg hg _; have hW:0≤ W:=pow_nonneg hg _
 calc
    _= P.ArcRise*(g^6*q)+s*U*(B*c)+s*W*q+s*W*(B*c):=by unfold Splitμ DeepL SaltL SPart Plough ArcRise g B U W s SummitH; unfold g; ring
    _≤ P.ArcRise*(W*q)+s*U*(B*c)+s*W*q+s*U*(B*c):=by refine add_le_add ((add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ r) he) _) _)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (existα L _ _ (by omega)) hs) (mul_nonneg hB t))
    _≤ P.GainH L*(U*c)+ P.GainH L*(W*q):=by
       have h0:2*s*B ≤ P.GainH L:=by change _ ≤ P.ArcRise+s*(P.rising+1+2*B); rw [mul_add]; nlinarith only [he,hs,hp0,mul_nonneg hs hp0]
       have h1:P.ArcRise+s ≤ P.GainH L:=by apply add_le_add_right; exact le_mul_of_one_le_right hs (by linarith : 1 ≤ P.rising+1+2*B)
       linarith only [mul_le_mul_of_nonneg_right h0 (mul_nonneg hU t),mul_le_mul_of_nonneg_right h1 (mul_nonneg hW r)]
    _=_:= by rw [←mul_add] -- tune
lemma Grow_n (q:ℝ)(p:0≤q)(v:ℝ)(j:ℕ):0≤P.σGrow j L v q:=by unfold σGrow DeepL SaltL Plough SPart; have hp:=α_pos L; have hP:= P.floored; have hX:= P.rising_nn; unfold stipe; positivity
lemma split_V(q:ℝ)(p:0≤q)(v:ℝ)(j:ℕ)(t:ℝ)(k:0≤t):0≤P.Splitμ L v q t j:=by unfold Splitμ DeepL SaltL SPart Plough; have hp:=α_pos L; have hP:= P.floored; have hX:= P.rising_nn; have ht:=HC_pos; unfold stipe; positivity
lemma Coffer_Zeta(a:ℝ)(h:0 ≤ a):Oath.Coffer SqBrim a = Oath.Coffer SqBrim 1*a:=by
 unfold Coffer; rw [add_mul,max_mul_of_nonneg _ _ h]; simp_rw [mintPay]; congr 1; · ring
 congr 1 <;> ring
lemma Coffer_n :0 ≤ Oath.Coffer SqBrim 1:=by
 have h:=Oath.BellPrice.PinRack.Coffer.monoQ (show (0:ℝ) ≤1 from zero_le_one) (show 0≤ SqBrim from by unfold SqBrim; positivity)
 have he:Oath.Coffer SqBrim 0=0:=by simp [Coffer,mintPay]
 rw [he] at h; exact h -- newline
abbrev caL := Oath.Coffer SqBrim 1
abbrev LaE := LodgeCost 1
abbrev leadTip (k e:ℝ):=GCost*e+2*GCost*k
abbrev tagP (P:PinRack)(L:Side):=2*LaE*P.GainH L
abbrev αInk (L:Side)(j:ℕ)(y:ℝ):= αN L^(3+j)*y
lemma leadCap (k e ℓ v V :ℝ)(j:ℕ)(p:j≤2)(u:0≤ℓ)(hx:0 ≤ V):P.LeadDot L v V ℓ k e j ≤ P.tagP L * (αInk L j ℓ + αInk L (j+1) V) + leadTip k e:=by
 let Z:=P.AnchorP; let X:=P.σGrow (j+1) L v V; let Y:=P.Splitμ L v V ℓ j; let D:=αInk L j ℓ + αInk L (j+1) V
 have h: X ≤ P.GainH L*D:=by
    apply (P.Silence L _ (by omega) _ hx v).trans; apply mul_le_mul_of_nonneg_left _ (P.Gain_nn _); exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg (α_pos _).le _) u)
 change GCost*e+( (LodgeCost Y+ GCost*k)+(LodgeCost X+GCost*k))≤_
 rw [αCost Y,αCost X]; unfold leadTip tagP
 linarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ LaE from ζLodge),mul_le_mul_of_nonneg_left (show Y≤ P.GainH L * D from P.SplitLead L j p ℓ V v u hx) ζLodge] -- tune U syntactic
lemma tag_V (Q v k e :ℝ)(j:ℕ)(t:j ≤3) (p:0≤Q)(u:0≤k) : P.TagMorn L v Q k e j ≤ P.tagP L * αInk L j Q + leadTip k e:=by
 let V:=αInk L j Q; have he:= P.Gain_nn L; have hx:0≤ V:=by unfold V αInk; have hx:=α_pos L; positivity
 unfold TagMorn AnchorP; rw [αCost]; unfold leadTip tagP
 have hS:0≤GCost:= (Real.exp_pos _).le
 have hg: LaE*P.σGrow j L v Q ≤ LaE*(P.GainH L * V):=mul_le_mul_of_nonneg_left (P.Silence L j t Q p v) ζLodge
 nlinarith only [hg,mul_nonneg hS u, mul_nonneg (mul_nonneg (show 0≤ LaE from ζLodge) he) hx] -- tune syntax Lodge
abbrev dawnCost(P:PinRack):= 2* leaps 6 3 3*P.mass*P.rising
abbrev dawnT'(k e:ℝ):=e+2*k
lemma hLeap : 0≤ leaps 6 3 3:=by unfold leaps; positivity
lemma dawn_P(V k e:ℝ)(p:0≤ k)(q:0≤ V) : P.T_Post L V k e ≤ P.dawnCost*αInk L 3 V + dawnT' k e ∧ P.W_Post L V k e ≤ P.dawnCost*αInk L 3 V + dawnT' k e:=by
 have h : 0 ≤ P.σDawn L k V:=by unfold σDawn CabinZ SPart; have hp:=α_pos L; have he:= P.floored; have ht:=P.rising_nn; have h:=hLeap; positivity
 have he:P.W_Post L V k e=P.dawnCost * αInk L 3 V + dawnT' k e:=by unfold W_Post dawnT' dawnCost αInk σDawn SPart CabinZ; ring -- tune 3+3
 rw [←he]; exact ⟨add_le_add_right (le_add_of_nonneg_right h) _,le_rfl⟩
abbrev mC:= ((6:ℕ).factorial:ℝ)
abbrev hCost_P(P:PinRack):= caL*mC* P.ArcRise + P.rising
abbrev relic (P:PinRack)(L:Side):=P.hCost_P + caL*LaE* P.GainH L
abbrev museTip(f c v k e:ℝ):= caL*(GCost*e)+(caL*k+ (f*fortK*(v*c)+caL*(GCost*k)))
lemma Ephos (k e v h c f Q:ℝ)(j:ℕ)(p:j≤2)(u:0 ≤ c)(l:0 ≤ f)(w:0 ≤ k)(z:0 ≤e)(y:c≤Q)(a:0 ≤ v): P.HeadPost L v h c f k e j ≤ P.relic L * αInk L (j+1) c + museTip f Q v k e:=by
 have hh:0≤GCost:=(Real.exp_pos _).le; have hg: P.DeepL L v c=P.ArcRise*(αInk L 3 c):=by unfold DeepL SaltL SPart ArcRise αInk; ring
 let t0:=αInk L 3 c; let Z:=αInk L (j+1) c; have ht:0 ≤t0:=by unfold t0 αInk; have ht:=α_pos L; positivity; -- semicolon
 have hW:t0≤Z:=mul_le_mul_of_nonneg_right (existα L _ _ (by omega)) u
 let γ:= P.σGrow (j+1) L v c
 have hb:P.AnchorP L γ k=LaE*γ+GCost*k:=congrArg (fun i=>i+GCost*k) (αCost γ)
 have hz0:0 ≤ P.AnchorP L γ k:= by rw [hb]; exact add_nonneg (mul_nonneg ζLodge (P.Grow_n L c u v _)) (mul_nonneg hh w)
 unfold HeadPost μMood τAppease; rw [Coffer_Zeta k w,Coffer_Zeta (GCost*e) (mul_nonneg hh z),Coffer_Zeta (P.AnchorP L γ k) hz0,hg,Coffer_Zeta _ (mul_nonneg (by positivity) (mul_nonneg (P.arcNN) ht))]; -- tune
 let K:=f*(fortK:ℝ); have hp:0 ≤ K:=mul_nonneg l (Nat.cast_nonneg _)
 have hy:αN L^6*(P.rising*c) = P.rising*t0:=by unfold t0 αInk; ring
 rw [hy,hb]; unfold relic hCost_P museTip; let D:=P.ArcRise
 linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (P.arcNN)) (show 0≤ mC by positivity)) (show 0 ≤caL from Coffer_n), mul_le_mul_of_nonneg_left hW (P.rising_nn),mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left y a) hp,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show γ ≤ P.GainH L * Z from P.Silence L _ (by omega) _ u _) (show 0 ≤ LaE from ζLodge)) (show 0 ≤caL from Coffer_n)] -- transparency arithmetic syntax issues
end PinRack
end BellPrice
end YM.CF.Oath
end
