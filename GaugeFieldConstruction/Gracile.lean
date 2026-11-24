import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Oath Roots Riant
open SectorNext.Remainder.Scales
variable {L:Side}{a:ℝ}
abbrev dropX(q:ℝ)(x:ℝ):ℝ:= Real.exp (-q*radiusB x)
lemma wing_x0 (p:0<a)(b:ℕ): sizeK L b (dropX a):=by
 let s:=a/(b+1:ℕ); have hs:0 < s:=by unfold s; positivity
 have he: sizeK L 2 (dropX s):= Chaff.blight L hs
 apply (he.square (b+1) |>.low (show b ≤_ from (by omega))).cost_d; filter_upwards with x; apply le_of_eq; apply congrArg abs; unfold dropX; rw [←Real.exp_nat_mul]; congr 1; unfold s; field_simp
-- scaling $1/Q$ pays any via Hearth. compare S at g^k.
variable (R:Patch)(C a:ℝ)
local notation "G₅"=> SU.group
lemma divided_B (p:0 < a)(i j:ℕ):sizeK R.L i fun x=> dropX a x * C/ (coin₂ R x)^j:=by
 obtain ⟨u,z⟩:=sizeK.tint (L:=R.L) (wing_x0 p (i+2*j)) (sizeK.mild R.L C)
 refine ⟨u,?_⟩; filter_upwards [z,(year SU.group R.L).eventually_gt_atTop 0] with x v z; let X:=Scales.g SU.group R.L x; have he:0<X:=Scales.gauge G₅ R.L z
 rw [abs_div,show coin₂ R x=X^2 from rfl, abs_of_nonneg (by positivity :0≤(X^2)^j), div_le_iff₀ (by positivity)]; exact le_trans v (le_of_eq (by change X^(_+0)*_=_; rw [Nat.add_zero,pow_add,pow_mul]; ring))
lemma hover_k (t:ℕ)(p:0≤ C)(u:0<a) : ∀ᶠ x:ℝ in atTop,(2*(C*(10/coin₂ R x)))^t ≤ Real.exp (a*radiusB x):=by
 let A:=(2*C*10)^t
 filter_upwards [((divided_B R A a u 1 t)).spine.eventually (ge_mem_nhds zero_lt_one),(year G₅ R.L).eventually_gt_atTop 0] with x v z
 let X:=coin₂ R x; have hs:0<X:= by have he:=Scales.gauge G₅ R.L z; exact pow_pos he _
 have hv: dropX a x * A/X^t ≤ 1:= v; let B:=Real.exp (a*radiusB x); have hb:0<B:= Real.exp_pos _; have hz:dropX a x=B⁻¹:=by unfold dropX; rw [neg_mul,Real.exp_neg]; -- tune
 rw [hz, mul_div_assoc,inv_mul_le_iff₀ hb, mul_one] at hv
 calc
   _= A/X^t:=by change (2*(C*(10/X)))^t=(2*C*10)^t/X^t; rw [←div_pow]; congr 1; ring
   _≤ _:=hv
-- from budget.L Pair.Per migration.Price each m≥B.A paid.
private lemma ΥcB {C ε:ℝ} (t B:ℕ) (hv:0<ε) (p:1 ≤ C)(ht:1 ≤ B)(hu:(2*C)^t≤Real.exp (ε/16*B))(Hw: (3:ℝ)^4*(B:ℝ)^12 ≤ Real.exp (ε/16*B)) (u:∀ m:ℕ,B≤ m→ (15:ℝ)^4*(m:ℝ)^8 ≤Real.exp (ε/16*m)): Nice_B B t C ε:=by
 intro m hw; let α:=ε/8; let β:=ε/16; let KB:= (2*C)^t; have hz:0 ≤ KB:=by have he:=zero_le_one.trans p; unfold KB; positivity
 have h0:0<α:=by unfold α; positivity; -- rest adapted
 let k:=chip_B B m/cape_B B; let T:=pearl (chip_B B m+B); let W:= pearl (cape_B B); have hx:rentP C B m t=T*KB*((W:ℝ)*KB)^k:=by
    change (T:ℝ)*(W:ℝ)^k*(2*C)^((k+1)*t)=_; rw [Nat.mul_comm (k+1) t,pow_mul]
    change ↑T*(W:ℝ)^k*KB^(k+1)=_; rw [pow_succ,mul_pow]; ring
 have hβ : 0<β:=by unfold β; positivity
 have hT : KB ≤ Real.exp (β*m):=hu.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hw) hβ.le))
 have hA(m:ℕ):Real.exp (β*m)*Real.exp (β*m)=Real.exp (α*m):=by rw [←Real.exp_add]; congr 1; unfold β α; ring
 have ha:(T:ℝ)*KB≤Real.exp (α*m):=by
    have ht':(T:ℝ)≤ (15:ℝ)^4*(m:ℝ)^8:=by exact_mod_cast pearl_m B m ht hw
    exact (mul_le_mul (ht'.trans (u m hw)) hT hz (Real.exp_pos _).le).trans (le_of_eq (hA _))
 have hh:(W:ℝ)*KB≤Real.exp (α*B):=by
    have ht':(W:ℝ) ≤ (3:ℝ)^4*(B:ℝ)^12:=by exact_mod_cast pearl_y B ht
    exact (mul_le_mul (ht'.trans Hw) hu hz (Real.exp_pos _).le).trans (le_of_eq (hA _))
 have hy:= mul_le_mul ha (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hz) hh k) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz) _) (Real.exp_pos _).le
 refine hx.trans_le (hy.trans ?_)
 have hK: (k:ℝ)* B≤ 6*(m:ℝ):=by exact_mod_cast sev_B B m ht
 rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; calc
    _ = α*m+ α*((k:ℝ)*B):= by ring
    _ ≤ α*m+ α*(6*m):= add_le_add_right (mul_le_mul_of_nonneg_left hK h0.le) _
    _ ≤ _:=by unfold α; nlinarith [Nat.cast_nonneg (α:=ℝ) m]
lemma highMark (t:ℕ)(h:0<a)(w:0<C):∀ᶠ x:ℝ in atTop, 1 ≤ C*(10/coin₂ R x)∧ Nice_B (radiusB x) t (C*(10/coin₂ R x)) a:=by
 have hβ:0 < a/16:=by positivity
 let V:= Work.E01.radiusB_tendsto; have hv:Tendsto (coin₂ R) atTop (𝓝 0):= (Riant.coin_B (R:=R)).height_r.low (by norm_num:1≤2) |>.spine
 obtain ⟨u,vu⟩:= eventually_atTop.mp (tear_r (15^4) _ 8 hβ)
 filter_upwards [V.eventually_ge_atTop u,V.eventually_ge_atTop 1,(year SU.group R.L).eventually_gt_atTop 0,hv.eventually (ge_mem_nhds (show 0<C*10 from by positivity)),hover_k R C _ t w.le hβ,V.eventually (tear_r (3^4) _ 12 hβ)] with x p hp v f g z
 let D:= C*(10/coin₂ R x); have he:1 ≤ D:=by
    have hv:0 < coin₂ R x:=pow_pos (Scales.gauge SU.group R.L v) _
    unfold D; rw [←mul_div_assoc,le_div_iff₀ hv,one_mul]; exact f
 exact ⟨he,ΥcB t _ h he hp g z (fun i y=> vu i (p.trans y))⟩
end Focus
end Pitching
end YM.CF.Py.Rate
end
