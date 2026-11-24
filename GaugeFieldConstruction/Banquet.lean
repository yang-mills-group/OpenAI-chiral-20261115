import GaugeFieldConstruction.Marsala
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
open Planned.PrimaryIntegral295 Carrier Jade Vow Bake
open Py Riant
namespace PinRack
variable (P:PinRack)
abbrev CoarseP(P:PinRack)(L:Side) := PieceFee (P.tagP L)+Etching 2 P.dawnCost
abbrev Headliner(P:PinRack)(L:Side):=2500*(P.relic L)+ SectorVal*Etching 2 P.dawnCost
abbrev Cap_φ(P:PinRack)(L:Side):=1+P.CoarseP L+P.Headliner L
lemma hillsS: SlowP P.Cap_φ:=by
 let E:=P.GainH; let B(L:Side):=P.tagP L
 have hp : SlowP B:=(SlowP.level _).prod P.primary
 have ht : SlowP P.relic:= (SlowP.level _).join ((SlowP.level _).prod P.primary)
 exact SlowP.join ((SlowP.level 1).join (((SlowP.level _).prod hp).join (SlowP.level _))) (((SlowP.level _).prod ht).join (SlowP.level _)) -- tuning
private lemma hSn: 0 ≤ SectorVal:= (show (0:ℝ)≤2500 by norm_num).trans (le_max_left ..)
abbrev εTag:= PieceFee 1
abbrev ζTax:= Etching 2 1
lemma piece0:0 ≤ εTag:=by unfold εTag PieceFee; have h:= Jε₀; positivity
lemma etch0:0≤ζTax:= by unfold ζTax Etching PieceFee; have h:= Jε₀; positivity
variable (L:Side)
lemma rates_nn : 0≤P.tagP L ∧ 0≤ P.dawnCost∧ 0 ≤ P.relic L:= by
    have ht: 0 ≤ P.GainH L:=Gain_nn ..; have hx:=P.arcNN; have hv:0 ≤caL:= Coffer_n; have hP:=P.floored; have hi:= P.rising_nn; have ha:0≤LaE:=ζLodge
    refine ⟨?_,?_,?_⟩; · unfold tagP; positivity
    · unfold dawnCost; have he:=hLeap; positivity
    unfold relic hCost_P mC; positivity
lemma ImpEc (a b:ℝ):PieceFee a+Etching 2 b= εTag*a+ζTax*b:=by unfold εTag ζTax Etching PieceFee; ring
lemma elderTag : 0 ≤ P.CoarseP L ∧ 0 ≤ P.Headliner L:= by
    obtain ⟨p,h,u⟩:= P.rates_nn L; unfold Headliner CoarseP; rw [ImpEc]; refine ⟨add_nonneg (mul_nonneg piece0 p) (mul_nonneg etch0 h), add_nonneg (mul_nonneg (by norm_num) u) (mul_nonneg hSn ?_)⟩; unfold Etching PieceFee; have he:=Jε₀; positivity
lemma opticX : 1 ≤ P.Cap_φ L:=by obtain ⟨a,b⟩:=P.elderTag L; exact (le_add_of_nonneg_right a).trans (le_add_of_nonneg_right b)
-- Tip Application Exact.w quant
variable {m n b:Side}(F:GramM (mid n b))(F':BudgetPoint)(M':Tulip.Male)(o:Seat (mid m b))(X:Scree.Hub (mid n b))(h:ℝ)(H_Deb:Vow.Pax (mid n b))(T:RegBudget (mid m b))(v Q fog k e x:ℝ)
  (hk: P.TokenAC F F' M' L o X.val.1 h (lagE X) H_Deb T v Q fog k e x)
  (s:ℝ)(p:Crafts F.p X.val.1 H_Deb h 2 s)(hx:0<h)(hs:F.p.order=6)(ht:F.p.power=2)(v₀:24≤ F.p.B)(hA:(Zhub X.val.1).val.2⊆X.val.2)(hpK: coverNumber F.p.B X.val.2 ≤ L.val +1) (mU:300<(mid n b).val)
abbrev Tipκ (e k:ℝ):= εTag*(leadTip k e)+ ζTax * dawnT' k e
abbrev FeePostC (f Q v k e:ℝ):=2500*museTip f Q v k e +SectorVal*(ζTax *dawnT' k e)
abbrev PyraFee(k:ℕ)(a d s:ℝ):= Real.exp (3*(k:ℝ))*(2*chi_f 6*Jε*a+chi_f 6*a)+Real.exp (3*(k:ℝ))*(2*chi_f 6*s)+Real.exp (3*(k:ℝ))*((2*chi_f 6*d)+(2*chi_f 6*Jε*d+chi_f 6*d)) -- tune
abbrev OrbitFee(L:Side)(P:PinRack)(Q k e s:ℝ):= PyraFee (L.val+1) (P.tagP L * Q + leadTip k e) (P.dawnCost * Q + dawnT' k e) s
variable (u:0 ≤ k)(z:0 ≤ e)(A:ℝ)(hQ:Q≤A)(a:0≤Q)(he:0≤v)(hv:F.p.threshold=temp x)(hg:0 ≤ fog)
abbrev StepPay(P:PinRack)(L:Side)(j:ℕ)(Q e k:ℝ):=P.Cap_φ L * αInk L j Q+Tipκ e k
abbrev StepPay'(P:PinRack)(L:Side)(j:ℕ)(Q δ e k:ℝ):=P.Cap_φ L * (αInk L j δ+αInk L (j+1) Q) + Tipκ e k
abbrev StepCore(P:PinRack)(L:Side)(f v k e q A:ℝ)(j:ℕ):= P.Cap_φ L * αInk L (j+1) q+ FeePostC f A v k e
include hk p hx hs ht v₀ hA hpK mU u z hQ a
lemma Wallτ (Tp:Ids (mid n b))(j r:ℕ)(h':j ≤ 3)(hB:r ≤2)(w: ∀ i:Scree.Hub (mid m b), i.val.1=o→Cresc L.val F' i → CarBot _ o (KeyUp F') M' (T i) h j) : Basalt F.p X.val.1 L.val (L.val+1) (Fetch Tp F.J.M F.p h X H_Deb L.val r) (P.StepPay L j Q e k) 2 (OrbitFee L P A k e s) h r F.J.M:=by
    have he:= hk.general j h' w
    have ht₁:=P.tag_V L Q v k e j h' a u; have ht₂:= (P.dawn_P L Q k e u a).1
    have hS:=he.shift ht₁ ht₂
    let C:= αInk L j Q; let D:= leadTip k e; let U:=dawnT' k e; let δ:=αInk L 3 Q
    have hx': δ≤C:=mul_le_mul_of_nonneg_right (existα L _ _ (by omega)) a; have h:0 ≤ C:=by unfold C αInk; exact mul_nonneg (pow_nonneg (α_pos _).le _) a
    obtain ⟨h0,h1⟩:=P.elderTag L; obtain ⟨h2,h3,h4⟩:=P.rates_nn L
    apply (fullB (n:=r) Tp F.J.M X p hx hs ht v₀ hpK hA mU hB hS rfl).sharpen
    · rw [ImpEc]; apply le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (show 0≤(1:ℝ) from zero_le_one)).trans (le_add_of_nonneg_right h1)) h) _); -- tune ambiguous instantiate
      unfold CoarseP; rw [ImpEc]; change εTag* (P.tagP L*C + D)+ ζTax*(P.dawnCost*δ+U) ≤ _
      unfold Tipκ; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx' h3) (show 0≤ζTax from etch0)] -- tune goal P.S._ syntax
    unfold OrbitFee PyraFee IaTax AtTax Flame_B; rw [hs];
    have ht: C ≤A:= (mul_le_of_le_one_left a (pow_le_one₀ (α_pos _).le (αsmall L))).trans hQ;
    let Y:= P.tagP L*C +D; let R:=P.dawnCost*δ+U; have hc:Y≤ P.tagP L*A+D:= add_le_add_left (mul_le_mul_of_nonneg_left ht h2) _
    have hR:R ≤ P.dawnCost*A+U:= add_le_add_left (mul_le_mul_of_nonneg_left (hx'.trans ht) h3) _
    let Ez:= spicy_f 6; let Y' := Jε₀; gcongr
include he hv hg
lemma Wallθ (Tp:Ids (mid n b))(j r:ℕ)(h':j≤r)(hB:r ≤ 2)(W:Waves)(uF: MetaB o M' W (T (Zhub o)) (KeyUp F') h)(wp:CarBot _ o (KeyUp F') M' (T (Zhub o)) h j)(w:∀ i:Scree.Hub (mid m b), i.val.1=o→Cresc L.val F' i → i≠Zhub o → CarBot _ o (KeyUp F') M' (T i) h (j+1))(W':∀ i:Scree.Hub (mid m b), i.val.1=o→Cresc L.val F' i → CarBot _ o (KeyUp F') M' (T i) h j) : let Y:= Fetch Tp F.J.M F.p h X H_Deb L.val r; Basalt F.p X.val.1 L.val (L.val+1) Y (P.StepPay' L j Q ‖MSlot j W‖ e k) 2 (OrbitFee L P A k e s) h r F.J.M ∧ ‖CardT Y (KeyUp F.p) F.J.M h X.val.1 j-MoonIdeal j L (KeyUp F.p) (KeyUp F') W‖ ≤ P.StepCore L fog v k e Q A j:=by
    intro Y; obtain ⟨ez,wz⟩:= hk.lead j (by omega) W uF wp w; let δ:= ‖MSlot j W‖; let X':= αInk L (j+1) Q; let U:= leadTip k e; let K:= αInk L 3 Q; let R:= αInk L j δ + X'
    obtain ⟨h0,h1⟩:=P.elderTag L; obtain ⟨h2,h3,h4⟩:=P.rates_nn L
    have H:= ez.shift (P.leadCap L k e δ v Q j (by omega) (show 0≤δ from norm_nonneg _) a) ((P.dawn_P L Q k e u a).2) -- tune norm instance
    have hh:=fullB Tp F.J.M X p hx hs ht v₀ hpK hA mU hB H rfl -- tune l
    have hp:0 ≤ X':= mul_nonneg (pow_nonneg (α_pos _).le _) a
    have he':X'≤R:=le_add_of_nonneg_left (mul_nonneg (pow_nonneg (α_pos _).le _) (norm_nonneg _));
    have hx':K ≤ X':= mul_le_mul_of_nonneg_right (existα L _ _ (by omega)) a
    constructor
    · have g:= Wallτ P L F F' M' o X h H_Deb T v Q fog k e x hk s p hx hs ht v₀ hA hpK mU u z A hQ a Tp j r (by omega) hB W'
      have ht₁:= hh.tags; refine ⟨?_,ht₁,g.keeps⟩; obtain ⟨C,hc⟩:= hh.rates; refine ⟨C,ArenaC.moveup hc (sub_le_sub_right ?_ _)⟩
      rw [ImpEc]; unfold StepPay'; apply le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right (show P.CoarseP L≤P.Cap_φ L from (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right h1)) (hp.trans he')) _); unfold CoarseP; rw [ImpEc]; unfold Tipκ; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hx'.trans he') h3) etch0]
    have hxz:= P.Ephos L k e v h Q fog A j (by omega) a hg u z hQ he
    have hy:= plate_X (l:=L.val) Tp F.J.M X p hx hs ht v₀ hpK hA mU hB H hv (O₀:=Zhub o) wz h' uF; apply hy.trans
    change 2500*_+ SectorVal* Etching 2 (P.dawnCost*K+dawnT' k e) ≤ _
    apply le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right (show P.Headliner L≤ P.Cap_φ L from le_add_of_nonneg_left (add_nonneg zero_le_one h0)) hp) _)
    have ht(v:ℝ):Etching 2 v= ζTax*v:=by unfold ζTax Etching PieceFee; ring
    unfold Headliner FeePostC; rw [ht (P.dawnCost*K+_), ht P.dawnCost]
    linarith only [hxz,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx' h3) etch0) hSn]
end PinRack
end BellPrice
end YM.CF.Oath
end
