import YM.SU5.FiniteGaugeData.Lapis.Saturn
import YM.SU5.FiniteGaugeData.Lapis.Cloche
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Affiche
open Next.Rank.Axial CF.Font
variable {n: Side}{G: Gauge}{F:Clip}{P:Bed}{u:Stage}{R:PathData G} {z:LogField G n}{Y:Finset (Bond n)}{a d' C Δ:ℝ}
local notation "Ve"=> coin (Plush G (denim n))
local notation "E"=> Vault (Plush G (denim n))
local notation "Color"=> G.ColorIndex
local notation "A"=> axle n
local notation "B"=> zodiac P G (denim n)
local notation "I"=> denim n
lemma solventS (x: coin (LT n)):∃ y:coin (LT n), (lasers n)*ᵥ y=0 ∧ tickets (axle n)*ᵥ y=0 ∧ d 1 n *ᵥ y = d 1 n*ᵥ x:=by
 let K:= amble (n:=n) ((n.val:ℝ)⁻¹ • (lasers n *ᵥ x)); let y:=x-K; let u:=descend (axle n) (tickets (axle n)*ᵥ y); refine ⟨y-ant u,?_,?_,?_⟩
 · rw [mulVec_sub,lasers_ant,sub_zero]; unfold y K; rw [mulVec_sub, lasers_read, smul_smul, mul_inv_cancel₀ (by exact_mod_cast n.property.ne'),one_smul]; exact sub_self _
 · rw [mulVec_sub, tickets_bill (axle n) (ant u),onTab]; exact sub_self _
 unfold y; rw [mulVec_sub,mulVec_sub,ant_c, show d 1 n *ᵥ K=0 from amble_d _, sub_zero,sub_zero]
-- assemble all colors.
lemma nomadicA (x: coin (Plush G (denim n))): ∀ i:Color,tickets (axle n)*ᵥ KickC (denim n) x i=0:=by
 intro i; rw [tickets_bill]; ext j; have he: j.val∉denim n:=by rw [denim,Finset.mem_compl,not_not]; exact j.property
 exact congrArg (fun y:G.Color=>y i) (at_key x j he) -- tune
lemma nomadicL(x:coin (LT n))(h:tickets (axle n)*ᵥ x=0):∃ y:coin (↥(denim n)), foot (tabKey (denim n)) *ᵥ y=x:=by
 refine ⟨x ∘ (tabKey I),?_⟩; ext i; by_cases z:i∈ Set.range (tabKey I)
 · obtain ⟨i,rfl⟩:= z; exact hold (tabKey I) (tab_in _) _ i
 rw [blankA _ _ z]; rw [tickets_bill] at h; obtain ⟨i,rfl⟩:= (portfolio n).surjective i
 by_cases u:i∈ (axle n).trunks; · exact (congr_fun h (⟨i,u⟩:stem (axle n))).symm
 exact False.elim (z ⟨⟨i,mem_compl.mpr u⟩,rfl⟩)
lemma beholdA (x:Ve) (z:∀i:Color,lasers n*ᵥ KickC _ x i=0): dotProduct x (zodiac P G (denim n)*ᵥ x)=Bid.gaugeFiscal P (kickC (denim n) x) (kickC (denim n) x):=by
 unfold Bid.gaugeFiscal zodiac; rw [chrome_eraP]; apply sum_congr rfl; intro i _; rw [costsA]; let V:=KickC I x i
 change dotProduct V (chips (axle n) P*ᵥ V)=dotProduct V (plaid P n*ᵥ V)
 unfold chips; rw [plus_bill,plus_bill,prize_bill,prize_bill]; rw [show lasers n*ᵥ V=0 from z i,show tickets (axle n)*ᵥ V=0 from nomadicA x i]; simp
-- equivalence tests for moment data, independent of t harmonic and Gauge. Do not interpret full point fields.B.
abbrev motive (x y:LogField G n):Prop:= ∀ i:G.ColorIndex, d 1 n*ᵥ parts G 1 x i=d 1 n*ᵥ parts G 1 y i
lemma sapph {x y:LogField G n}(h:motive x y): Bid.gaugeFiscal P x x=Bid.gaugeFiscal P y y:=by
 unfold Bid.gaugeFiscal; apply sum_congr rfl; intro i p; rw [show K (P.metric.acts n)=plaid P n from rfl,plaid_cost,plaid_cost,h] -- tune
-- every budget standardized root
variable (D:Floor P u.clip n a C)(h:0<a)
local notation "Ω"=> bridgeB (B) (shine (denim n) G D h)
def olive (G:Gauge): Vault (Plush G (denim n)) →ₗ[ℝ] LogField G n:=(keyM G (denim n)).comp (bridgeB (zodiac P G (denim n)) (shine (denim n) G D h)).toLinearMap
include D h
lemma sunflower(W:R.Bounds u.clip u.width u.paths Δ)(H:Attached P R)(x:E): Bid.gaugeFiscal P (olive D h G x) (olive D h G x) ≤‖x‖^2 :=by
 let Q:= (denim n); change Bid.gaugeFiscal P (kickC Q (Ω x)) (kickC Q (Ω x))≤_; rw [←wholeC D W H, ← attainedE _ W H]; change ‖castM Q W H D h x‖^2 ≤ _; exact pow_le_pow_left₀ (norm_nonneg _) (glance (denim n) W H D h x) 2
lemma fillC (x:LogField G n): ∃ v:E, motive (olive D h G v) x ∧ Bid.gaugeFiscal P x x=‖v‖^2 :=by
 choose y hL hT hd using fun i:G.ColorIndex=> solventS (parts G 1 x i); choose v hv using fun i:G.ColorIndex=> nomadicL (y i) (hT i)
 let z:Ve:=fun i=> v i.2 i.1; let g:= (Ω).symm z; let w:= olive D h G g; have hh(i:Color): KickC (denim n) z i= y i:= hv i; have hp: w = kickC (denim n) z:= by unfold w g olive; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl
 have he : motive w x:=by intro i; rw [hp,show parts G 1 (kickC (denim n) z) i=KickC (denim n) z i from rfl,hh]; exact hd i
 refine ⟨g,he,?_ ⟩; rw [← sapph he,hp, ← beholdA (P:=P) z (by intro i; rw [hh]; exact hL i),← chalk (B) (shine (denim n) G D h) g]; rw [show (Ω g)=z from LinearEquiv.apply_symm_apply _ _]
end Affiche
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Affiche.fillC
