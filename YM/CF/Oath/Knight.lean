import YM.CF.Oath.Forge
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "V'"=> Support (Domain N B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
-- ACCOUNT PARROT aggregating costs after selection
open Trees
variable {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "ζ"=>Raid CM
-- Scalar BURY closed WK money. Exposure carve. reserve no projection.T.
local notation "Λbf"=> (Finset (Dwell (mid P B)))
local notation "RK"=> Track (Ride S) (Raid CM)
variable (Qx : TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G))
variable (kp:∀ i B,Suite (badge _) (pinH G t true) (pinH G t false) B (Qx i B) (W i B))(ht: ∀ i B, Suite (badge _) (pinH G t true) (pinH G t true) B (Qv i B) (heal G t Y i B))
variable {p':ℝ}(o:Seat (mid P B))(U:Support (Domain N B))(k':ℕ)
local notation "o'"=> (S.ratio.parent o)
variable (KD:BudgetPoint)(a v' h':ℝ)(b0 s:ℕ)(w:v'*2*Yaw.χ s≤b0*a)(b':0 ≤ v')(u:0<b0)(r0:kR≤ s*b0)(g':0≤a) (gU:Eire.mint S p∈U)(eZ:0≤h')
local notation "Cz"=> (currency b0 v' U)
local notation "λx"=> (Real.exp (v'*(Yaw.χ s:ℝ)))
local notation "Fie"=> payZ G k' Qv
section
local notation "Vq"=> Scree.tariff KD (S.ratio.parent o) h'
variable {I:Type}[LinearOrder I][Fintype I]
variable (r₀ r₁: Prism.Rock (mid P B))(huS:S.ratio=Rush.ratio G)
local notation "bY"=> (Qx (true,true))
local notation "cY"=> (Qx (true,false))
include u r0 b' g' w kp g_ huS eZ
variable (A':Support (Domain N B)) (C S':ℝ)
local notation "P₁"=> paintL G r₀
local notation "P₂"=> paintL G r₁
local notation "bV"=> Stilo.beamH A'
local notation "cZ"=> currency b0 v' A'
variable (C_:0 ≤ C)(hr:S.ratio.parent (Cube.node r₀.1)∈ A')(hr':S.ratio.parent (Cube.node r₁.1)∈ A')
-- AGGREGATE THEORY ANY Both legs mesh.Length.ge.Event.*
include C_ hr hr'
abbrev mapK (J:Finset ((Support (Domain P B))× Support (Domain P B))):Track (Ride S) (Raid (LeanV (Single (mid N B)))):=∑ i∈J,∑ p: Rock (mid N B),∑ q:Rock (mid N B),billQ (S:=S) kR Qx r₀ r₁ (Stilo.beamH A') C p q i.1 i.2
variable (J:Finset ((Support (Domain P B))× Support (Domain P B)))
local notation "cΨ"=> cZ
lemma roll_v : 0 ≤ mapK (S:=S) kR Qx r₀ r₁ A' C J ∧ Strung A' (rateT Vq (mapK (S:=S) kR Qx r₀ r₁ A' C J)) b0 v' (∑ i∈J,∑ p:Rock (mid N B),∑ q:Rock (mid N B),ridQ (S:=S) Qx o KD h' r₀ r₁ a v' s b0 A' p q i.1 i.2 C):=by
 let L(p q)(i j):= billQ (S:=S) kR Qx r₀ r₁ (Stilo.beamH A') C p q i j; let R(p q)(i j):=ridQ (S:=S) Qx o KD h' r₀ r₁ a v' s b0 A' p q i j C
 have H(i j)(p q):0≤ L p q i j ∧ Strung A' (rateT Vq (L p q i j)) b0 v' (R p q i j):= silt_k W g_ kR Qx kp o KD a v' h' b0 s w b' u r0 g' eZ r₀ r₁ huS A' C C_ hr hr' p q i j -- order
 have hu (i j:ρ)(p: Rock (mid N B)):= sumsQ A' b0 univ (fun q: Rock (mid N B)=>L p q i j) Vq (fun q=> R p q i j) (fun q _=>(H i j p q).1) (fun q _=>(H i j p q).2); have hv(i j:ρ):= sumsQ A' b0 univ (fun p: Rock (mid N B)=> ∑ q: Rock (mid N B),L p q i j) Vq (fun p=>∑ q:Rock (mid N B), R p q i j) (fun p _=>(hu i j p).1) (fun p _=>(hu i j p).2)
 exact sumsQ A' b0 J (fun i=>∑ p: Rock (mid N B),∑ q: Rock (mid N B),L p q i.1 i.2) Vq (fun i=>∑ p: Rock (mid N B),∑ q: Rock (mid N B),R p q i.1 i.2) (fun i _=>(hv i.1 i.2).1) (fun i _=>(hv i.1 i.2).2)
variable {hΦ:ℕ}{δ z₀:ℝ} (hhC:∀ i∈ J,hΦ ≤ i.1.card+i.2.card) (δ0:0 ≤ δ)(gρ:∀ j,incline (hall G t) KD.power (G.count.val:ℝ)⁻¹ (fun _=> z₀) (a+δ) (Qx j))
local notation "ψ"=> (pactB G KD.power)
local notation "R₂"=> (Haro.amt KD.power)
include hhC δ0 gρ
abbrev lorp (a:ℝ)(s m:ℕ)(z:ℝ):ℝ:=flavor*(flavor*(Real.exp (a*Yaw.χ s)^2 * (3:ℝ)^m))*(flavor*z)*(flavor*z)
local notation "Δ"=> (Real.exp (-δ*(hΦ:ℝ)))
local notation "QP"=> R₂ o r₀ r₁
local notation "tΦ"=> lorp v' s KD.power z₀
set_option maxHeartbeats 800000 in
lemma spendL : Strung A' (rateT Vq (mapK (S:=S) kR Qx r₀ r₁ A' C J)) b0 v' (cΨ* Δ *tΦ * (Haro.amt KD.power o r₀ r₁*h'^2*C)):=by
 have h:= (roll_v W g_ kR Qx kp o KD a v' h' b0 s w b' u r0 g' eZ r₀ r₁ huS A' C C_ hr hr' J).2
 let Λ:= flavor*z₀; let VU:ℝ:=3^KD.power -- collision local
 let B₁(X:ρ)(p):= ψ r₀ p*(Branch.rent (a+δ) X* paintL G r₀ p (bY X)); let B₂(X:ρ)(p) := ψ r₁ p*(Branch.rent (a+δ) X * paintL G r₁ p (cY X));
 let K':= flavor*(flavor*(λx*λx*VU)); let Z':= cΨ*Δ*K'*(Haro.amt KD.power o r₀ r₁*h'^2*C)
 have hp(U:ρ)(p):0 ≤ B₁ U p:=mul_nonneg (by unfold pactB; positivity) (mul_nonneg (rent_pos ..).le (gust_l G bY _ _ _ (fun i=>(kp _ _).nonn))); have hg(U:ρ)(p):0 ≤ B₂ U p:= mul_nonneg (by unfold pactB; positivity) (mul_nonneg (rent_pos ..).le (gust_l G cY _ _ _ (fun i=>(kp _ _).nonn)))
 have hec:= add_nonneg g' δ0
 have hQ:∑ U:ρ,∑ p:Rock (mid N B), B₁ U p≤Λ:=by rw [sum_comm]; exact bow_i g_ (a+δ) hec bY (fun i=>(kp _ i).nonn) (gρ _) r₀
 have hG:∑ U:ρ,∑ p:Rock (mid N B),B₂ U p≤Λ:=by rw [sum_comm]; exact bow_i g_ (a+δ) hec cY (fun i=>(kp _ i).nonn) (gρ _) r₁
 have hr':0 ≤ cΨ:=(Real.exp_pos _).le
 have hz:0 ≤ flavor:= Nat.cast_nonneg _
 have h₁(X Y:ρ)(p q)(hi:hΦ ≤ X.card+Y.card): ridQ (S:=S) Qx o KD h' r₀ r₁ a v' s b0 A' p q X Y C ≤ Z'*(B₁ X p*B₂ Y q):=by
    have he: Branch.rent a X * Branch.rent a Y ≤ Δ * (Branch.rent (a+δ) X*Branch.rent (a+δ) Y):=by
       unfold Branch.rent; simp only [←Real.exp_add]; apply Real.exp_le_exp.mpr; have hι:(hΦ:ℝ)≤ X.card+Y.card:= by exact_mod_cast hi
       linarith only [mul_le_mul_of_nonneg_left hι δ0]
    have hh : Haro.amt KD.power (S.ratio.parent o) p q ≤ VU* QP* ψ r₀ p * ψ r₁ q:=by rw [huS]; exact Haro.amtV ..
    let W:= paintL G r₀ p (bY X)*paintL G r₁ q (cY Y); have hU:0 ≤ QP:=by unfold Haro.amt; positivity
    let κR:= λx*λx*flavor*flavor*W*(cΨ*h'^2*C); have huW:0 ≤ W:=mul_nonneg (gust_l G bY _ _ _ fun i=>(kp _ _).nonn) (gust_l G cY _ _ _ fun i=>(kp _ _).nonn)
    have hW:0 ≤ κR:=by unfold κR; positivity
    calc
       _ = κR*(Haro.amt KD.power (S.ratio.parent o) p q*(Branch.rent a X*Branch.rent a Y)):=by unfold κR W ridQ; ring -- `_` binder
       _ ≤ κR*((VU*QP*ψ r₀ p*ψ r₁ q)*(Δ*(Branch.rent (a+δ) X*Branch.rent (a+δ) Y))):=mul_le_mul_of_nonneg_left (mul_le_mul hh he (mul_nonneg (rent_pos ..).le (rent_pos ..).le) ?_) hW
       _ = _:=by unfold Z' κR K' B₁ B₂ W; ring
    apply le_trans _ hh; unfold Haro.amt; positivity
 have hΦ' :0≤∑ U:ρ,∑ p:Rock (mid N B), B₁ U p:= sum_nonneg fun i _=>sum_nonneg fun j _=>hp i j; have hw:0 ≤ Z':=by unfold Z' K' VU Haro.amt; positivity
 refine ⟨h.hand,h.spear,h.pay.trans ?_⟩; apply le_trans (sum_le_sum (fun i p=>sum_le_sum (fun j _=> sum_le_sum (fun k _=>h₁ i.1 i.2 j k (hhC i p)))))
 have hu: Z'*(Λ*Λ) = cΨ* Δ *tΦ*(Haro.amt KD.power o r₀ r₁*h'^2*C):=by unfold Z' K' lorp VU Λ; ring
 rw [←hu]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul hQ hG (sum_nonneg fun i _=>sum_nonneg fun j _=>hg i j) (hΦ'.trans hQ)) hw)

 let F'(i:ρ×ρ):=∑ j:Rock (mid N B),∑ k:Rock (mid N B),Z'*(B₁ i.1 j* B₂ i.2 k)
 apply le_trans (b:=∑ i:ρ×ρ,F' i) (sum_le_sum_of_subset_of_nonneg (f:=F') (subset_univ _) (fun i _ _=> sum_nonneg (fun j _=>sum_nonneg (fun k _=>mul_nonneg hw (mul_nonneg (hp i.1 j) (hg i.2 k))))))
 apply le_of_eq; rw [Fintype.sum_prod_type, sum_mul_sum]; unfold F'; simp_rw [sum_mul_sum,mul_sum]
end
end YM.CF.Oath
