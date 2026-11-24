import YM.SU5.FiniteGaugeData.Steam.Valence
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
/- Heights already paid at actual Course such that `Steam.Club` and any inputs in scope. Tool for toll estimates over the genuine physical period/cutoff. -/
namespace Steam
open Window LocalLimit Steve Next.Rank Preparation
variable {X:GivenX V U}{T:GramM (mid m B)}{K':Scree.Loom (mid m B)}{F:Marks.Tagged (mid m B)}{r:ℝ}
variable {y:ℝ}(Q:Flacon X T K' x h oracle)
local notation "θ"=> focusG X
local notation "NetA" => unlit T K.top.paths V.W.bar
local notation "δ"=> τ X x (mid m B)
namespace Indigo
variable {t n:ℕ}
local notation "F'"=> SU.group
local notation "gg"=> soaked T.beta
local notation "U₀"=> mid m B
abbrev accrual := 3*(2:ℝ)^SU.group.lieDim
private lemma billsD {N: Side}(V:Scree.GramM N)(g:ℝ)(p:0<g):rebate oracle V (2*g) ≤ rebate oracle V g * Real.exp (accrual* Rate.sites N):=by
 let n:=3*Fintype.card (Site (More N))-3; let d:= SU.group.lieDim; let h:=strength V.funds; let D:=oracle.big*((2*g)/h)^d; let a:ℝ:=2^d; have he: 0< h:=strength_pos _; have hv:0<oracle.big:= zero_lt_one.trans_le oracle.big_ge; have ht:0<D:=by unfold D; positivity; -- beware syntax
 have hp(n₀:ℕ)(h:n₀≤ 3*Fintype.card (Site (More N))): (n₀:ℝ)≤ 3* Rate.sites N :=by unfold Rate.sites; exact (Nat.cast_le.mpr h).trans_eq (by rw [site_card]; push_cast; rfl)
 have ha:0≤ a:=by unfold a; positivity
 change (oracle.big*((2*(2*g))/h)^d)^n ≤ D^n*_ ; rw [show (2*(2*g))/h=(2*g)/h*2 from (by ring),mul_pow _ 2 d,←mul_assoc oracle.big ((2*g/h)^d),mul_pow]; refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.le _)
 apply (pow_le_pow_left₀ ha ((Real.add_one_le_exp a).trans' (le_add_of_nonneg_right zero_le_one)) n).trans; change (Real.exp a)^n≤_; rw [←Real.exp_nat_mul]; exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (hp n (Nat.sub_le ..)) ha).trans_eq (show _=_ from by change _= 3*a*_; ring))
private lemma extra (t:Scree.GramM N)(g:ℝ)(p:0<g)(U:Pane N): basal t g U-basal t g U/2=basal t (2*g) U :=by
 rw [show basal t g U-basal t g U/2= basal t g U/2 from by ring]; unfold basal; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring_nf
-- norm-cost with LOCAL CHORD-basal tax consumption
local notation "Z"=> basal T gg
def baron (X:GivenX V U)(T:GramM (mid m B))(K':Scree.Loom (mid m B))(F:Marks.Tagged (mid m B))(x r:ℝ):Prop:=∀ i:Orbit (mid m B), ‖Marks.read F i (Graph.beam T U K' i)‖ ≤ r * Real.exp (τplus X x i.1+ basal T (soaked T.beta) i.1 /2)
include Q
lemma lesson(p:0≤r)(q:baron X T K' F x r):‖Marks.evaluate (Rate.field U T K') F‖ ≤ r * Real.exp (Fare x (mid m B) θ+ accrual*Rate.sites (mid m B)):=by
 let y:=field U T K'; let Λ:= soaked T.beta; have he: 0<Λ:=(amplifier _ (Q.stamp.budget _ Q.member).2.2.1).2.2.1; let V₀:= Real.exp (δ+NetA); let A(i:Orbit (mid m B)):=Real.exp (-basal T (2*Λ) i.1); obtain ⟨K0,t⟩:= repays oracle T (mul_pos two_pos he); let D:=accrual* Rate.sites (mid m B)
 have hb: ∀ i:Orbit (mid m B), ‖Marks.read F i (y i)‖ ≤ (r*V₀)*A i:=by
    intro i; let c:=υ K.top.clip x i.1; let v := Graph.past T i.1; change ‖Marks.read F i (Graph.recX U T K' i)‖ ≤ _; rw [Graph.porch,show v • _= (v:ℂ) • Graph.beam T U K' i from RCLike.real_smul_eq_coe_smul (K:=ℂ) ..,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (show 0≤v from (Real.exp_pos _).le)]
    apply (mul_le_mul (Q.outside i) (q i) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq
    let d₀:=τplus X x i.1 + Z i.1 /2; let g:= Z i.1; change Real.exp (NetA-c)*Real.exp (-g)*(r*Real.exp (δ+c+g/2))=(r*Real.exp (δ+NetA))*A i
    rw [← Real.exp_add, mul_left_comm _ r, mul_assoc r,← Real.exp_add]; unfold A; rw [← extra T Λ he, ← Real.exp_add]; unfold g Λ; ring_nf
 apply (norm_integral_le_of_norm_le (K0.const_mul (r*V₀)) (Eventually.of_forall hb)).trans; rw [integral_const_mul]; apply (mul_le_mul_of_nonneg_left (t.trans (billsD T Λ he)) (mul_nonneg p (Real.exp_pos _).le)).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ p; rw [Real.exp_add (Fare x _ _) _,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; rw [Real.exp_add,mul_assoc]; exact Q.full_z
abbrev slopeZ(X:GivenX V U)(g:ℝ):=slopeF X g+accrual
lemma steep (p:0≤r)(q:baron X T K' F x r)(y:ℝ)(hp:Real.exp (Fare x (mid m B) (-(2*y+1))) ≤ ‖compensated U T K'‖) : ‖Marks.ratio V U T K' F‖ ≤ r * Real.exp (slopeZ X y * (sites (mid m B))) := by
 let P:= Complex.exp (-T.v); have hP:P≠0:=Complex.exp_ne_zero _; let v:= Marks.evaluate (field U T K') F; let q' := compensated U T K'; have he:Marks.ratio V U T K' F = v/q':=by unfold q' v compensated field Marks.ratio; rw [Marks.scale_ket F]; exact (mul_div_mul_left _ _ hP).symm
 have hq:0< ‖q'‖:=(Real.exp_pos _).trans_le hp
 rw [he,norm_div]; refine (div_le_iff₀ hq).mpr ((lesson Q p q).trans ((mul_le_mul_of_nonneg_left hp (mul_nonneg p (Real.exp_pos _).le)).trans' ?_)); rw [mul_assoc r (Real.exp (slopeZ _ _ * _)),←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ p; apply Real.exp_monotone; unfold Fare slopeZ slopeF; nlinarith only [mul_le_mul_of_nonneg_right (le_abs_self θ) (zero_le_one.trans (sites_pos (mid m B)))]
omit Q
-- apply to current
variable {u:Preparation} {l i s k:ℕ}{H:(s:Side)→Scree.Loom s→ Prop}{Y:Course u H} (P:Club Y r s)
local notation "Γ₁"=> ((Y.voyage i).X (Y.uv k)).gram s
variable (X:Marks.Tagged (u.Ctor (Y.ir i) s))
include P
lemma Fore (t:0 ≤ y)(p:(Y.voyage i).kick≤ k)(v:s≤ Y.uv k)(b:baron u.W (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s) X (hat u.R.L u.x s) y):
 ‖Marks.ratio u.V u.U Γ₁ ((Y.voyage i).CapeT s) X‖≤ y*Real.exp (slopeZ u.W r*sites (u.Ctor (Y.ir i) s)):= steep (P.full i k v) t b r (P.lower i k p v)
#print axioms Fore
end Indigo
end Steam
end YM.CF.Py.Rate
