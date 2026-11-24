import YM.CF.Lor.Hat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable (L:Side)
local notation "g"=> Scales.g SU.group L
local notation "y"=> Scales.y SU.group L
local notation "P"=> Scales.p SU.group L
namespace rates
open sizeK
lemma arm(v:ℝ→ℝ)(t:ℝ)(p:sizeK L n v) :sizeK L n (fun x=> Jet.composeCost d (v x) t):=(p.scale _).tint (mild L _)
lemma year_r (t:ℝ)(f:ℝ→ℝ)(h:sizeK L (l+2) f):sizeK L l fun x=> t*y x*f x:= ((sizeK.yearsK (n:=l) L h).scale t).cost_d (Eventually.of_forall fun x=> Eq.le (congrArg abs (mul_assoc ..)))
lemma slopeK (f:ℝ→ℝ)(h:sizeK L (l+1) f)(t:ℝ):sizeK L l fun x=> (t/g x)*f x:=by
 obtain ⟨C,h⟩:= h; have h' := mild L t; obtain ⟨D,h'⟩:=h'; refine ⟨C+D,?_⟩
 filter_upwards [h,h',(year SU.group L).eventually_gt_atTop 0] with x h hp hx; simp only [pow_zero,one_mul] at hp; have hb:=gauge SU.group L hx; rw [abs_mul,abs_div,abs_of_pos hb]; apply (mul_le_mul ((div_le_div_iff_of_pos_right hb).2 hp) h (abs_nonneg _) (div_nonneg (pow_nonneg (pos ..).le _) hb.le)).trans_eq; rw [pow_add,pow_add]; field_simp
lemma burn_k (P':Patch)(a:ℝ):sizeK P'.L 1 (fun x=> Cay.burn a x P'):=((coin P'.L).accrue (sizeK.fierce _)).scale a
lemma cowK: sizeK L 0 aimC :=(Bcash L).powC _ -- namespace?
variable (C M s t D B:ℝ)(R:Patch)
local notation "p'"=> Scales.p SU.group R.L
local notation "L'" => R.L
local notation "g'"=> Scales.g SU.group R.L
local notation "y'"=> Scales.y SU.group R.L
local notation "f"=>fun x=> Cay.burn s x R
local notation "w"=> fun x:ℝ=>B*p' x
local notation "κ"=> Jet.composeCost
local notation "Z"=> fun x=>2*y' x
-- Converts life in β
variable (l n)
def bill (B C M:ℝ)(s b u:ℝ)(μ:ℝ)(x:ℝ):= let X:=Cay.bankU*μ; b*(X*(C*(aimC x*(fiery G₅ x L')^2))) + X*(2^n*(C*Neige.lamp x)*μ) + u*(about L' (horn x l)*κ n (2^n*κ n ((M+M)*s^3) 1+2^n*(2^n*κ n ((M+M)*s^3) 1)) (1/2))
def bull(M:ℝ)(z u s v:ℝ):=κ n (u*z*(bankU*v*(2^n*M*(M*s^(l+2))))+(bankU*v)*(v*(M*s^3))) (1/2)
private lemma coal_k:sizeK L 0 (fun x=>(about L (Cay.horn x l):ℝ)):=by
 let C:= ((Bcash L).scale (↑(l+76:ℕ):ℝ)).accrue ((Bcash L).scale (↑(l+76:ℕ):ℝ))
 unfold Cay.about Cay.horn; push_cast; push_cast at C; exact (((C.accrue (mild L _)).powC _).scale _) -- tune syntactic
lemma bill_s :sizeK L' 1 fun x=>bill n l R D C M (f x) (2/g' x) (Z x) (w x) x:=by
 have hx:= burn_k R s; have hp: sizeK L' 0 w:= (height L').scale B; let X:=fun x=>bankU*w x; have hX:sizeK L' 0 X:= hp.scale _; let A(x):=κ n ((M+M)*f x^3) 1; have hA:sizeK L' 3 A:=arm L' _ 1 ((hx.square 3).scale _)
 let Q:=sizeK.scale ( (cowK L').tint ((fierce L').square 2)) C; exact ((slopeK (l:=1) L' _ (hX.tint Q) _).accrue (hX.tint ((((coin L').scale C).scale (2^n)).tint hp))).accrue (year_r (l:=1) L' _ _ ((coal_k l L').tint (arm L' _ (1/2) ((hA.scale (2^n)).accrue ((hA.scale (2^n)).scale (2^n)))))) -- order
lemma bill_h (h:3 ≤ l):sizeK L' 3 fun x=>bull n l C (2*g' x) (Z x) (f x) (w x):=by
 have he:= burn_k R s; have hx: sizeK L' 4 (fun x=>f x^(l+2)):= (he.square _).low (by omega); have hh:sizeK L' 0 w:=(height L').scale B; let V:= (hh.scale Cay.bankU).tint ( (mild L' (2^n*C)).tint (hx.scale C)); apply arm L'; apply accrue ?_ ((hh.scale _).tint (hh.tint ((he.square _).scale _))); exact (year_r (l:=3) L' 2 _ ( ((main _).scale (2:ℝ)).tint V)).cost_d (Eventually.of_forall fun x=> Eq.le (congrArg abs (mul_assoc ..)))
private lemma coupling_buy(x β:ℝ)(h:β∈Set.Icc (y x/2) (2*y x))(p:0<y x): |β| ≤ 2*y x ∧ |coupling β| ≤ 2*g x ∧ |coupling β|⁻¹ ≤ 2/g x:=by
 have hv:0<β:= (half_pos p).trans_le h.1; have he:=coupling_pos hv; rw [abs_of_pos hv,abs_of_pos he]; obtain ⟨i,t⟩:= compare_v G₅ L x h p; refine ⟨h.2,i,?_⟩; change 0 < coupling β at he
 rw [←one_div]; exact (div_le_div_iff₀ he (Scales.gauge G₅ L p)).mpr (by rw [one_mul]; exact t)
-- L budget after cap ANY.Z recorded. Seek both saturated cap and trimmed. low-degree needs Z polynomial not P. 
variable {β x:ℝ}
lemma check_b (v:ℝ)(hv:0≤v)(hm:v≤w x)(h:β∈Set.Icc (y' x/2) (2*y' x))(p:0<y' x)(t:0≤f x)(a:0 ≤ temp x)(b:0≤ C)(d:0≤M): 0≤ coarseZ R n n l (f x) x β C (fiery G₅ x R.L) M v ∧ coarseZ R n n l (f x) x β C (fiery G₅ x R.L) M v ≤ bill n l R D C M (f x) (2/g' x) (Z x) (w x) x:=by
 have he:= coupling_buy L' x β h p; let s:=f x; have hp:0 ≤ s := t; change _∧coarseZ _ _ _ _ s _ _ _ _ _ _≤ _; change 0≤ coarseZ _ _ _ _ s _ _ _ _ _ _∧ _
 have hh:0≤bankU:=by unfold bankU; positivity
 have hk:0≤Neige.lamp x:=by unfold Neige.lamp; positivity
 have hz:0≤B*p' x:=hv.trans hm
 constructor
 · unfold coarseZ aimC Jet.composeCost; dsimp only; positivity
 unfold coarseZ bill; dsimp only; have ht:0≤ aimC x:=by unfold aimC; positivity
 have hbn:=Scales.gauge SU.group R.L p; gcongr <;> first|exact he.2.1|exact he.2.2|exact he.1|unfold Jet.composeCost; positivity
lemma check_h (v:ℝ)(hv:0≤v)(hm:v≤w x)(h:β∈Set.Icc (y' x/2) (2*y' x))(p:0<y' x)(t:0 ≤ f x)(b:0≤C):0 ≤ Cay.glenZ n l β C v (f x)∧ Cay.glenZ n l β C v (f x) ≤ bull n l C (2*g' x) (Z x) (f x) (w x):=by
 have he:= coupling_buy L' x β h p; have hh:0≤bankU:=by unfold bankU; positivity
 let z:= f x; have ht:0≤ z:=t; have hy:0≤B*p' x:=hv.trans hm; have hb:0<β:= (half_pos p).trans_le h.1; have hk:=coupling_pos hb; change 0 ≤ Cay.glenZ _ _ _ _ _ z ∧ Cay.glenZ _ _ _ _ _ z ≤ bull _ _ _ _ _ z _
 unfold Cay.glenZ bull Jet.composeCost; constructor
 · positivity
 have hbn:0≤ Z x*(2*g' x):=mul_nonneg (mul_nonneg (by norm_num) p.le) (mul_nonneg (by norm_num) (Scales.gauge G₅ R.L p).le)
 gcongr <;> first|exact h.2|exact ((abs_of_pos hk).symm.trans_le he.2.1)|exact hm
end rates
end YM.CF.Lor
