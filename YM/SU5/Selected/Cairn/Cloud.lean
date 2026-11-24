import YM.SU5.Selected.Cairn.Violet
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
section relief
private lemma winter_change {n:Side}{γ δ ε:ℝ}{w:ℕ} (X:Pane n){M:Tulip.Male}{t:Finset (Seat n)}(p:Winter 4 δ n γ w ε)(h:Guard X δ)(hv:0≤δ)(l:Rightful (Lattice.halo w t) X 1 γ):
    ‖((1-spar 4 M X) - (1- spar 4 M (1:Pane n)))*Vo t‖≤ε:=by
 let A:= (1-spar 4 M X) - (1- spar 4 M (1:Pane n)); let T:= t; change ‖A*Vo t‖≤ε; apply p.plank true M t _ _ h (guard0 hv) l; intro i k; by_cases h:node k.1.1∈ T; · right; refine ⟨h,?_⟩; rw [Vo,cutM, Matrix.mul_diagonal,if_pos ((modes_at ..).2 h),mul_one]; exact le_rfl
 left; unfold Vo cutM; rw [Matrix.mul_diagonal,if_neg (mt (modes_at ..|>.1) h),mul_zero]
-- estimate prior to mixing for width in many copies. target ν/10,  etc. simplicity generous. 
private theorem pass_grad {t n:Type}[Fintype n][DecidableEq n][Fintype t][DecidableEq t]
   (F G: Op n)(H V X Y: WRect n t){ε R v:ℝ}(p:Payroll F H V (1/4) (R/4) ε (R*ε))(t':0 ≤ ε)(vR:100 ≤ R)(e:ε≤1/100)(q:(100*R)*ε ≤ v)(k:‖V-Y‖≤ε)(x:‖H-X‖≤ε)(p':‖F‖≤1)(a:‖(G-F)*Y‖≤ ε*‖Y‖) : Payroll G X Y (1/2) (R/2) (v/4) (v/2):=by
 have ht: ‖X‖≤ 1/2:=by have he:=p.tribute; linarith [norm_sub_rev X H,norm_le_norm_sub_add X H] -- norm_rev syntax
 have hv: ‖Y‖≤ R/2:=by linarith [p.cost,norm_sub_rev Y V,norm_le_norm_sub_add Y V]
 have hX: ‖X-H‖≤ε:= (norm_sub_rev ..).trans_le x; have hY: ‖Y-V‖≤ ε:= (norm_sub_rev ..).trans_le k
 constructor
 · exact ht
 · exact hv
 · rw [show Xᴴ*Y-1=(Hᴴ*V-1)+(X-H)ᴴ*V+Xᴴ*(Y-V) from (by rw [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub]; abel)]; refine ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add p.gram ((charge_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le hX) p.cost)))) (charge_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le ht) hY))).trans ?_; nlinarith
 rw [show G*Y=( (G-F)* Y)+F*(Y-V)+F*V from (by rw [Matrix.sub_mul,Matrix.mul_sub]; abel)]; refine ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (a.trans (mul_le_mul_of_nonneg_left hv t')) (charge_mul p' hY))) p.seat)).trans ?_; nlinarith

end relief
namespace Giant
variable (A:Giant) {N:Side} (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b:Bool)
open Mint Silks
local notation "S" => park N A.Broad
local notation "K" => park N A.Core
local notation "W" => A.bW
local notation "Φ" u:max => wrap (More N) u
local notation "α"=> cutM (Tset N)
local notation "χ" A:max=> (A).debt.val
abbrev pink := Attic.paidX A.rank (χ A)
abbrev sampleW:= Attic.billX A.rank (χ A)
abbrev snowLine:= Cuve.footW (χ A) (Attic.tideU A.rank+3)
structure Clear(y d:ℕ)(C:ℝ): Prop where
 excess : paidX y d ≤1/100
 safe : 100*C*paidX y d≤billX y d
lemma clearout (y:ℕ)(C:ℝ) (h:0≤ C): ∀ᶠ d:ℕ in atTop,Clear y d C:=by
 filter_upwards [eventually_gt_atTop 0, (twilight (k:=tideU y) (by unfold tideU; omega)).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/100)), degree_bill 1 (100*C) 1 (flareU y+1) (tideU y) (by norm_num) (by unfold tideU; omega)] with i p t a; refine ⟨t,?_⟩; unfold billX; rw [one_mul, mul_one] at a; exact le_trans (mul_le_mul_of_nonneg_left (benefits _ p (show Attic.flareU y+1+1≤ Attic.tideU y from (by unfold tideU; omega))) (show 0≤ 100*C by positivity)) a
variable {M:Tulip.Male}{δ γ C:ℝ}(g:Pride A Z C δ γ M N) (e:A.tokenS<N.val) (u:1≤ C)
local notation "ζ"=> A.pink
local notation "η"=> A.sampleW
local notation "T₀"=> coastCap C
variable (c:Clear A.rank A.debt.val (coastCap C))(w':Winter 4 δ N γ A.debt.val A.snowLine)
 (U:Pane N)(r:Guard U δ) -- placeholder
local notation "L"=>A.LHS P b C
local notation "R"=>A.RES Z P M C
-- threshold since Prep coordinate. 
def bath :ℝ:= A.pink/(8*W*coastCap C)
lemma pink_hot: 0<ζ:= (Attic.foot_lead A.debt.property _).1
lemma flake : snowLine A ≤ ζ:= Attic.benefits _ A.debt.property (by omega)
include u
lemma bath_ps : 0< A.bath (C:=C):=by unfold bath; have h:=A.pink_hot; have hv:=A.height; have ht:0<T₀:=(by linarith [capCost C u]); positivity
variable (v:0<γ)
include e v g u
private lemma bather {q:Type}[Fintype q][DecidableEq q] (s:Cover)(t:s∈ A.Broad)(G:WRect (Single N) q)(x:Contained (modesIn N S) G)(y:‖G‖≤ T₀)(i:Rightful S U 1 (min γ (A.bath (C:=C)))): ‖dressedK (Φ s) G U-G‖≤ ζ:=by
 let B:= A.bath (C:=C); let z:=min γ B; have he:0 ≤ z:= le_min v.le (A.bath_ps u).le; refine (Silks.tally S G _ _ x (by positivity) (fun k (p:k∈S) => stampsL W t (subset_refl _) (A.widest e) i he k p)).trans ?_ -- positivity before z maybe
 change 8*W*z* ‖G‖≤ ζ; have hp:0<T₀:=(by linarith [capCost C u]); have h₀:0<W:=A.height; refine le_trans (mul_le_mul_of_nonneg_left y (by positivity)) ?_; apply le_trans _ ((le_div_iff₀ (by positivity: (0:ℝ)<8*W*T₀)).mp (show z≤ B from min_le_right ..)); exact le_of_eq (by ring)
include c w' r
local notation "V₀" u:max=>1-spar 4 M u
lemma glacier (p:0≤δ)(t:Rightful S U 1 (min γ (A.bath (C:=C)))):
    Payroll (V₀ U) (A.filmL P b C U) (A.filmV Z P C M U) (1/2) (T₀/2) (η/4) (η/2):=by
 let V:= A.filmV Z P C M U; let Y:= A.filmL P b C U
 have he:= A.pays Z P b u g -- arg order
 have hx:=capCost C u; have ht: A.ascX ⊆ A.Broad := A.nudge.trans (A.portS.trans A.portT); have hvA : ‖Y-A.LHS P b C‖≤ ζ:= bather A Z g e u U v _ (ht (A.anchor_here b)) _ (((A.shore_x P b).grows (modes_monotone (image_subset_image ht))).smul _) (he.tribute.trans (by linarith)) t
 have hv : ‖V-A.RES Z P M C‖≤ ζ:= bather A Z g e u U v _ (((A.nut.trans A.portS).trans A.portT) A.anchor_dawn) _ (((A.horns Z P).grows (modes_monotone (image_subset_image A.portT))).smul _) (he.cost.trans (by linarith)) t
 refine pass_grad (V₀ (1:Pane N)) (V₀ U) (L) R Y V he A.pink_hot.le hx c.excess c.safe ((norm_sub_rev ..).trans_le hv) ((norm_sub_rev ..).trans_le hvA) (g.stars.one_sub.norm_le _) ?_
 let F:= (V₀ U)-(V₀ (1:Pane N)); have hu:=winter_change (M:=M) U w' r p (Rightful.pushU t A.riskC (min_le_left ..)); change ‖F* V‖≤ ζ*‖V‖; rw (occs:=.pos [1]) [← show Vo K * V=V from floraH ..]; rw [←Matrix.mul_assoc]; exact charge_mul (hu.trans A.flake) le_rfl
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms clearout
#print axioms glacier
#print axioms bather
#check @bather
