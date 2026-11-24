import YM.SU5.Selected.Twirl.Horizon
import YM.SU5.Selected.Twirl.Pearl
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Stencil (pulseNode pval)
open Rubric
open Afterglow Afterglow.Tapestry
attribute [local instance] opCStarAlgebra
-- narrow neutral algebra including products. Need separate ambient eval & comm proof. keep support. Compare Nation.
open Commission
namespace Mezz
set_option synthInstance.maxSize 26000
attribute [local instance] opCStarAlgebra
namespace Grant
open Sermon Tower.SlabMark
-- headline C combo. Coordinates count. Seam b at d'. All factors physically remain, also shifted (Steering). Elementary expression preserves explicit source. Cut-secants.
variable (A:Mezz)(K:Calibration){W:Window.Family} (F F': Sermon A K W) (e:A.Legate) (r:ℕ) (s:Finset A.Lot)(d:A.BlockDay)(b:Bool) (x y:ℂ)
local notation "P" F:max => pool A K F e s
local notation "D" F:max=> drain A K F e s
local notation "P₀" => quarry A K
local notation "P₁" => quay A K
local notation "A₀"=> stage_at A K F F' d.val
local notation "A₁"=> stage_at A K F F' (d.val+1)
local notation "ξ" F:max=> embrace A K e F s
local notation "Ω" F:max=> Liturgy A K e F s
local notation "₩" F:max=> Sermon.solitude A K e F
local notation "β"=> A.Broad
local notation "α"=> Prize K A.Broad
noncomputable def glaze : α:= x • (ξ A₀)+y • (ξ A₁)
noncomputable def icing (w:ℕ) (D₀:A.BlockDay): Buffered.Family K:= x • tripty A K A₀ e s D₀ b w+y • tripty A K A₁ e s D₀ b w -- not asserting still on U. Larger seam coverage? endpoints read exact. 
local notation "g"=> glaze A K F F' e s d x y
local notation "U₊" b:max f:max=> Liturgy A K e f s b
-- geometry auxiliary
include e
lemma glaze_mar : (g).val ∈ Marble K W A.Zumba (A.coast_b true) (A.coast_b false) A.Broad (10*s.card) (10*s.card) s.card:=
 (Marble K W A.Zumba (A.coast_b true) (A.coast_b false) A.Broad (10*s.card) (10*s.card) s.card).add_mem (Submodule.smul_mem _ x (knot_s A K e (A₀) s)) (Submodule.smul_mem _ y (knot_s A K e A₁ s))
noncomputable def coast_fadeY :α:= x • (Ω A₀) true+y • (Ω A₁) true
noncomputable def coast_fadeZ: α:=(Ω F) false
local notation "γ"=> coast_fadeY A K F F' e s d x y
local notation "Κ"=> coast_fadeZ A K F e s
-- kernel uses explicit `congrArg` helpers
private lemma mix_vs {a b: α}{S:Finset Cover}(t: luxury K a.val S)(u:luxury K b.val S): luxury K (x • a+y • b:α).val S:=by
 refine ⟨InTest.add (.smul x t.1) (.smul y u.1),grown _,?_⟩; change Tower.mirror K 0 0 (Tower.mirror K 1 0 (x • a.val+y • b.val))= -(x • a.val+y • b.val); rw [Tower.mirror_plus,Tower.mirror_plus,Tower.mirror_scale,Tower.mirror_scale,Tower.mirror_scale,Tower.mirror_scale,t.2.2,u.2.2,star_star,star_star]; simp; rw [add_comm] -- note rw may loop star order
lemma coast_presentation(v: Odd s.card): (g).val = (γ).val*(Κ).val ∧ Sermon.luxury K (γ).val (A.coast_b true) ∧ Sermon.luxury K (Κ).val (A.coast_b false):=by
 refine ⟨congrArg Subtype.val (?_ : g= γ * Κ), ?_, Liturgy_lux A K e _ _ _ v⟩ -- args
 · unfold glaze coast_fadeY coast_fadeZ; rw [merge,merge,add_mul, Algebra.smul_mul_assoc,Algebra.smul_mul_assoc, enroll A K A₀ F e s (b:=false) (fun i hi=>rfl), enroll A K A₁ F e s (b:=false) (fun i hi=>rfl)]
 exact mix_vs A K e x y (Liturgy_lux A K e _ _ _ v) (Liturgy_lux A K e _ _ _ v)

variable (D₀:A.BlockDay)
local notation "K₀" F:max=> pool A K F e s D₀ b
local notation "K₁" F:max=> drain A K F e s D₀ b
-- Major arm expression valid for ALL seams independent of phase; adjustment applies to left if d≤D and b allows inclusive; then right same.
private lemma steam_d (p:wanted A D₀ b d): K₁ A₀=K₁ A₁:=by
 unfold drain; exact congrArg₂ (·*·) (enroll _ _ _ _ e _ (fun i u=> offDay A K F F' i d (fun e=> (show ¬wanted A D₀ b i.1 from (mem_filter.mp u).2) (e.symm ▸ p)))) (enroll A K _ _ e _ (fun i u=>rfl))
private lemma steam_u (p:¬wanted A D₀ b d): K₀ A₀=K₀ A₁:=by
 unfold pool; exact congrArg₂ (·*·) (enroll _ _ _ _ e _ (fun i u=> offDay A K F F' i d (fun e=>p (e ▸ (show wanted A D₀ b i.1 from (mem_filter.mp u).2))))) (enroll A K _ _ e _ (fun i u=>rfl))
noncomputable def melt0 :α:= if wanted A D₀ b d then x • (K₀ A₀)+y • (K₀ A₁) else K₀ A₀
noncomputable def melt1 :α:= if wanted A D₀ b d then K₁ A₀ else x • (K₁ A₀)+y • (K₁ A₁)
local notation "L"=> melt0 A K F F' e s d b x y D₀
local notation "R"=> melt1 A K F F' e s d b x y D₀
lemma frosting : (g).val = (L).val*(R).val:=by
 refine congrArg Subtype.val (?_ : g=L*R); unfold glaze melt0 melt1; split_ifs with p p;
 · rw [rejoin A K A₀ e s D₀ b, rejoin A K A₁ e s D₀ b, ←steam_d A K F F' e s d b D₀ p,add_mul,Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
 rw [rejoin A K A₀ e s D₀ b,rejoin A K A₁ e s D₀ b, ←steam_u A K F F' e s d b D₀ p,mul_add,Algebra.mul_smul_comm,Algebra.mul_smul_comm]
lemma frosted (w:ℕ) : icing A K F F' e s d b x y w D₀= (L).val* relocate K 3 w (R).val:=by
 let R':= relocate K 3 w; unfold icing tripty melt0 melt1; split_ifs with p; · rw [←steam_d A K F F' e s d b D₀ p, ←Algebra.smul_mul_assoc, ←Algebra.smul_mul_assoc,← add_mul]; rfl -- extra parens
 rw [←steam_u A K F F' e s d b D₀ p]; let U:=K₀ A₀; let a:= K₁ A₀; let e:=K₁ A₁; change x • (U.val* R' a.val)+ y • (U.val* R' e.val)= U.val* R' (x • a.val+y • e.val); unfold R' relocate; rw [Tower.chime_plus,Tower.chime_scale,Tower.chime_scale,mul_add,Algebra.mul_smul_comm,Algebra.mul_smul_comm]
variable (η:addgap K ≤ A.ℓ.val)
include η
lemma beam_born : InTest K false (P₀ D₀ b) false (L).val ∧ InTest K false (P₁ D₀ b) false (R).val :=by
 have hv₀:= quarry_x A K A₀ e s D₀ b η; have hk₀:=quarry_x A K A₁ e s D₀ b η; have hv₁:=quay_x A K A₀ e s D₀ b η; have hk₁:=quay_x A K A₁ e s D₀ b η; unfold melt0 melt1; split_ifs; exact ⟨InTest.add (hv₀.smul x) (hk₀.smul y),hv₁⟩; exact ⟨hv₀,InTest.add (hv₁.smul x) (hk₁.smul y)⟩ -- angle `Scope`
local notation "S₀" w:max => melt0 A K F F' e s d false x y w
local notation "S₁" w:max => melt1 A K F F' e s d false x y w
-- for D₀ with odd slice, at b=false time arms still centered EVEN when d appended. prove from Pent.Seaway manually if `stagD` defeq via desired with comparisons & omit Bool meet.
lemma tips (p: Odd (regCard A s D₀)) : luxury K (S₀ D₀).val (P₀ D₀ false) ∧ luxury K (S₁ D₀).val (P₁ D₀ false):=by
 have ht(F:Sermon A K W) : luxury K (pool A K F e s D₀ false).val (P₀ D₀ false)∧ luxury K (drain A K F e s D₀ false).val (P₁ D₀ false):= (seaWay A K e F s D₀ η p).2.2
 unfold melt0 melt1; split_ifs; · exact ⟨mix_vs A K e x y (ht A₀).1 (ht A₁).1,(ht A₀).2⟩
 exact ⟨(ht A₀).1, mix_vs A K e x y (ht A₀).2 (ht A₁).2⟩
lemma prestige_time(v: Odd s.card) : ∃ (d₀:A.BlockDay), Odd (regCard A s d₀)∧ luxury K (S₀ d₀).val (P₀ d₀ false) ∧ luxury K (S₁ d₀).val (P₁ d₀ false) :=by obtain ⟨d',r⟩:= Sermon.pension A s v; exact ⟨d',r,tips _ _ _ _ e s d x y _ η r⟩
end Grant
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Grant
#print axioms coast_presentation
#print axioms frosting
#print axioms frosted
#print axioms tips
#print axioms prestige_time
#print axioms glaze_mar
#print axioms beam_born
