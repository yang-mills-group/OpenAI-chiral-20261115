import YM.SU5.Selected.Cor.Scrolls
import YM.CF.Brace.Fish
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
open Payroll Mezz.Caste
set_option synthInstance.maxSize 24000
variable {N:Side}
section relief
lemma Rightful.pushU {x y: Pane N}{S T:Finset (Seat N)}{γ δ:ℝ}(p: Rightful S x y γ) (h:T⊆ S)(t:γ≤δ) : Rightful T x y δ:= by
 intro i he; obtain ⟨a,b⟩:=(mem_filter.mp he).2; exact (p _ (mem_filter.mpr ⟨mem_univ _,h a,h b⟩)).trans t
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
namespace Mezz
open Mint Numeric
variable {T:Type}[Fintype T][DecidableEq T]
variable (P: Mezz) (A:Society T) (X Z: Coast → Wq P.marks)(V:ℝ) {M:Tulip.Male}{ℓ t:ℕ}
local notation "R" => billR V
local notation "ε"=> Tender.tightH P.D (billR V)
local notation "η"=> Tender.levyH P.D (billR V)
variable (c:Caste (N:=N) P M V (Tender.tightH P.D (billR V)) ℓ X Z)
local notation "S"=> park N P.Broad
local notation "B"=> park N P.Core
local notation "K" a:max => (1 - sp false 4 M a)
local notation "K₀" => (1 - sp false 4 M (1:Pane N))
local notation "A'" => P.dart A N X
local notation "V'" => P.dart A N Z
local notation "↑X" => design (Ro N) (A') (lowerP V)
local notation "↑Z" => design (Ro N) (V') (Caste.upperP V)
local notation "↓X" => Caste.accept P A true X Z V
local notation "↓Z" => Caste.fillV P A X Z V
-- environment supports rentable threshold (γ from Winter); choose another ρ smaller), fees support only at t. 
variable {ρ γ δ:ℝ}
private def prage : (Tender.Acres P.G P.D P.u.val P.q.val) ≃ (P.Lot) := Equiv.refl _ -- lemma should def
lemma flowersK : Fintype.card P.Lot>0:= by
 rw [show Fintype.card P.Lot= _ from Tender.power_acre P.G P.D P.u.val P.q.val]; unfold Tender.powerK; positivity -- structure congr
noncomputable def threshD (V:ℝ):ℝ:= (Tender.tightH P.D (billR V))/( ((2*Fintype.card P.Lot:ℕ):ℝ)*(8*P.beams)*billR V )
lemma rowS (e:1≤V) :0<threshD P V:= by
 apply div_pos (rankE P e); have hp:=flowersK P; have ht:0<P.beams:=Nat.mul_pos (by omega) P.geo_w; have hz:0 < R:= by linarith [bigV e]; -- no shadow
 positivity
variable (cV:1≤V) (w:Winter 4 δ N γ t (Tender.tightH P.D (billR V)))
-- replace notation `ε` binder
include c cV w
lemma visit_now (u:t ≤ P.W)(d:0≤δ)(a:Pane N)(h:Guard a δ)(p:Rightful S a 1 (min γ (threshD P V))) (l:0<γ): Payroll (K a) (↓X a) (↓Z a) (1/2) (R/2) (η/4) (η/2):=by
 let v:= min γ (threshD P V); have hv:0<v:= lt_min l (rowS P V cV); have hK:= bigV cV; have hp:= rankE P cV; let Λ:= ((2*Fintype.card P.Lot:ℕ):ℝ); have hL:0<Λ:= by unfold Λ; have L:= flowersK P; positivity -- ℓ
 have hG(b:Bool): ‖accept P A b X Z V a - accept P A b X Z V (1:Pane N)‖ ≤ ε:=by
    have hx:= Caste.salary P A b X Z V c cV hv.le a p; apply hx.trans; have ht: 0<P.beams:= Nat.mul_pos (by omega) P.geo_w
    have hz: v*(Λ*(8*P.beams)* R) ≤ ε := (le_div_iff₀ (show 0 < (Λ*(8*P.beams)*R:ℝ) from by have hQ:0<R:=(by linarith); positivity)).1 (min_le_right ..)
    change Λ*(sizeW V b *2*((8*P.beams*v)*V)) ≤ ε; apply le_trans _ hz; nlinarith only [mul_le_mul_of_nonneg_left (Numeric.limitPole cV b) (show (0:ℝ)≤ Λ*(8*P.beams * v) by positivity)]
 have eX: ‖↑X-(↓X a)‖≤ ε:= by rw [norm_sub_rev,←accept_low]; exact hG true
 have eV: ‖↑Z-(↓Z a)‖≤ ε:= by rw [norm_sub_rev, fill_less P A X Z V c]; exact hG false
 let F:= ↓Z a; have hF: Vo B *F=F:= sera _ _ _ _ _ c a
 have e:(Lattice.halo t B) ⊆ S :=by unfold Broad Core; rw [park_plant,park_plant]; apply park_halo; unfold vol beams; omega
 have hu:= winter_change (M:=M) a w h d (Rightful.pushU p e (min_le_left ..));
 apply pass_grad K₀ (K a) ↑X ↑Z _ _ ((sememes _ _ c cV).mono _ _ _ _ _ _ _ (rentC_L cV) (rentC_H cV) le_rfl (show ε*tollS V≤_ by nlinarith [seat_t P cV])) hp.le hK (lowE P cV) (rank_toll P cV) eV eX -- tune
 · exact (raft true c.spinC).norm_le _ -- `$hand` wraps
 rw (occs:=.pos [1]) [←show Vo B*F=↓Z a from hF]; rw [←Matrix.mul_assoc]; exact charge_mul hu le_rfl
-- notation binders fixed. ro etc. `association`.
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms visit_now
