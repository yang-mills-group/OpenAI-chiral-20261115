import YM.CF.BPress.Spin.Touches
import GaugeFieldConstruction.Axe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt

namespace SliceRoof
variable {N:Side}(U:Pane N) {e d a b t:ℝ}
local notation "JP" => (Single N)
open YM.CF.BPress.Spin (sphereRate OrbRate invitation)
section Estimate
variable {H:BeatL N}{F:Elm N Unit d a b}
-- use actual conditional configuration. Preserve short terms before changing T.
lemma variation_clip (h:0≤ t)(p:0<d) (A B:Pane N)(u:Guard A d)(v:Guard B d) (S:Support (More N))(i j:JP)(w:BPress.chord.Close A B S t):
 ‖ivory F p A u S i j-ivory F p B v S i j‖ ≤ F.W S i j*(sphereRate*(4*S.card*t)/d):=by
 let X:= (F.coat S|>.1 ())
 apply (X.expo i j|>.variation (light d A p u) (light d B p v)).trans (mul_le_mul_of_nonneg_left _ (X.nonn i j)); change Tulip.fare S _ _ / |d| ≤ _; rw [abs_of_pos p]; apply div_le_div_of_nonneg_right _ p.le; exact (BPress.Spin.invitation.forum_compare BPress.Spin.sphereRate_cost).trans (mul_le_mul_of_nonneg_left (BPress.Spin.invitation.size h w) (BPress.Spin.sphereRate_cost.positive.le))
lemma seat_rent (p:0<d)(U:Pane N)(h:Guard U d) (V:Skye.Seat N → SU.E) -- rename
    (S:Support (More N)): ivory F p (Lattice.gauge V U) (h.cov V) S= twist (tradew N V) (ivory F p U h S):=by
 let W:=light _ U p h; let G:=forum N d; rw [twist_formula]; have he:= ((F.coat S|>.1 ()).frame.frame V W); change F.F S () (G.drive V W)=_ at he
 exact (congrArg (F.F S ()) (show (light _ _ _ _)=G.drive V W from Subtype.ext (profile_g ..))).trans he
lemma steady (p: NearL F (fun _=>H)) (u:0<d)(g:Guard U d): H (Tulip.profile U)=∑ S:Support (More N), ivory F u U g S:= p () (light d U u g) _ g rfl

def massSite {ι:Type*}[Fintype ι](P:Op ι):ℝ:= ∑ i:ι,∑ j:ι,‖P i j‖ -- [DecEq?]
def payFull {ι:Type*}[Fintype ι](P:Op ι) (C:ℝ):Prop:= (∀ i,∑ j:ι, ‖P i j‖≤ C)∧ ∀ j,∑ i:ι, ‖P i j‖ ≤ C
lemma payFull_real (u:0 < d)(g:0<a) (p:NearL F (fun _=>H)) (x:Pane N)(h:Guard x d): payFull (H (Tulip.profile x)) b:=by
 let A:= H (Tulip.profile x); have ht (i j:JP): ‖A i j‖≤ saleM a F.W i j:=by
    unfold A; rw [steady x p u h,Matrix.sum_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro k _; let e:= (F.coat k|>.1 ())
    exact (e.expo i j|>.bounded _).trans (le_mul_of_one_le_left (e.nonn i j) (rent_one g.le _))
 exact ⟨fun i=> (sum_le_sum fun j _=>ht i j).trans (F.bank.rows i),fun i=>(sum_le_sum fun j _=>ht j i).trans (F.bank.cols i)⟩
-- tax of kernel on seat with Tool.Safe neighbourhood around node. second Pane~first and cut rotated using shape proof later. Pink uses only real gauges
abbrev lipCharge (a C d v:ℝ)(j:ℕ):= C*(sphereRate*(4*j*v)/d + 2*Real.exp (-(a*j)))
abbrev bayS(n:Side)(x:Site n)(m:ℕ): Support n:= Branch.bay (terr n) x m
lemma touch_column (u:0<d)(g:0<a)(p:NearL F (fun _=>H))(A B:Pane N)(h:Guard A d)(e:Guard B d) (v:ℝ)(hp:0≤v)(i:JP)(m:ℕ)(k:BPress.chord.Close A B (bayS _ (node i.1.1) m) v): ∑ j:JP, ‖(H (Tulip.profile A)-H (Tulip.profile B)) i j‖ ≤ lipCharge a b d v m :=by
 let V:= H (Tulip.profile A); let W:= H (Tulip.profile B); let L:=light d A u h; let M:=light d B u e
 let C:=sphereRate*(4*m*v)/d; let R:= Real.exp (-(a*m)); have hc0 : 0≤ C:=by unfold C; have ht:=BPress.Spin.sphereRate_cost.positive; positivity; -- tune
 have hr:0≤2*R:=mul_nonneg (by norm_num) (Real.exp_pos _).le
 have he(j:JP):‖V i j-W i j‖≤ (C+2*R)* saleM a F.W i j:=by
    let v'(i:Lantern N d)(S:Support (More N)):=F.F S () i;
    rw [show V=∑ S, v' L S from steady A p u h, show W=∑ S,v' M S from steady B p u e,Matrix.sum_apply,Matrix.sum_apply, ←sum_sub_distrib]; unfold saleM; rw [mul_sum]
    apply (norm_sum_le ..).trans; apply sum_le_sum; intro s _; let P':= (F.coat s|>.1 ()); let σ:= F.W s i j; let D:=rent a s
    have ht: ‖v' L s i j-v' M s i j‖≤σ+σ:=(norm_sub_le ..).trans (add_le_add (P'.expo i j|>.bounded L) (P'.expo i j|>.bounded M)); change _ ≤ (C+2*R)*(D*σ); have hs:0≤σ:=P'.nonn i j
    by_cases hh:σ=0; · simpa [hh] using ht
    rcases le_or_gt s.card m with hl|hl
    · have hh:= P'.expo i j|>.triggered hh; have he:s⊆bayS _ (node i.1.1) m:= fun z x=>mem_filter.mpr ⟨mem_univ _,(Nat.le_of_lt (hh.1.lim _ hh.2.1 _ x)).trans hl⟩
      apply (variation_clip hp u A B h e s i j (BPress.chord.Close.smaller A B he k)|>.trans ?_)
      calc
       _ ≤ σ*C:=by apply mul_le_mul_of_nonneg_left _ hs; unfold C; have h:= BPress.Spin.sphereRate_cost.positive; gcongr
       _ ≤ _:=by rw [mul_comm σ]; apply mul_le_mul (le_add_of_nonneg_right hr) (le_mul_of_one_le_left hs (rent_one g.le _)) hs (add_nonneg hc0 hr)
    apply ht.trans
    have huv: 1 ≤ R*D:=by unfold R D Branch.rent; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hl.le) g.le]
    rw [←mul_assoc,←two_mul]; apply mul_le_mul_of_nonneg_right _ hs; nlinarith only [huv,mul_nonneg hc0 (show 0≤D from (rent_pos ..).le)]
 refine le_trans (sum_le_sum (fun j _=>he j)) ?_; rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (F.bank.rows _) (add_nonneg hc0 hr)).trans_eq (mul_comm _ _)
end Estimate
end SliceRoof
end YM.CF.Sour
end
