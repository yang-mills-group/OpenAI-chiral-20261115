import YM.CF.Levier.Dent
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
variable (S:Seal (Site (More P)))(W:Toll (Iota G))(F:Raw (cro G e) (Iota G))
local notation "π"=>paceU (castX k⁻¹) G
variable (C:Seal (Site (More P))→Toll (Iota G))(u:ℕ)(p d r:ℝ)
def wheelS(s:Seal (Site (More P))):Toll (Iota G):= chase G k (C (toRoar G k⁻¹ s))
def weaveS :Seal (Site (More P)) ≃ Seal (Site (More P)):= {toFun:=toRoar G k,invFun:=toRoar G k⁻¹,left_inv:=fun S=>by rw [swept,inv_mul_cancel,sw_i], right_inv:=fun S=>by rw [swept,mul_inv_cancel,sw_i]}
local notation "Ω"=>weaveS G k
lemma coinS(S:Seal (Site (More P))): (weaveS G k S).card=S.card:=card_image_of_injective _ (Shape.anon_b (Shape.broad G (castX k))).1
lemma soldX(i j:Hand G)(x y:QuiltF): saleM d (wheelS G k C) (beamH G i x) (beamH G j y)=∑ p:QuiltF,∑ q:QuiltF,‖scene G k i j x y p q‖*saleM d C (beamH G (π i) p) (beamH G (π j) q):=by
 let a:= Ω; have hx(Z:Seal (Site (More P))): toRoar G k⁻¹ (a Z)=Z:= a.symm_apply_apply _
 unfold wheelS chase saleM; simp only [beamH,Equiv.apply_symm_apply]; conv_lhs=> rw [←Equiv.sum_comp a]
 simp_rw [hx,Branch.rent,show ∀ S:Seal (Site (More P)),(a S).card=S.card from coinS G k,mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]; simp_rw [mul_left_comm (Real.exp _)]; -- tune
lemma scene_n(i j:Hand G)(x y p q):‖scene G k i j x y p q‖ ≤1:=by
 unfold scene; dsimp only; rw [norm_mul,norm_star]; apply mul_le_one₀ <;> first| exact (norm_entry (milU _ _ _ _).val _ _).trans (CStarRing.norm_of_mem_unitary (milU ..).property).le | positivity
include h
abbrev population :ℝ:= (Fintype.card QuiltF:ℝ)^2
lemma spoke (v:incline (hall G e) u p (fun _=>r) d C)(g:∀ S i j,0≤ C S i j)(hk:0≤p): incline (hall G e) u p (fun _=>population*r) d (wheelS G k C):=by
 intro i; obtain ⟨⟨i,x⟩,rfl⟩:=(abbe G).symm.surjective i
 let R(i j:Iota G):=(1+p*(hall G e).F.span ((hall G e).home i) ((hall G e).home j))^u
 let f(i j:Hand G)(x y:QuiltF):= saleM d C (beamH G i x) (beamH G j y); let H(j:Hand G):=(1+p*(terr _).span (meetH G true i) (meetH G true j))^u
 have ht(j:Hand G)(x y:QuiltF):R (beamH G i x) (beamH G j y)=H j:=rfl
 have hp(j:Hand G)(x y:QuiltF):R (beamH G (π i) x) (beamH G (π j) y) = H j:=by change (1+p*((terr _).span (meetH G true (π i)) (meetH G true (π j))))^u=_; simp [meet_x G h,H,terr,Shape.anon,affine]
 have he(p':QuiltF):∑ j:Hand G,∑ z: QuiltF,H j*f (π i) (π j) p' z ≤r:=by
    have hv:=v (beamH G (π i) p'); change ∑ j,R (beamH G (π i) p') j*_≤_ at hv; rw [←Equiv.sum_comp (abbe G).symm,Fintype.sum_prod_type,← Equiv.sum_comp π] at hv; unfold beamH at hp; simp_rw [hp] at hv; exact hv
 let X(j:Hand G):= H j* ∑ z: QuiltF,∑ w:QuiltF, f (π i) (π j) z w; change ∑ j,R _ j*_≤_; rw [←Equiv.sum_comp (abbe G).symm,Fintype.sum_prod_type]; unfold beamH at ht; simp_rw [ht]
 apply (sum_le_sum (g:= fun j=>∑ _y:QuiltF, X j) _).trans; swap; · intro j _; apply sum_le_sum; intro y _; apply mul_le_mul_of_nonneg_left _ (by unfold H; positivity); rw [show saleM _ _ _ _= _ from soldX G k C d i j x y]; exact sum_le_sum fun z _=> sum_le_sum fun w _=> mul_le_of_le_one_left (sale_nn g ..) (scene_n ..)
 rw [sum_comm]; let Q:= Fintype.card QuiltF; have hx(i:QuiltF): ∑ j:Hand G, X j ≤ ∑ _y:QuiltF,r:=by unfold X; simp_rw [mul_sum]; rw [sum_comm]; exact sum_le_sum fun i _=>he i -- tune
 exact (sum_le_sum (s:=univ) (fun y _=>hx y)).trans_eq (by simp [population]; ring)
end YM.CF.Levier
