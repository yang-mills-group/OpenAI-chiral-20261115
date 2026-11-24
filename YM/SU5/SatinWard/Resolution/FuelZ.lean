import YM.SU5.SatinWard.Resolution.BeyondSea
import YM.CF.Scree.Locus
/-! # Stove identity without changing billing. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Laurent Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial Vault
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Tap MeasureTheory ProbabilityTheory Scree Skye Filter Precision Tree Push.SectorMeasure
local notation "V𝕊"=> UNI SU.Slot
variable {g:V𝕊}
universe u
lemma across_at {α:Type u}[DecidableEq α][Fintype α](g:V𝕊)(x:α× Slot): acts (across α g).val (basisKet x) = ∑ i:Slot, g.val i x.2 • basisKet (x.1,i):=by
 apply PiLp.ext; intro j
 rcases x with ⟨y,i⟩; rcases j with ⟨z,b⟩; simp only [basis_act,WithLp.ofLp_sum,Finset.sum_apply,basis_apply,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,mul_ite,mul_one,mul_zero,Prod.mk.injEq]; change (1:Op α) z y * g.val b i = _; by_cases h:z=y<;>(first | (solve | simp [h]) | (subst z; simp)) -- α maybe instance confusion

section Belt
variable {N P: Side}(G:Ratio N P)
local notation "R"=> reefS G true
local notation "U"=>singlet N
local notation "V"=>ceremony G
local notation "p✲"=> patchQ G
variable (g)
lemma cloth_rose (x: Wave (Single P)): cartsL (switchG G).symm (performance (singlet P) g x)=performance (ceremony G) g (cartsL (switchG G).symm x):=by
 unfold performance cartsL; let s:= (singlet P g).val; let F:Phys P:=x
 change hoist _ _ (acts (quant s) x)=acts (quant _) _
 rw [freezes _ _ (shelfG _) s x, flexL (switchG G).symm]; change acts (quant (foot G s)) _=_; rw [show foot G s=_ from foot_rose G g]
lemma ensemble (u:Single N): coat (patchQ G) (acts (singlet N g).val (basisKet u))=acts (ceremony G g).val (basisKet (patchQ G u)):=by
 rw [show acts _ (basisKet u)=_ from across_at g u, show acts _ _=_ from across_at g (patchQ G u),map_sum]; simp_rw [map_smul, basis_shell]; rfl
variable {g}(q:Concert g)
include q
lemma scroll_payment (x:Wave (Single N)): hoist p✲ R (performance U g x)=performance V g (hoist p✲ R x):=by
 have he(t:Finset (Single N)): hoist p✲ R (performance U g (basisKet t))=performance V g (hoist p✲ R (basisKet t)):=by
    induction t using Finset.induction_on with
    | empty=> rw [hoops,knot_empty,roseReef G q]; unfold performance; change hoist p✲ R (acts (quant _) (vacuum _))= _; rw [quant_vac]; change hoist p✲ R (basisKet ∅)=_; rw [hoops,knot_empty]
    | @insert i t v ih=>
      rw [create_basis_is i t v,map_smul,map_smul,map_smul,map_smul,hoist_put]; congr 1; unfold performance
      rw [← create_put i,← create_put (patchQ G i),Fock.swivel,Fock.swivel (quantU (ceremony G g)),twist_create,twist_create, hoist_c _ _ (reefS_deck ..),ensemble]; unfold performance at ih; rw [ih]
 nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul,he]
lemma pail_rose (x: Wave (Iota G)): pailL p✲ R (performance V g x)=performance U g (pailL p✲ R x):=by
 apply PiLp.ext; intro i; rw [←basis_inner,←basis_inner,pails _ _ (reefS_deck ..),←act_inner,←act_inner]
 have hx:= scroll_payment G q.star (basisKet i)
 change _ = inner ℂ (acts (star (quantU _).val) _) (pailL p✲ R x)
 rw [pails _ _ (reefS_deck ..)]; congr 1
 have hv:∀ (I:Type) [Fintype I] [LinearOrder I](X:V𝕊→* UNI I), star (quantU (X g)).val=(quantU (X (star g))).val:=by intros I _ _ X; rw [show X (star g)= star (X g) from map_inv X g, quantU_star]; rfl
 rw [hv _ U,hv _ V]; exact hx.symm
lemma hearth_rose (k:Odd G.count.val)(j:ℕ)(M:Male)(x:Nom N P)(w:Wave (Iota G)): fire (Thread j) G M (unionP x) (performance V g w)=performance U g (fire (Thread j) G M (unionP x) w):=by
 let Z:= ticketT (Thread j) true M G (unionP x); have he: effectK Z (performance V g w)=performance V g (effectK Z w):=by
    unfold effectK performance; rw [←act_mul,← act_mul]; apply congrArg (fun A:FC (Iota G)=>acts A w); exact ((still_U.mp ( (quant_twist _ Z).symm.trans (congrArg quant (ticket_stock G k g q.gate j true M x)))).eq).symm
 unfold fire; rw [show effectK _ _=_ from he,pail_rose G q,map_smul]
end Belt

section Pantry
variable {n:Side}(q:Concert g)
variable (A:Op Slot)
include q
lemma scale_visit (x:Phys n): scaleZ (twist g A) (performance (singlet n) g x)=performance (singlet n) g (scaleZ A x):=by
 let U:=singlet n g; let v:=quantU U; let F(B:Op Slot):= exp (-(plankP n B)); have hU:quant (F (twist g A))=twist v (quant (F A)):=by unfold F plankP; rw [←roseHead, ←map_neg, ←breeze_exp,quant_twist] -- maybe reverse breeze
 let w:=mateK n
 have ht:skyGlow w (F (twist g A)) w=skyGlow w (F A) w:=by
    change inner ℂ w (acts (quant _) w)=inner ℂ w _; rw [hU]; nth_rw 1 2 [←(show acts v.val w=w from roseMate n q)]; rw [← Fock.swivel,act_unit_inner]
 change (skyGlow w (F (twist g A)) w)⁻¹ • acts (quant (F _)) (acts v.val x)= acts v.val ((skyGlow w (F A) w)⁻¹ • _)
 rw [ht,hU,← Fock.swivel,map_smul]

lemma performance_summ {x y:Phys n} : dist (performance (singlet n) g x) (performance (singlet n) g y)=dist x y:=by rw [dist_eq_norm,dist_eq_norm,←map_sub,performance,act_unit_norm]
end Pantry
section
variable {m C B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
variable (P:Grasp Y B e)
variable (A:Loom (mid m B))(R:GramM (mid C B))(A':Loom (mid C B))(G:Ratio (mid m B) (mid C B))
variable (S:RG.StepData (More (mid m B)) (More (mid C B)))(r:Chi)(d:ℝ)
variable (Q:Op Slot)
local notation "S_U"=> performance (singlet (mid m B)) g
local notation "R'" => Scree.stove P A R A' G S r d
include g
variable (q:Concert g)
include q
lemma stove_rose (h:Odd G.count.val)(v:∀ᵐ i:Orbit (mid C B) ∂city (mid C B), performance (singlet (mid C B)) g (denZ R P A' i) = denZ R P A' i) (x:Orbit (mid m B)):
 R' (twist g Q) x= S_U (R' Q x):=by
 unfold Scree.stove; rw [← ContinuousLinearMap.integral_comp_comm' (performance (singlet (mid m B)) g) (K:=1) ((Isometry.of_dist_eq fun i j=> performance_summ q (n:=mid m B) (x:=i) (y:=j)).antilipschitz)]
 apply MeasureTheory.integral_congr_ae; filter_upwards [v] with i hi
 have hh(F:Forest (ratio G)): carrier P A R A' G S r d (twist g Q) F x i=S_U (carrier P A R A' G S r d Q F x i):=by
    unfold carrier; rw [show S_U (_ • _) =_ from (map_smul ( (performance (singlet (mid m B)) g).restrictScalars ℝ) (S.density R.beta i.1 x.1) _)]
    nth_rw 1 [←hi]; rw [cloth_rose g G,hearth_rose G q h,scale_visit q]; rfl
 unfold integrated; rw [show S_U (_ • _) =_ from map_smul ((performance (singlet (mid m B)) g).restrictScalars ℝ) ((Fintype.card (Forest (ratio G)):ℝ)⁻¹) _]; simp_rw [hh,map_sum]; rfl -- last CLM eq remove

end
end YM.CF.Mezzo
