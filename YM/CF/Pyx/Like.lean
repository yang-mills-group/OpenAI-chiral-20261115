import YM.CF.Pyx.Fenn
import YM.Branch.Covariant
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (G:Ratio n f)(g:Seat f→SU.E)
variable (ζ:ℝ)
abbrev ape:= (Peaks.parcel G false ζ).run g
abbrev beak:= tradew n (scaleG G g)
include G g ζ
lemma spearV : effectK (ape G g ζ).val (oceanA G)=oceanA G:=by
 let Y:= ape G g ζ; let Z:= g ∘ (ratio G).embed; let w(i:Site f):= Z (node (((isle G).symm i).1)); classical
 let F:= Function.extend (node (N:=f)) w (fun _=>1)
 let T:= (Peaks.parcel G true ζ).run F; have hv:T.val=Y.val:=by
    unfold T Y ape; rw [warrant,warrant]; refine congrArg _ (funext ?_); rintro ⟨p,j,u⟩; change (matter (F (node (isle G (p,j))))).val = (matter (Z (node p))).val
    have hp: ∀ i,F (node i)=w i:=fun i=> Tenant.needle.extend_apply w (fun _=>1) i; rw [hp]; unfold w; rw [Equiv.symm_apply_apply]
 change effectK Y.val _=_; rw [←hv]; exact (pompK _ _ (switchG G).symm (tradew f F).val (mateK f)).trans (congrArg (cartsL (switchG G).symm) (mastC F))
lemma op_t (t:Ket (Tulip.Single n)): acts (ape G g ζ).val (coat (patchQ G) t)=coat (patchQ G) (acts (beak G g).val t):=by
 nth_rw 1 2 [←basis_expand t]; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=> congrArg _ ?_; rw [basis_shell]; apply PiLp.ext; intro x; let H:= patchQ G; let c:=ape G g ζ;  rw [basis_act]
 by_cases h:x∈lows (patchQ G)
 · obtain ⟨x,v,rfl⟩:= mem_map.mp h; rw [←seamK,trails,basis_act]; rcases x with ⟨⟨p,a⟩,b⟩; rcases i with ⟨⟨q,c⟩,d⟩
   unfold ape beak; rw [warrant]; simp [patchQ,rideG,jump_apply,tradew,touch,scaleG]; rfl
 rw [basin (patchQ G) _ _ h]; rcases i with ⟨⟨l,j⟩,t⟩; rcases x with ⟨⟨q,k,hk⟩,a⟩; unfold ape; rw [warrant]; simp [patchQ,rideG,jump_apply]; intro p u K; apply False.elim; exact h (mem_map.mpr ⟨((l,j),a),mem_univ _,by subst q; subst k; subst hk; rfl⟩) -- tune implication
lemma mist_a (x:Phys n):hoist (patchQ G) (reefS G true) (effectK (beak G g).val x)= effectK (ape G g ζ).val (hoist (patchQ G) (reefS G true) x):=by
 have hg:=act_unit (quantU (ape G g ζ)); let k:= Tset n; refine charge_i _ _ (reefS_deck ..) _ _ k (mateK n) (touchP n ▸ tickB n) (op_t G g ζ) (mastC (scaleG G g)) ?_ x
 let y:=oceanA G; have he:=spearV G g ζ; rw [sec_phase] at he; unfold effectK at he; rw [map_smul] at he; exact smul_right_injective _ (norm_pos_iff.mp ((sectorU G).symm ▸ zero_lt_one)) he
lemma mist_f (x: Wave (Iota G)): pailL (patchQ G) (reefS G true) (effectK (ape G g ζ).val x)= effectK (beak G g).val (pailL (patchQ G) (reefS G true) x):=by
 have h:= reefS_deck G true; let T:= pailL (patchQ G) (reefS G true); let A:= quantU (beak G g); let U:=quantU (ape G g ζ)
 apply PiLp.ext; intro i; rw [←basis_inner,←basis_inner]; let b:=basisKet i; let L:=acts (star A.val) b; have he:b=acts A.val L:=by unfold L; rw [←act_mul,A.property.2, act_one]
 change inner ℂ b (T (acts U.val x))= inner ℂ b (acts A.val (T x)); rw [he,act_unit_inner A]; unfold T; rw [pails _ _ h]; change inner ℂ (hoist _ _ (effectK (beak G g).val L)) (acts U.val x)=_; rw [mist_a]; apply Eq.trans (act_unit_inner U _ x) (pails _ _ h _ _ |>.symm)
lemma rain_c (X:Nom n f)(p:G.count=L)(M:Male)(i:ℕ)(x:i≤n.val)(h:Tax L (ticketT (Thread j) true) false true a w i ζ)(u:unionP X∈legal G ζ)(W: Phys f):fire (Thread j) G M (unionP (july G g X)) (cartsL (switchG G).symm (effectK (tradew f g).val W))=effectK (tradew n (scaleG G g)).val (fire (Thread j) G M (unionP X) (cartsL (switchG G).symm W)):=by
 let U:= (Peaks.parcel G true ζ).run g; let s:=ticketT (Thread j) true M G; let A:= unionP X; let B:=unionP (july G g X); let Z:=ape G g ζ
 have hs: s B*U.val=Z.val*s A:=by rw [show s B= _ from crown_pulse G (h M G p x) X u g,mul_assoc,U.property.1,mul_one]
 have hx(v: Phys f) : effectK (s B) (cartsL (switchG G).symm (effectK (tradew f g).val v))=effectK Z.val (effectK (s A) (cartsL (switchG G).symm v)):=by
    rw [←pompK]; change acts _ (acts (quant U.val) _)= acts _ (acts _ _); rw [←act_mul,←quant_mul,hs,quant_mul, act_mul]
 have hm:chargeA (Thread j) G M B=chargeA (Thread j) G M A:=by
    let f':=oceanA G; have he:=hx (mateK f); rw [mastC] at he; change inner ℂ f' (effectK (s B) f')=inner ℂ f' _; rw [show effectK (s B) f'= _ from he]; have ht:=act_unit_inner (quantU Z) f' (effectK (s A) f'); rw [show acts (quantU Z).val f'=f' from spearV G g ζ] at ht; exact ht
 unfold fire; rw [show chargeA _ _ _ B=_ from hm,hx]; change _=acts (quant (beak G g).val) (_ • _); rw [map_smul]; exact congrArg _ (mist_f G g ζ _)
end YM.CF.Pyx
