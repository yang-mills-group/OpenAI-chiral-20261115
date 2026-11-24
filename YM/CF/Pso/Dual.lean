import YM.CF.Cay.Yarn
import YM.CF.Cay.Plush
import YM.CF.Forge.Dawn
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay

open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}
local notation "ζ"=>Monk SU.group S
open Slate.Far
open Matrix
variable {A:Monk SU.group S}{X: Support c}
section
-- kinetic coordinate chart change; inverse dilation proof; no Warm default needed
abbrev rune (β t:ℝ):= coupling t/coupling β
abbrev poleY (M:ζ)(β u:ℝ):ζ:= Cay.rough M ((rune β u) • M.z)
lemma rune_p {β u:ℝ}(h:0<β)(p:0<u) : 0 < rune β u:= div_pos (coupling_pos p) (coupling_pos h)
lemma rune_s {β u:ℝ}(h:0<β)(p:0<u) : rune β u ^2 = β/u:=by unfold rune coupling; rw [div_pow,inv_pow,inv_pow,Real.sq_sqrt h.le,Real.sq_sqrt p.le,div_inv_eq_mul,mul_comm]; rfl -- tune
private lemma tally {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (L:E≃L[ℝ]E)(n:ℕ)(f:E→ℝ):iteratedFDeriv ℝ n (f ∘ L) 0=(iteratedFDeriv ℝ n f 0).compContinuousLinearMap fun _=> L:=by
 simpa only [iteratedFDerivWithin_univ, map_zero, Set.preimage_univ] using L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (show L 0 ∈ Set.univ from trivial) n
lemma strut_t (F:E→ℝ)(L:E≃L[ℝ]E)(p v:E): strut (F ∘ L) p v=strut F (L p) (L v):=by
 have hx(f:E→ℝ)(p v:E):strut f p v=iteratedFDeriv ℝ 1 f 0 ![p]+ iteratedFDeriv ℝ 2 f 0 ![v,p]/2:=by rw [iteratedFDeriv_one_apply,iteratedFDeriv_two_apply]; rfl
 rw [hx,hx,tally,tally]; simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,ContinuousLinearEquiv.coe_coe]
 have he:(fun i:Fin 2=> L ((![v,p]:Fin 2→ E) i)) = ![L v,L p]:= funext (fun i=> by fin_cases i <;> rfl)
 rw [he,show (fun i:Fin 1=> L ((![p]:Fin 1→ E) i))=![L p] from funext (fun i=> by fin_cases i;rfl)]
def dialK (q:ℝ)(h:q≠0)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]:E ≃L[ℝ] E where
 toFun:=fun x=>q • x
 invFun:=fun x=>q⁻¹ • x
 left_inv:= fun _=>by simp [smul_smul,h]
 right_inv:= fun _=>by simp [smul_smul,h]
 map_add':=smul_add q
 map_smul':=fun s x=>by dsimp; rw [smul_comm]
 continuous_toFun:=by fun_prop
 continuous_invFun:=by fun_prop
variable (T:Tube SU.group S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β u:ℝ)(h:0< β)(p:0<u)(M:Monk SU.group S)
local notation "Rz"=> poleY M β u
include M S T h p
lemma lift_z: (poleY M β u).fuel x T q d l β=M.fuel x T q d l u:=by
 let W:=liftN T x M.V M.k M.key M.park q d (M.bush _) l
 let U:=credW T M.key M.park M.k q d x (M.bush x) l M.V
 change W + coupling β • (U *ᵥ wrench M x (rune β u • M.z))= W + coupling u • (U *ᵥ wrench M x M.z)
 rw [map_smul, mulVec_smul,smul_smul, show coupling β * rune β u=coupling u from by unfold rune; field_simp [(coupling_pos h).ne']]
lemma port_z: (poleY M β u).sent x T q d l β=M.sent x T q d l u:=by
 let F:= Next.SectorChange.physical (x:=x) M.key M.park M.V (M.bush x)
 exact congrArg (fun w=> F (tape w)) (lift_z T x q d l β u h p M)
lemma ψ_z (s: Signed)(i: Along S): dense T x q d l β s i Rz=dense T x q d l u s i M:=by
 unfold dense stars Slate.payer -- see goal
 -- care
 dsimp only
 simp_rw [lift_z T x q d l β u h p M,port_z T x q d l β u h p M]
 rfl
lemma adjust_z: adjust T x q d l β Rz=(β/u)*adjust T x q d l u M:=by
 let t:=β/u; let Y:=rune β u; rw [basedP T x q d l β h,basedP T x q d l u p,mul_add, Finset.mul_sum]
 dsimp only
 congr 1
 · change wrench M x (Y • M.z) ⬝ᵥ wrench M x (Y • M.z) / 2=t*flog q M x
   rw [map_smul, smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul]; unfold flog; change Y*(Y*_)/_= _; rw [← mul_assoc,←pow_two,show Y^2=t from rune_s h p]; ring
 apply sum_congr rfl; intro i _; unfold subX; rw [show tunic T x q d l β Rz true=tunic T x q d l u M true from congrArg (fun f=> axle M.key M.park T x M.k q d (M.bush x) f M.V) (lift_z T x q d l β u h p M),show tunic T x q d l β Rz false=tunic T x q d l u M false from rfl]; field_simp -- name axle
local notation "D_ζ"=> Directions SU.group f
omit T
lemma ringlet (H F: Monk SU.group S→ℝ)(q₀:ℝ)(v:∀ (M:Monk SU.group S), H (poleY M β u)=q₀*F M)(hx:q₀≠0) (e:Bond f): spring H e (poleY M β u)=q₀*spring F e M:=by
 let Z:=dialK (rune β u) (rune_p h p).ne' D_ζ; let b:=arrow e M.z
 have hp:(arrow e (poleY M β u).z)=Z b:=by
    funext i; by_cases x:i=e; · subst i; simp [Z,b,arrow,dialK,poleY,rough]
    simp [Z,b,arrow,dialK,poleY,rough,x]
 let Y:= dialK q₀ hx ℝ
 have he(p : D_ζ→ℝ)(v a:D_ζ):strut (Y ∘ p) v a=q₀*strut p v a:=by
    have ht(f:D_ζ→ℝ):strut f v a= iteratedFDeriv ℝ 1 f 0 ![v]+ iteratedFDeriv ℝ 2 f 0 ![a,v]/2:=by unfold strut; rw [iteratedFDeriv_two_apply,iteratedFDeriv_one_apply]; rfl
    rw [ht,ht,Y.iteratedFDeriv_comp_left,Y.iteratedFDeriv_comp_left]; change q₀*((iteratedFDeriv ℝ 1 p 0) ![v])+q₀*((iteratedFDeriv ℝ 2 p 0) ![a,v])/2=q₀*_ ; ring -- parentheses
 have hF: (H ∘ rough M) ∘ Z=Y ∘ (F ∘ rough M):= funext fun i=> v (rough M i)
 change strut (H ∘ rough M) (arrow e (poleY M β u).z) (Z M.z)=q₀*strut _ b _; rw [hp,← strut_t,hF]; exact he (F∘ rough M) _ _
include T
lemma shove_z (s:Signed)(i:Along S): let f(β:ℝ):= dense T x q d l β s i; shotB (f β) (poleY M β u)=shotB (f u) M:=by
 intro F; let Z:=dialK (rune β u) (rune_p h p).ne' (Directions SU.group f)
 have he: (F β ∘ rough M) ∘ Z= F u ∘ rough M:=funext fun z=> ψ_z T x q d l β u h p (rough M z) s i
 unfold shotB ash secT; change (F β ∘ rough M) (Z M.z)- (F β ∘ rough M) 0-strut _ (Z _) (Z _)=_; rw [← he,← strut_t]; simp only [Function.comp_apply,map_zero]
 rfl -- tune `map_zero` rhs under ∘ not applied.
lemma opus_z (j:ℕ)(i:Bond f): opus T x q d l β j i (poleY M β u)= (β/u)*opus T x q d l u j i M:=by
 unfold opus; have hx (s:Signed)(k:Along S): spring (dense T x q d l β s k) i Rz=spring (dense T x q d l u s k) i M:=by
    exact (ringlet β u h p M _ _ 1 (fun M'=> (ψ_z T x q d l β u h p M' s k).trans (one_mul _).symm) one_ne_zero i).trans (one_mul _)
 rw [ringlet β u h p M _ (adjust T x q d l u) (β/u) (adjust_z T x q d l β u h p) (div_pos h p).ne' i]; simp_rw [hx]; dsimp only [poleY,rough]; field_simp
end
end YM.CF.Cay
