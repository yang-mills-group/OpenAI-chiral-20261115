import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
variable (P:Spine)(a:Axis) (x:P.Spectrum0 a) (s:ℕ)
local notation "μ"=>P.birthF a s
local notation "ν"=> P.viewF a x s
lemma mn_add {p q:P.Test}(h:μ p)(k:μ q):μ (p+q):=by obtain ⟨p,rfl⟩:=h; obtain ⟨q,rfl⟩:=k; exact ⟨⟨p.val+q.val,Subalgebra.add_mem (enclave P.calibration) p.property q.property⟩,rfl⟩
lemma mn_scale(z:ℂ){p:P.Test}(e:μ p):μ (z • p):= by obtain ⟨p,rfl⟩:=e; exact ⟨⟨z • p.val,Subalgebra.smul_mem (enclave P.calibration) p.property z⟩,rfl⟩
lemma mn_plus{p q:P.Test}(h:μ p)(k:μ q):ν (mn_add P a s h k)= ν h+ν k:=by
 let u:=mn_add P a s h k; have hg:=P.sixWard_view_sub a x s u k ((show μ ((p+q)-q) by rwa [add_sub_cancel_right])); have he:ν h=ν u-ν k:= (P.identical_F a x s h _ (add_sub_cancel_right ..).symm).trans hg
 exact (eq_sub_iff_add_eq.mp he).symm
lemma mn_mult(z:ℂ){p:P.Test}(h:μ p):ν (mn_scale P a s z h)=z •ν h:= by
 let v:=mn_scale P a s z h
 have hh(e:P.Test)(g:μ e): inner ℂ (ν g) (ν v) = z * inner ℂ (ν g) (ν h):= ((P.released_gram a x s g v).trans (congrArg (P.singleState a s x) (mul_smul_comm ..))).trans ((map_smul (P.singleState a s x) z _).trans (congrArg (fun x':ℂ=>z*x') (P.released_gram a x s g h).symm))
 apply Spine.right_weight (P.ColorHil a x) _ _ (0:P.ColorHil a x); intro i v; simp only [List.mem_cons,List.not_mem_nil,or_false] at v; rcases v with v|v <;> subst i <;> exact hh _ _
local notation "K"=> P.calibration
lemma bornP(o:Cover)(h:(K).ℓ+22 ≤ nodeC o a):P.birthF a s (wp P s o):=by
 have p:wp P s o∈bay K (bands o 22) true:= lining_test ..
 refine P.criteria a s p ?_ (color_wp P s o); intro z q; have u:=bands_spec o q a; rw [zero_add]; omega
lemma rooty(j:ℕ)(o:Cover)(h:(K).ℓ+22 ≤ nodeC o a): P.birthF a s (etui P s j o):=by
 apply bornP; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]
 apply h.trans
 apply le_mul_of_one_le_left (by omega); exact_mod_cast (show 1≤ P.par.R.L.val^(s-j) from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))
variable (j:ℕ)(o:Cover)(C D:ℕ→ℝ)(h:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o a)
include h
lemma bonDress :P.birthF a (s+1) (dress P s j o true C D):= mn_add _ _ _ (mn_scale P a _ _ (rooty P a (s+1) j o h)) (mn_scale P a _ _ (P.rig a s (s+1) (rooty P a s j o h) (Nat.le_succ _)))
lemma mn_dress : P.viewF a x (s+1) (bonDress P a s j o C D h)= tokenA P (s:=s) (j:=j) true C D • P.viewF a x (s+1) (rooty P a (s+1) j o h) + tokenB P (s:=s) (j:=j) true • P.viewF a x s (rooty P a s j o h):=by
 let l:= rooty P a (s+1) j o h; let k:= rooty P a s j o h; let f:=P.rig a s (s+1) k (Nat.le_succ _)
 exact (mn_plus P a x (s+1) (mn_scale P a _ (tokenA P (s:=s) (j:=j) true C D) l) (mn_scale P a _ (tokenB P (s:=s) (j:=j) true) f)).trans (congrArg₂ (·+·) (mn_mult P a x (s+1) _ l) ((mn_mult P a x (s+1) (tokenB P (s:=s) (j:=j) true) f).trans (congrArg (fun w:P.ColorHil a x=>tokenB P (s:=s) (j:=j) true • w) (P.view_rig a x s (s+1) k (Nat.le_succ _)))))
private abbrev squareR (f:P.Test)(v:P.Spectrum0 3):ℝ:= (P.singleState a s (P.otherSpectrum 3 a v) (P.reflectTest a f*f)).re
omit h
lemma as_mn {p:P.Test}(f:μ p)(v:P.Spectrum0 3) : squareR P a s p v = ‖P.viewF a (P.otherSpectrum 3 a v) s f‖^2:=by
 exact (congrArg Complex.re (P.released_gram a (P.otherSpectrum 3 a v) s f f).symm).trans (slevel (X:=P.ColorHil a (P.otherSpectrum 3 a v)) _)
where slevel {X:Hilbert}(v:X): (inner ℂ v v).re=‖v‖^2:=by rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]; change (((‖v‖:ℝ):ℂ)^2).re=_; rw [←Complex.ofReal_pow,Complex.ofReal_re]
lemma mn_cont(f:P.Test):Continuous (squareR P a s f):= Complex.continuous_re.comp ((P.chi_joint a _).comp (P.otherSpectrum 3 a).continuous)
lemma mn_earn (f:P.Test): (∫ v,squareR P a s f v ∂P.pillars 3)=(P.E s (P.reflectTest a f*f).val).re:=by
 let B:= P.reflectTest a f * f; let W:=P.reading a s B
 have e:= P.recovery_all 3 a W; change (∫ v,P.chi a (P.otherSpectrum 3 a v) W ∂P.pillars 3)=inner ℂ (P.groundZero a) ((P.compressed a s B) (P.groundZero a)) at e
 rw [P.occupied] at e
 rw [←e]; exact @integral_re _ _ _ ℂ _ _ (((P.chi_joint a W).comp (P.otherSpectrum 3 a).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
#print axioms mn_dress
#print axioms mn_earn
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
