import YM.CF.BProof.Single.Gravel
import YM.CF.Cascade.Doric
import YM.CF.Cour.Rite
/-!
# The flat fermion factor in benchmarking from VP929. Infrared every period.

These are *static*, same amplitude parameters and `Loom` Grasp. Using tools
on finite-dimensional coherent states. No hypotheses identifying any other limit
 laws. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (M:Male)(N:Side)(j:ℕ)
-- NB Angular_zero here of static symbols, not identified with Kea.angel.
abbrev angleFin := -OrbT (tickA N) (spar j M (1:Bkg (More N))) 0
lemma cut_free (p:1 ≤ j):IsUnit ((love N).symm (Zoom N (tickA N * spar j M (1:Bkg (More N))))) := by
 -- adapted from Aroma.Foot.census
 let Q: Dress N:=fun _=>0; let T:= grace j M Q
 have he:T 0=tickA _*spar j M (1:Bkg _):=by unfold T grace postR; simp only [Q,Crops,capT,mul_zero,zero_mul,Function.comp_apply,link_one,add_zero,mul_one]
 let n:= SU.Slot; let J:= subHub (N:=N) (fun i=> fuel n j M.val (mel i))
 have hJ:(love N).symm (T 0)=J:= base_grace p _ _ rfl
 rw [←he,Zoom,map_add,map_sub,map_one,map_mul,map_star,hJ,plusInk,StarAlgEquiv.symm_apply_apply]
 let A:=flatV n N; let X:=subHub (fun i=>shell j M.val (mel (N:=N) i) • bins n); let Y:=subHub (fun i=> edgeH n j M.val (mel (N:=N) i)); let F:= subHub (fun _:Site N=> bins n); have he:A=F:=bin_hub.symm
 have hp(k:Site N):shell j M.val (mel k) ≠0:=div_ne_zero (fun h=> (noGhost (p:=mel k) (N:=M.val) (base_subset_realCube zone_pos (mel_h k)) (mel_away k)).ne' (congr_arg Complex.re h)) (mass_ne j _ M.property (base_subset_realCube zone_pos (mel_h k)))
 have hG (U V:Site N→Op (coneA n)): subHub U*subHub V=subHub (fun i=> U i*V i) := lung (Equiv.refl _) U V
 have h: IsUnit (X+(1-A)):= Fock.live_of (show (X+(1-A))*(Y+(1-A))=1 from by
   have ht:X*Y=A:=by unfold X Y; rw [hG]; simp_rw [edgeH,Matrix.mul_smul,Matrix.smul_mul,binsSq, inv_smul_smul₀ (hp _),he]; rfl
   have hu: X*A=X:=by unfold X; rw [he,hG]; simp_rw [Matrix.smul_mul,binsSq]
   have hv:A*Y=Y:=by unfold Y; rw [he,hG]; simp_rw [edgeH,Matrix.mul_smul,binsSq]
   rw [add_mul,mul_add,mul_add,ht,mul_sub,sub_mul (1:Cab n N) A Y,hu,hv,mul_one,one_mul,sub_self,sub_self,mul_sub,mul_one,sub_mul 1 A A,one_mul,show A*A=A from flatA.1]; abel)
 rw [show J*star J=X from ?_]; exact h; unfold J X; rw [subhub_star,hG]; congr 1; exact funext fun i=> fuel_p _ _ _ M.property _ (base_subset_realCube zone_pos (mel_h i))
lemma pigment_zero (n:Side)(P:Pec.Pride n):Pec.pigment P 1=0:=by
 unfold Pec.pigment Pec.lexn Pec.zinger Pec.tag; simp_rw [show ∀ i:Signed,Yg (incX i) (1:Bkg (More n))=1 from fun p=> (by rw [Ywin]; ext; simp [Lattice.pull,Lattice.Step.read]), Nacre.silt_0]; simp only [inner_zero_left, zero_smul,sum_const_zero,map_zero, smul_zero]
variable {m X B L:Side}{ho:Odd L.val}{d:ℝ}
variable {Y:Pricing j L ho (Vault.Thread j)}
-- careful CLI warning
variable (P:Grasp Y B d)(z:0<d)
lemma angle_pay (m:Side)(p:1≤j)(h:P.roundZ ≤ (CSide m B).val)(z:0<d):
 let m':=CSide m B; let V:= (changeM (m:=m) P 1 M); inner ℂ (mateK m') V≠0 ∧ angleFin M m' j=Real.log ‖inner ℂ (mateK m') V‖ ∧ angleFin M m' j ≤ 0 :=by
 intro m' V
 let T:=spar j M (1:Bkg (More m')); let v:=tickA m'; let t:=mateK m'
 have hg:Guard (1:Bkg (More m')) d:=by rw [← link_one]; exact (show ∀ᶠ x in 𝓝 (0:Cloud m'), Guard (represent x) d from nearB d z).self_of_nhds
 have hp:IsStarProjection T:= (P.broadness m' h M).projection _ hg; have hT:=plus_P m'; have hx:Sea T V:= sea_g h _ hg _
 have ht: Matrix.trace (tickA m')=Matrix.trace T := (rank_z m' p M).symm
 have he: skyGlow t (1:Op (Single m')) V=inner ℂ t V:=by rw [skyGlow,quant_one, act_one]
 have hh:IsUnit (Zoom m' (v*T)):= (isUnit_map_iff (love m').symm.toAlgEquiv.toRingEquiv _).1 (cut_free M m' j p) -- need symm
 have hw: inner ℂ t V≠0:=by
    intro u; have hy:= prismK hp hT ht (1:Op (Single m')) V hx t (tickB _);
    rw [he,u,norm_zero,zero_pow (by norm_num: (2:ℕ)≠0),Complex.ofReal_zero] at hy
    apply (Matrix.isUnit_iff_isUnit_det _|>.1 hh).ne_zero; unfold Zoom; simpa only [mul_one] using hy.symm -- let?
 have hy : angleFin M m' j=Real.log ‖inner ℂ t V‖:=by
    have hB:= orb_snap T v 0 V hx t (tickB _) hp hT ht; rw [add_zero,he] at hB; exact hB.symm
 rw [hy]; exact ⟨hw,rfl,Real.log_nonpos (norm_nonneg _) ((norm_inner_le_norm ..).trans (by rw [hx.2,(tickB _).2,mul_one]))⟩
open Pec
include z
lemma limb_fit (q:1≤j)(w:Even j)(G: Ratio (CSide m B) (CSide X B))(f:G.count=L) (k:P.roundZ≤ (CSide m B).val)(I:Pride (CSide m B))(H:Pride (CSide X B))(D:Aim (CSide X B)): (Cour.shipA G P M D.den H I (1,1)).re= angleFin (upMale L ho M) (CSide m B) j-angleFin M (CSide X B) j:=by
 let x: Nom (CSide m B) (CSide X B):=(1,1);
 let K:=foot G (0:Op (Single (CSide X B))); let a:=P; let J:= coatG _ ho j G M D.den x
 have hk:K=0:=rfl
 let t: JointB G x d:= (near_j G d z).self_of_nhds
 let R:=desire L j ho G M x K
 have he:R=0:=by unfold R desire bentT; rw [hk, mul_zero]
 have hx: ‖R‖<1:=by rw [he,norm_zero]; norm_num
 let A:=spar j M (1:Bkg (More (CSide X B)))
 have hs:Matrix.trace (tickA _) = Matrix.trace A:= (rank_z _ q M).symm
 let v:= koh x t f k (0:Op (Single (CSide X B))) hx (by rw [add_zero,mul_one]; exact cut_free _ _ _ q) hs
 have hG:TagG A 0:=by constructor <;> simp
 let Y:= upMale L ho M; have hh: OrbT (tickA _) A 0= -(altar G P x M+invoice R).re+ OrbT (tickA _) (spar j Y x.2) (fruit L j ho G M x K):=laser z G f k M x t hG hx hs v
 have hy: unionP x=1:=by simp [x, unionP, profile_trivial]
 have h₀:fruit L j ho G M x K=0:=by
    rw [hk]; unfold fruit traitP Thera.creep; rw [hy]; simp only [bentT,mul_zero,add_zero,one_mul,mul_one,inv_one]; apply Thera.endorseI G; rw [spry]; change lum _ _ _ _ true M G 1=endorse G 0; rw [cologne j L ho w q (Thread j) (canUse _ _ ho) _ _ f,betP (0:Op (Iota G))] -- tune
 have hJ:J=R:=by
    unfold J Pec.coatG Kennel.gate crux capT; rw [show D.den x.1=0 from BProof.Spin.den_void D, (show foot G (0:Op (Single (CSide X B)))=0 from rfl),mul_zero,zero_mul]; rw [show R=desire L j ho G M x K from rfl,hk]
 rw [h₀] at hh
 unfold Cour.shipA Pec.lush angleFin
 rw [show Pec.coatG _ ho j _ _ _ _=_ from hJ]; simp only [pigment_zero, zero_add,sub_zero, Complex.sub_re, Complex.neg_re] -- tune
 rw [Complex.add_re] at hh; change - ((altar G P x M).re)- (invoice R).re = - OrbT _ (spar j Y x.2) _- -(OrbT _ A 0); linarith only [hh]
end YM.CF.Cascade
#print axioms YM.CF.Cascade.limb_fit
#print axioms YM.CF.Cascade.angle_pay
