import YM.SU5.May.FloeWeight
import YM.CF.Onyx.Gold
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU
variable {N F:Side}(G: Ratio N F)(p:Odd G.count.val)
local notation "L" => G.count
variable (j:ℕ)(v:Momentum)
abbrev hail (N:Side)(p:Odd N.val) : Jill.Male:=⟨N,p⟩
abbrev white: Jill.Male:=hail 1 odd_one
def coins(s:Side)(r:ℝ):ℂ:= (r:ℂ)^3/(s.val:ℂ)^4
def wave (j:ℕ)(M:Jill.Male)(z:Cover)(s t:SpinIdx)(u:Momentum):ℂ:= mode u z * dip j M u s t
def delta (N:Side)(j:ℕ)(M:Jill.Male)(r:ℝ)(z:Cover)(s t:SpinIdx): ℂ:= coins N r * ∑ k:Site N,wave j M z s t (mel k)
omit p
lemma prices : coins F (G.count.val:ℝ)= coins N 1 * ((G.count.val:ℂ)⁻¹):=by
 unfold coins; rw [G.exact_size]; push_cast; field_simp [side_ne N,side_ne G.count] -- tune
lemma dip_math (M:Jill.Male)(k:Site N): dip j M (mel k)= lash (mixL j M.val (mel k)):=by
 have t:= base_subset_realCube zone_pos (mel_h k); have hz:shell j M.val (mel k) ≠0:=by rw [shell_inv j M.val t (mel_away k)]; exact inv_ne_zero (graphs_ne (phys_mix j M.val M.property _ t.1))
 rw [dip, skin_mix j _ t,lash_s,inv_smul_smul₀ hz]
lemma whitePrice (k: Site N): dip j white (mel k)=lash (bGraph (mel k)):=by
 let v:= mel k; rw [dip_math]; unfold mixL; change lash ((_ : ℂ) • (∑ l:Site 1,_))=_
 rw [Finset.sum_eq_single 0]; change lash (((1:ℕ):ℂ)⁻¹ • (muff j 1 (aliasAt v (0: Site 1))^2 • _)) = _; rw [alias_zero_eq]; simp [muff_one,narrow,v] -- maybe
 intro i _ g; exact (g (by unfold Site Four Per at *; exact Subsingleton.elim (α:= Axis → ZMod 1) _ _)).elim; simp
local notation "M₀"=>hail L p
include p
private lemma real_frame (k:Site N) : dip j M₀ (mel k) = ((G.count.val:ℂ)⁻¹ • ∑ l:Site L,muff j L (mel (aimK G k l))^2 • dip j white (mel (aimK G k l))) := by
 rw [dip_math]; simp_rw [whitePrice]; change lashCL ((G.count.val:ℂ)⁻¹ • ∑ l:Site L,_)= _
 simp_rw [aim_eq G p,map_smul,map_sum,map_smul]; rfl
local notation "Z" => Trace j L
variable (x y:Cover)(s t:SpinIdx)
local notation "D" x:max a:max => point L x (traces L j a)
omit p
private lemma st_locus(k:Site N)(l:Site L)(a b: Z): mode (aliasAt (mel k) l) (point L x (traces L j a)-point L y (traces L j b)) = mode (mel k) (x-y)* mode (aliasAt (mel k) l) (traces L j a) * mode (aliasAt (mel k) l) (-traces L j b):=by
 rw [show point L x (traces L j a)-_= G.count.val • (x-y)+traces L j a + -traces L j b from ?_, mode_shift,mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one]; unfold point; rw [smul_sub]; abel -- tune from underscore
include p
private lemma priceAt(k:Site N)(l:Site L) : let v:= aliasAt (mel k) l; mode (mel k) (x-y)*(muff j L v^2 * dip j white v s t)=expected (fun a: Trace j L=>expected fun b:Trace j L=> wave j white (point L x (traces L j a)-point L y (traces L j b)) s t v):=by
 intro v; unfold wave v; simp_rw [st_locus G j x y,expected_mulRight,expected_mul,← weight_neg G.count _ p]; simp_rw [expected_mulRight,expected_mul,← weight_pose]; ring -- expected_mul* conflict
lemma rocking : delta N j M₀ 1 (x-y) s t= expected (fun a:Trace j L=> expected fun b:Trace j L=> delta F j white G.count.val (point L x (traces L j a)-point L y (traces L j b)) s t):=by
 unfold delta; simp_rw [summing G p,expected_mul,expected_sum,wave]; rw [prices G]
 rw [mul_assoc,Finset.mul_sum _ _ ((G.count.val:ℂ)⁻¹)]; apply congrArg; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [real_frame G p,Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,Finset.mul_sum]; apply sum_congr rfl; intro k _; rw [aim_eq G p]
 rw [Matrix.smul_apply,smul_eq_mul,show mode (mel i) _*_ = ((G.count.val:ℂ)⁻¹)* (mode (mel i) (x-y) * (muff j G.count _ ^ 2 * dip j white (aliasAt (mel i) k) s t)) from mul_left_comm ..]; exact congrArg _ (priceAt G p j x y s t i k)
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.rocking
