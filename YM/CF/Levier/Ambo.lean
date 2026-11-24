import YM.CF.Levier.CrestD
import YM.CF.Reef.Bronze
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
open Reef Kennel
variable {d r w p:ℝ}(L:Aim N)(t:L.toll d r w p)(u:Cry L)
include t
lemma dawn(T:Bkg (More N)): L.den (Yg a T)= ZoneH a (L.den T):=by simp only [Aim.den, Pi.add_apply,colorX]; rw [symmetry a (cavil L.x) (fun _ _=> pre_a _ _ _ t.1.1),symmetry _ _ (fun _ _=>pre_a _ _ _ t.2.1),map_add]
include u
lemma prism_x(x:Bkg (More N))(B:UNI SpinIdx)(h:JetS a.s b (detX a.s) B): Moire.bloom L (profile (stir (xtra b) a x))= Thera.jazz (detX a.s) (sings b (siteU a b B N) (Moire.bloom L (profile x))):=by
 rw [Moire.bloom_P,Moire.bloom_P]; cases b
 · rw [show stir (xtra false) a x= Yg a x from rfl,dawn _ _ t]; exact z_spin _ _ B h -- tune
 let U:=spinX a.s; let V:=U*axS; let F:=L.den; have hx:F (stir (xtra true) a x)= F (Yg a (echo x)):=by rw [show Yg a (echo x)=echo (Yg a x) from echo_p x _ _]; rfl
 have hy: JetS a.s true (detX a.s) V:=by simpa only [one_mul,Bool.false_xor] using jet_add true false (detX a.s) 1 a.s axS U cloneSX (bud_s _)
 obtain ⟨z,q,hz⟩:= kitsX true a.s B V h hy
 have hV : sings true (siteU a true B N)=sings true (siteU a true V N):=by funext T; rw [site_ui,site_ui,singT,twist_formula,singT,twist_formula,Ygs a _ _ q,star_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
 rw [hV]; change F _=_; rw [hx,show F (Yg a _)=_ from dawn a L t _,cry_p u,zone_c]; congr 1
 change twist _ (twist _ (cc _))= twist (prepU a (U*axS) inert N) _; have he:prepU a U inert N * axle N=prepU a V inert N:=by rw [show axle N=prepU diva axS inert N from rfl,kio,show joinX diva a=a by simp [joinX,diva,incX]]
 rw [←show _=prepU a (U*axS) inert N from he, Fock.twin]; rfl
end YM.CF.Levier
