import YM.SU5.Diva.Uprise
/-! # Explicit tangent gamma for our axial composite field. Compute powers before any spectral continuation. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Twah
namespace Cordial
open Lead (Clan)
open YM.Stationary (Gaia)
variable {I:Type*} (P:Cellz I→Gaia)(D:I→DirSpin)
private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
 -- from Audition
 simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
local notation "ρ" => germRho P D
variable (i j': I)(p q:Slot)
def billX(i j:I):ℂ := pencil (P (i,true)-P (j,false)) (dnSpin (D i).2) (upSpin (D j).1)
lemma dhelp (i:Fin 2): i.addNat 2 ∉ plusHalf:=by simpa using (dn_half i)
lemma funds : ρ (i,p,true) (j',q,false) = if p=q then billX P D i j' else 0:=by simp [germRho,pilotS,signW,dhelp, colbase,up_half, frank,billX, readS]
lemma funds_neg : ρ (i,p,false) (j',q,true)= -ρ (j',q,true) (i,p,false):=by simp [germRho,pilotS,signW,dhelp, colbase,up_half,readS]
lemma dcash (p q:Slot)(x:Bool) : ρ (i,p,x) (j',q,x)=0:=by cases x <;> simp [germRho,pilotS,signW,dhelp,up_half,readS]
variable (Z:Clan)
def numberX : ℂ:= dimf Z
def surprise (i j': I):ℂ := numberX Z * (- billX P D i j' * billX P D j' i)
def lyric (i:I) := numberX Z * billX P D i i
def dipole := lyric P D Z i * lyric P D Z j'+ surprise P D Z i j' -- tune args
#print dipole
lemma chorus2 : witness (fun _:I=>Z) [i] P D= lyric P D Z i:=by
 have hx(p:Slot) : runes (ρ) (sayHi [] i p)= billX P D i i:=by
    change runes _ [(i,p,true),(i,p,false)]= _; simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,funds]
 unfold witness; simp only [chore,hx,sum_const,colors_card,nsmul_eq_mul,lyric,numberX]
lemma chorus4 : witness (fun _:I=>Z) [i,j'] P D= lyric P D Z i* lyric P D Z j'+ surprise P D Z i j' :=by
 let f(p q:Slot):= runes (ρ) (sayHi (sayHi [] i p) j' q); let A:=billX P D; let I₁:=A i i*A j' j'; let C:= -A i j'*A j' i
 have h (p q:Slot) : f p q=I₁+if p=q then C else 0:=by
    unfold f; change runes _ [(i,p,true),(i,p,false),(j',q,true),(j',q,false)]= _; rw [wick₂]; simp only [funds,funds_neg,dcash,ite_true,mul_zero,sub_zero]; split_ifs <;> first | contradiction| (expose_names; subst_vars; contradiction)| simp_all [I₁,A,C] -- tune
 unfold witness; change ∑ p∈colors Z,∑ q∈colors Z,f p q= _; have hd(p:Slot)(hp:p∈colors Z): (∑ q∈colors Z,f p q)= numberX Z*I₁+C:=by simp_rw [h,sum_add_distrib]; simp only [sum_const,nsmul_eq_mul,colors_card,sum_ite_eq,if_pos hp,numberX]
 rw [sum_congr rfl hd,sum_const,nsmul_eq_mul,colors_card]; unfold lyric surprise I₁ C A numberX; ring
lemma quaternion (x:Gaia) : (gleamV x) (dnSpin 0) (upSpin 0)= (x 3:ℂ)+(x 2:ℂ)*Complex.I:=by
 let i2:Axis:=2; rw [gleamV,Matrix.mul_sum, Matrix.sum_apply]; simp_rw [Matrix.mul_smul,Matrix.smul_apply]
 have he(i:Axis) : (minA*gammaOp i) (dnSpin 0) (upSpin 0)= (if i=(3:Axis) then (1:ℂ) else if i=(2:Axis) then Complex.I else 0):=by
    rw [minA, show Aop = cutM plusHalf from Adef.trans raising.symm, sub_mul,one_mul,Matrix.sub_apply, cutM,Matrix.diagonal_mul,if_neg (dn_half _),zero_mul,sub_zero]
    change gammaOp i 2 0 = _
    fin_cases i <;> norm_num [gammaOp,Fin.ext_iff,SpinIdx] <;> rfl
 simp_rw [he,smul_eq_mul]; simp only [mul_ite,mul_one,mul_zero]
 norm_num [Fin.sum_univ_succ,Axis,Fin.ext_iff]
 rw [show (Fin.succ (2:Fin 3)) = (3:Axis) from rfl]; ring
-- Actual rational evaluation; prefer argument space Cross=E4 orth axis, with dim in kernel. Preserve sign (left-chiral).
local notation "ε" => YM.basis (3:Axis)
abbrev Bank := OS.Cross (3:Axis)
def siteOf (t:ℝ) (x:Bank):E4:= t•YM.basis (3:Axis) +(x:E4)
lemma shift_abs (t:ℝ) (x:Bank) : ‖siteOf t x‖^2=t^2+‖x‖^2:= by
 unfold siteOf; rw [norm_add_sq_real, real_inner_smul_left, YM.basis_inner, show (x:E4) 3=0 from x.property, norm_smul, YM.basis_norm,mul_one, Real.norm_eq_abs,sq_abs,show ‖(x:E4)‖=‖x‖ from rfl]; ring -- argument
lemma tip (t:ℝ)(x:Bank): siteOf t x 3=t:=by simp [siteOf,show (x:E4) 3=0 from x.property]
lemma left (t:ℝ)(x:Bank): siteOf t x 2=(x:E4) 2:=by simp [siteOf, show (2:Axis)≠3 by decide]
def kP20 (x:Gaia):ℂ:= pencil x (dnSpin 0) (upSpin 0)
def pearly(t:ℝ)(x:Bank):ℝ:=(Real.pi^2*(t^2+‖x‖^2)^2)⁻¹
def plume(t:ℝ)(x:Bank):ℂ:= (pearly t x) • ((t:ℂ)+(((x:E4) 2:ℝ):ℂ)*Complex.I)
lemma pulse_k (t:ℝ)(x:Bank): kP20 (siteOf t x)= plume t x:=by
 unfold kP20 Onyx.pencil plume pearly; rw [Matrix.smul_apply,quaternion,tip,left,← shift_abs, ← pow_mul]
lemma k_flip (x:Gaia):kP20 (-x)= -kP20 x:=by
 unfold kP20 Onyx.pencil; simp only [norm_neg,Matrix.smul_apply,quaternion, PiLp.neg_apply,Complex.ofReal_neg]; rw [neg_mul, ← neg_add,smul_neg]
lemma k_birth : kP20 ε=P20:=rfl
variable (Z: Clan) (t:ℝ) (x:Bank)
local notation "ε₁" => siteOf t x
def layoutFirst (x:ℝ) (p:Bank) : Gaia:= siteOf x p + YM.basis 3
def duo (x:ℝ) (p:Bank)(i:Cellz (Fin 2)): Gaia := if i.1=0 then if i.2 then - ε else (-2:ℝ) • ε else if i.2 then layoutFirst x p + ε else layoutFirst x p
section
local notation "ι"=> duo t x
lemma reunion : billX ι 0 0 0=P20 ∧ billX ι 0 1 1=P20 ∧ billX ι 0 0 1= -(plume (t+2) x) ∧ billX ι 0 1 0=plume (t+4) x:=by
 refine ⟨?_,?_,?_,?_⟩
 · change kP20 ((ι (0,true)) - ι (0,false))=P20; rw [← k_birth]; congr 1; simp [duo]; module
 · change kP20 (ι (1,true)-ι (1,false))=P20; rw [← k_birth]; congr 1; norm_num [duo]
 · rw [← pulse_k,← k_flip]; change kP20 _= _; congr 1; norm_num [duo,layoutFirst,siteOf,add_smul]; module -- maybe need `module`
 rw [← pulse_k]; change kP20 _ = _; congr 1; norm_num [duo,layoutFirst,siteOf,add_smul]; module
end
-- use Lead weighting 1/5
-- `satin_ovoid` true Wick formula target for chosen references.
def ovoid (z:Clan)(t:ℝ)(x:Bank):ℂ:=(numberX z * P20/5)^2+(numberX z/25 * (plume (t+2) x * plume (t+4) x))
lemma goesO : (1/5:ℂ)*(1/5)*witness (fun _=>Z) (Twah.letters 2) (duo t x) 0=ovoid Z t x:=by
 rw [show Twah.letters 2= [0,1] from rfl,chorus4]; unfold lyric surprise ovoid; obtain ⟨a,b,p,q⟩:= reunion t x; rw [a,b,p,q]; ring
-- continuity in real Euclidean spacetime in needed domain
variable{t}
lemma pearl_pos(h:0<t): 0 < pearly t x:=by unfold pearly; positivity
lemma pearl_cont(h:0<t): Continuous (pearly t):= by unfold pearly; refine Continuous.inv₀ (by fun_prop) (fun x=>?_); positivity
lemma plume_cont (h:0<t): Continuous (plume t):= by unfold plume; refine Continuous.smul (pearl_cont h) (Continuous.add continuous_const ?_); exact (((Complex.continuous_ofReal.comp (show Continuous (fun v:E4=> (v (2:Axis))) from PiLp.continuous_apply .. )).comp continuous_subtype_val).mul continuous_const)
lemma horn_cont (h:0≤t):Continuous (ovoid Z t):= by unfold ovoid; first | fun_prop (disch:=positivity) | exact continuous_const.add (continuous_const.mul ((plume_cont (by linarith : 0<t+2)).mul (plume_cont (by linarith : 0<t+4))))
end Cordial
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Cordial.goesO
