import SatinPP.Corners
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open Preparation.Yoke
open Regis Circuit Regis.Head.Brecht QuadClock
open CF.Onyx (moor)
open YM.Stationary (Gaia)

-- Maxwell curl. expansion from Silk/Mango/Oriel
abbrev duff(i j:Axis)(x:Gaia):ℝ:= -2*(YM.basis i j)*(‖x‖^2)⁻¹^2+ 8*(x i*x j)*(‖x‖^2)⁻¹^3
abbrev drum0 (a b c d:Axis)(x:Gaia):ℝ:=(((if c=b then duff a d x else 0)-(if d=b then duff a c x else 0))-((if c=a then duff b d x else 0) - if d=a then duff b c x else 0))
def drum (x:Gaia)(A B:PlaqAxes):ℝ:= drum0 A.val.1 A.val.2 B.val.1 B.val.2 x
lemma playsDuet (A B:PlaqAxes)(x:Gaia)(h:x≠0): Maxwell.bareCurl A.val.1 A.val.2 B.val.1 B.val.2 x=Maxwell.normal*drum x A B:=by
 simp only [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad h,Maxwell.second_Green h,drum,drum0,duff]; split_ifs<;> ring

def vote (f:PlaqAxes→ℝ):ℝ:= (f rimA-f rimB-f rimC+f rimD)/2
lemma tally(f:PlaqAxes→ℝ):(∑ i,witnessZ i*f i)=vote f:= by
 let S: Finset PlaqAxes:={rimA,rimB,rimC,rimD}
 rw [← sum_subset (s₁:=S) (subset_univ _)]; swap
 · intro i h u; rcases rimCases i with p|p|p|p|p|p <;> subst i; rotate_left; exacts [(u (by simp [S])).elim,(u (by simp [S])).elim,(u (by simp [S])).elim,(u (by simp [S])).elim,by norm_num [witnessZ,show starWeight highHigh=0 from rfl],by norm_num [witnessZ,show starWeight lowLow=0 from rfl]] -- tune
 unfold S; rw [sum_insert (by decide : rimA∉ ({rimB,rimC,rimD}:Finset _) ), sum_insert (by decide : rimB ∉ ({rimC,rimD}:Finset _) ),sum_insert (by decide : rimC∉ ({rimD}:Finset PlaqAxes)),sum_singleton]
 rw [show witnessZ rimA=1/2 from rfl, show witnessZ rimB=(-1)/2 from rfl,show witnessZ rimC=(-1)/2 from rfl, show witnessZ rimD=1/2 from rfl]
 unfold vote;ring
def soloSq (x:Gaia):=vote fun i=>vote fun j=>drum x i j^2
lemma fanfare (p:Vantage)(e:p≠0): gloss p=(↑(soloSq (moor p)/16):ℂ):=by
 let x:=moor p
 have h:x≠0:=fun h=>e (congrArg WithLp.ofLp h)
 let F:= fun i j : PlaqAxes=> drum x i j^2
 have he:(∑ i,witnessZ i*(∑ j,witnessZ j*F i j))=soloSq x:=by simp only [tally,F,soloSq]
 have t(i j): spectrumColor i j SU.group x= (F i j:ℂ)*(canonWeight:ℂ)/16:= by
    unfold spectrumColor duoPower specter; rw [playsDuet i j x h]; unfold F canonWeight; rw [Complex.ofReal_mul,Complex.ofReal_pow]; push_cast; ring
 have hh:spectrumℓ witnessZ SU.group x= (soloSq x:ℂ)*((canonWeight:ℂ)/16):= by
    rw [←he,Complex.ofReal_sum,Finset.sum_mul]
    unfold spectrumℓ wholeV
    refine Finset.sum_congr rfl fun i _=>?_
    rw [Complex.ofReal_mul, Complex.ofReal_sum,Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _=>?_
    dsimp only; rw [t,Complex.ofReal_mul (witnessZ j)];ring
 change _/_= (↑(soloSq x/16):ℂ)
 have hx:(canonWeight:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr focus_positive.ne'
 rw [hh,Complex.ofReal_div,Complex.ofReal_ofNat]; field_simp

def quarter (x:Gaia):ℝ:= ‖x‖^2
lemma quarter_dance(x:Gaia):
 quarter x=x 0^2+x 1^2+x 2^2+x 3^2:= by
 unfold quarter; rw [EuclideanSpace.real_norm_sq_eq]
 -- Axis defeq Fin4
 simp [Axis,Fin.sum_univ_succ]; ring
def hiNote (q:ℝ)(p:Vantage)(i j:Axis) := -2*(YM.basis i j)*q+8*(p i*p j)
def horn (q:ℝ)(p:Vantage)(A B:PlaqAxes):ℝ:=let f:= hiNote q p;let a:=A.val.1;let b:=A.val.2; let c:=B.val.1; let d:=B.val.2; (((if c=b then f a d else 0)-(if d=b then f a c else 0))-((if c=a then f b d else 0) - if d=a then f b c else 0))
lemma treble (x:Gaia)(h:x≠0)(i j:Axis) :
 duff i j x = hiNote (quarter x) x.ofLp i j * ((quarter x)⁻¹)^3:=by
 have ht: ‖x‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr h)
 unfold duff hiNote quarter; field_simp

def volume0 (q:ℝ)(p:Vantage):ℝ:= (vote fun i=>vote fun j=>horn q p i j^2)/16
lemma treble_pay (x:Gaia)(h:x≠0):
 soloSq x /16 = volume0 (quarter x) x.ofLp * ((quarter x)⁻¹)^6:= by
 have T (A B):drum x A B = horn (quarter x) x.ofLp A B*((quarter x)⁻¹)^3:=by
    unfold drum drum0 horn; simp only [treble x h,_root_.sub_mul,ite_mul,zero_mul]
 have y (f:PlaqAxes→ℝ)(z:ℝ): vote (fun i=> f i*z)=vote f*z:=by unfold vote; ring
 let F:=horn (quarter x) x.ofLp
 let z:=(quarter x)⁻¹
 have hw (i): vote (fun j => drum x i j ^2)=vote (fun j=> F i j^2)*z^6:= by
    rw [←y]; unfold vote; unfold F z; simp_rw [T]; ring
 unfold soloSq volume0; simp_rw [hw]; rw [y _ (z^6)]; change (_*z^6)/16=vote (fun i=>vote (fun j=>F i j ^2))/16*z^6; ring
def pth (p:Vantage):ℝ:= p 0^4+p 1^4-6*p 0^2*p 1^2 + (p 2^4+p 3^4-6*p 2^2*p 3^2)
def tilt (p:Vantage):ℝ:=p 0^2+p 1^2+p 2^2+p 3^2


set_option maxHeartbeats 2000000 in
lemma tumbling (p:Vantage):volume0 (tilt p) p = pth p:= by
 norm_num [volume0, horn, hiNote, vote, basis_eq, rimA, rimB, rimC, rimD]
 simp (config := {decide := true})
 unfold tilt pth
 ring
lemma heyday (p:Vantage)(q:p≠0):gloss p=(↑(pth p/(tilt p)^6):ℂ):=by
 have e:moor p≠0:=fun h=>q (congrArg WithLp.ofLp h)
 have h: quarter (moor p)=tilt p:=quarter_dance _
 rw [fanfare _ q,treble_pay _ e, h]
 change ↑(volume0 (tilt p) p*((tilt p)⁻¹)^6)= (↑(pth p/(tilt p)^6):ℂ)
 rw [tumbling,inv_pow,div_eq_mul_inv]
lemma joyous (p:Vantage)(q:p≠0):ContinuousAt gloss p:= by
 have e:moor p≠0:=fun h=>q (congrArg WithLp.ofLp h)
 have hp: Continuous pth:=by unfold pth; fun_prop
 have ht: Continuous tilt:=by unfold tilt;fun_prop
 have hv: (tilt p)^6 ≠0:=pow_ne_zero _ ((quarter_dance _ : quarter (moor p)=tilt p).symm.trans_ne (pow_ne_zero _ (norm_ne_zero_iff.mpr e)))
 refine ContinuousAt.congr (f:=fun u=> (↑(pth u/(tilt u)^6):ℂ)) (Complex.continuous_ofReal.continuousAt.comp (hp.continuousAt.div (ht.continuousAt.pow 6) hv)) ?_
 filter_upwards [eventually_ne_nhds q] with u h; exact (heyday u h).symm

def aglow (j:Axis)(s:ℝ): Vantage:=Function.update 0 j s
lemma aglow_j(j:Axis)(s:ℝ): aglow j s j=s:=by simp only [aglow, Function.update_self]
lemma solo_aglow(t:ℝ)(q:0<t):gloss (aglow 3 t) = (↑((t^8)⁻¹):ℂ):=by
 have h:aglow 3 t ≠0:=fun e=> by have a:=aglow_j 3 t; rw [e] at a; exact q.ne a
 rw [heyday _ h]
 simp (config:={decide:=true}) [aglow, tilt,pth, Function.update]
 congr 1
 field_simp

