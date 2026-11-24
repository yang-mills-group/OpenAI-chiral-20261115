import GaugeFieldConstruction.Spicery
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Loden
open Fir Ember Next.Free
attribute [local instance] opCStarAlgebra
abbrev high := baseF false
abbrev low := baseF true
abbrev Crossbar (b:Bool)(M:Male)(v:Plane):= high*binor M b v*low
abbrev keelM (i:Axis):Plane:=Pi.single i 1
abbrev gamma_A (i:Axis): Pal:= (gammaOp i) ⊗ₖ (1:Op SU.Slot)
abbrev gramB(v:Plane):= ∑ i:Axis, v i • boom i
abbrev uroS(v:Plane):= high*gramB v*low
lemma needleK (i:Axis): high*boom i*low=(Complex.I / 2) • (high * gamma_A i * low):=by
 rw [show high=bins SU.Slot from rfl,boom_A] -- unfold high defeq?
 change (petal i⊗ₖ _)*_= _; unfold petal; simp only [high,gamma_A,baseF, Bool.false_eq_true, ↓reduceIte]; simp only [bins,op_kron_mul, one_mul, Matrix.smul_kronecker,Matrix.smul_mul]
lemma GammaS (p:Plane) : uroS p= (Complex.I/2) • (∑ i:Axis, p i • (high*gamma_A i*low)):=by
 unfold uroS gramB; simp only [Matrix.mul_sum, Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_smul,smul_sum,needleK]; exact sum_congr rfl fun i _=> smul_comm ..
variable (v:Plane)(M:Male)
private lemma tilt₁ (i:Axis): (pilotS M true).2.1 (keelM i)=boom i:=by
 have hx(t:ℝ):Lenten.angle (t • keelM i)=bout i t:=by ext a; by_cases e:a=i<;> simp [Lenten.angle,bout,e,keelM,Pi.single_apply,Lattice.step_apply,e]
 have tt:(fun t:ℝ=>binor M true (t • keelM i))=fun t=>boot 4 M (bout i t):= by unfold binor; simp_rw [hx]; rfl
 have hp:=((kiosk_P M true).turn (keelM i)).diff; rw [tt] at hp; exact hp.unique (barox 4 (by decide) M i)
lemma pins_A : (pilotS M true).2.1 v=gramB v:=by
 nth_rw 1 [show v=∑ i:Axis,v i • keelM i from ?_]; rw [map_sum]; unfold gramB; apply sum_congr rfl; intro x _; rw [map_smul,tilt₁]
 ext i; simp [keelM, Pi.single_apply]
lemma pins_Z :(pilotS M false).2.1 v= -gramB v:=by
 have ht:= ((kiosk_P M true).turn v).diff.const_sub 1; rw [pins_A v M] at ht; exact ((kiosk_P M false).turn v).diff.unique ht
lemma starBlock_P {E:Type*}[NormedRing E][NormedAlgebra ℝ E](f:Plane→ E)(P:Ole Plane E)(p:AptK f P)(u:∀ᶠ x in 𝓝 0, f x*f x=f x)(i:Plane): P.1* P.2.1 i * P.1=0:=by
 let T:=cartF P P; have he:T=P:=p.cart p |>.equal u|>.unique p -- tune
 let x:= P.1; let l:= P.2.1 i; have hx:x*x=x:=congrArg Prod.fst he
 have hz:l*x+x*l=l:=congrArg (fun k:Ole Plane E=> k.2.1 i) he
 have hp:l*x+x*l*x=l*x:=by simpa only [add_mul,mul_assoc l,hx] using (congrArg (·* x) hz)
 exact add_left_cancel (b:=x*l*x) (by rwa [add_zero])
lemma capital_o : high*low=0:=by change _*(1-high)=_; rw [mul_sub,mul_one, (bladeSeal false).1.eq,sub_self]
lemma capital_r:low*high=0:=by change (1-high)*_=_; rw [sub_mul,one_mul, (bladeSeal false).1.eq,sub_self]
-- pay cross
private abbrev blister: Pal→L[ℝ]Pal:= ((ContinuousLinearMap.mul ℝ Pal).flip low).comp (ContinuousLinearMap.mul ℝ Pal high)
lemma ford (x:Plane)(h:Lenten.angle x∈ realCube zone)(b:Bool): Crossbar b M (-x)= -Crossbar b M x:=by
 let q:=Lenten.angle x; let z:=Lenten.angle (-x); have hq:q∈realCube zone:=h; have hx:z= -q:=by unfold z q Lenten.angle; ext; simp
 let a:= M.val; have hw: Aop*grading=Aop:=(BZ.atom 0).plusChir; have hh(y:Momentum)(hy:y∈realCube zone): high*boot 4 M y * low= (Aop* Fir.zen (Fir.skin 4 a y)*(1-Aop))⊗ₖ (1:Op SU.Slot):=by
    let f:=1-Aop; rw [show low=f⊗ₖ (1:Op SU.Slot) from ?_]; swap; · unfold f; simp only [sub_eq_add_neg, op_kron_neg, Matrix.add_kronecker,Matrix.one_kronecker_one]; rfl
    change (Aop⊗ₖ (1:Op SU.Slot))* _ * _= _; simp only [Tap.boot, op_kron_mul,mul_one]; unfold Fir.bar; simp only [mul_add,Matrix.mul_smul,hw, ← mul_assoc Aop grading,mul_one]; congr 1
    have hh:Aop*f=0:=(by unfold f; rw [mul_sub,mul_one,AOne,sub_self]); rw [add_mul, add_mul, Matrix.smul_mul, Matrix.smul_mul,hh, smul_zero, smul_zero, zero_add, zero_add]
 have hp:z∈realCube zone:=hx.symm ▸ realCube_neg h
 have hu: Fir.shell 4 a z=Fir.shell 4 a q:=by
    rw [hx]; by_cases h:q=0
    · simp [h]
    rw [shell_inv 4 a (hx ▸ hp) (neg_ne_zero.mpr h),shell_inv 4 a hq h,mix_neg _ _ M.property]; simp [prodM,a]
 have he: Fir.skin 4 a z = - Fir.skin 4 a q:=by rw [skin_mix _ _ hp,skin_mix _ _ hq,hu,hx,Fir.mix_neg _ _ M.property, smul_neg]
 have hy:high*boot 4 M z*low= -(high*boot 4 M q*low):=by rw [hh _ hp, hh _ h,he, show Fir.zen (- Fir.skin 4 a q)= - Fir.zen (Fir.skin 4 a q) from (by nth_rw 1 [←neg_one_smul ℂ (Fir.skin 4 a q)]; rw [zenS,neg_one_smul]), mul_neg,neg_mul,op_kron_neg]
 cases b; · change high*(1-boot 4 M z)*low= -(high*(1-boot 4 M q)*low); rw [mul_sub,mul_one,mul_sub,sub_mul,sub_mul,mul_one, capital_o,zero_sub, zero_sub, hy]
 exact hy
lemma Capital (b:Bool) (w:Plane):let U:= pilotS M b; high*U.2.2.val v w*low =0:=by
 intro X; let f:= fun v:Plane=> Crossbar b M v; let P:=postF X blister; have hp:AptK f P:=(kiosk_P M b).geomF blister
 let L:= -ContinuousLinearMap.id ℝ Plane
 have hx: pre P L= minusF P :=(hp.preC L|>.equal ?_).unique hp.negS
 · have he: P.2.2.val (-v) (-w)= -(P.2.2.val v w):=congrArg (fun z:Ole Plane Pal=> z.2.2.val v w) hx
   simp only [map_neg,ContinuousLinearMap.neg_apply,neg_neg] at he; apply (smul_right_injective (M:=Pal) (by norm_num:(2:ℂ)≠0)); change (2:ℂ) • P.2.2.val v w= _; rw [two_smul, ← sub_neg_eq_add, ← he,sub_self]; simp
 filter_upwards [buoy_l] with x h; exact ford M x (base_subset_realCube zone_pos h) b
lemma Star_p (b:Bool): let P:=pilotS M b; baseF b*P.2.1 v*baseF b=0:=by
 intro P; rw [←corner_0 M b]; apply starBlock_P (binor M b) P (kiosk_P ..); exact (palP M b).mono fun i h=> h.1.eq
end Loden
end Lenten
end YM.CF.TableF
end
