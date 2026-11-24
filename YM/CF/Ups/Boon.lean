import YM.CF.Ups.Beet
import YM.CF.Emu.Well
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
open MeasureTheory Sods Girt Cube Pyx Py Scree Skye Graph
abbrev eyeY:Gaia:=EuclideanSpace.single (3:Axis) (1:ℝ)
def brush(c:Slot)(b:Bool):Wing:= if b then ⟨2,c,1⟩ else ⟨0,c,1⟩
def scout(b:Bool):Gaia:= if b then eyeY else 0
lemma bosh(c i): signW (brush c i)=i ∧ (brush c i).x=c:=by cases i <;> simp [signW,brush,plusHalf]
lemma pencil_non : pencil eyeY 2 0≠0:=by
 have he:(∑ i:Axis,(eyeY i:ℂ) • gammaOp i)=gammaOp 3:=by
    rw [sum_eq_single (3:Axis)]; · simp [eyeY]
    · intro i _ h; simp [eyeY,h,Ne.symm h]
    simp
 have hs: ‖eyeY‖=1:=by simp [eyeY]
 have ht:(minA*gammaOp 3) 2 0=1:=by
    change (minA*gammaOp (Fin.succ (Fin.succ (Fin.succ 0)))) (Fin.succ (Fin.succ 0)) 0=1; rw [minA,Adef]; norm_num [Matrix.mul_apply,SpinIdx, Fin.sum_univ_succ, grading, gammaOp,Matrix.one_apply]; change (1/2:ℂ)+ -(1/2)=0; exact add_neg_cancel _
 unfold pencil gleamV; rw [hs,he,Matrix.smul_apply,ht]; simp [Real.pi_ne_zero]
variable {a:ℕ→ℝ}{N:ℕ→Side}(A:Yard N a)(p:Plot Bool a)(c:Slot)(v:p.atV=scout)(z:p.seat=brush c)
include v z
lemma pennyW: runes p.rho [true,false]= pencil eyeY 2 0:=by
 have ht(x y:Bool):runes p.rho [x,y]=p.rho x y:=by simp [runes,spinC,offer,claps,cites,besideX,cval,extendsU,picks]
 rw [ht,Plot.rho,v,z]; simp_rw [(bosh _ _).1]; simp [frank,brush,scout]
include A
lemma grateK (Y:∀ i,Site (N i)):∀ᶠ j in atTop,node (Y j+wrap _ (p.z j true))≠node (Y j+wrap _ (p.z j false)):=by
 let z(j):=p.z j true-p.z j false; let n(j):ℝ:= (N j).val; let D(j:ℕ):ℤ:=z j 3
 have hp: Tendsto (fun i=> (D i:ℝ)/a i) atTop (𝓝 1):=by
    have he: Tendsto (fun i=>riseX (a i) (z i)) atTop (𝓝 eyeY):=by
       simp_rw [z,←face_z]; simpa only [v,scout,ite_true,Bool.false_eq_true,↓reduceIte,sub_zero] using (p.voyage true).sub (p.voyage false)
    have ht: (eyeY 3)=(1:ℝ):=by simp [eyeY]; -- tune
    exact ht ▸ (((show Continuous (fun i:Gaia=> i (3:Axis)) from PiLp.continuous_apply ..).tendsto _).comp he) -- tune name
 filter_upwards [hp.eventually (gt_mem_nhds (by norm_num : (1:ℝ)< 2)),hp.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num)),A.water.eventually (gt_mem_nhds (show 0<Real.pi/3 by positivity))] with i v ht hs
 have hx:a i>0:=A.pos _
 have hu:0<(D i:ℤ):=by exact_mod_cast (lt_of_lt_of_le (show 0<(D i:ℝ) from (by simpa using ((lt_div_iff₀ hx).mp ht))) le_rfl)
 have he: D i<(N i).val:=by
    have hN: n i>0:= by unfold n; positivity
    have hD: (D i:ℝ)<2*a i:= (div_lt_iff₀ hx).mp v
    change a i*(Real.pi/n i)<_ at hs; field_simp at hs; exact_mod_cast (lt_trans hD (show _ < ((N i).val:ℝ) from (by change _< n i; nlinarith [Real.pi_pos])))
 intro e; have hg:wrap (N i) (z i)=0:=by
    unfold node at e; let L:Lattice.Ratio _ _:= assembly (N i); have h:L.embed (Y i+ _) = L.embed (Y i + _):= add_right_cancel e; have hx: Y i+wrap _ (p.z i true)= Y i+wrap _ (p.z i false):= by rw [←L.embed_parent (Y i+_),h,L.embed_parent]
    unfold z; rw [map_sub,sub_eq_zero]; exact add_left_cancel hx
 have hv:= Int.natAbs_le_of_dvd_ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd (D i) _).mp (congr_fun hg (3:Axis))) hu.ne'; omega
end YM.CF.Emu
