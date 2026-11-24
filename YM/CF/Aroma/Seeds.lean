import YM.CF.Ember.Quote
import YM.CF.Rush.Rill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N : Side}
def dialH (q:Momentum)(x:Site N):= mode q (natural x)
structure Tide (N:Side)(q:Momentum) where
 phys:physical q
 live(w:Cover): mode q ((More N).val • w)=1
 σ:Equiv.Perm (Site N)
 cost(k:Site N):∃ w:Cover, spoon (mel k) q=mel (σ k)+reciprocal w
def opp {p:Momentum}(F:Tide N p): Tide N (-p):= by -- def
 refine ⟨by unfold physical; rw [star_neg,F.phys],fun x=>by rw [mode_negate _ F.phys,F.live,star_one],F.σ.symm,fun k=>?_⟩
 obtain ⟨x,hx⟩:=F.cost (F.σ.symm k); rw [Equiv.apply_symm_apply] at hx; refine ⟨-x,?_⟩
 unfold spoon at *; rw [show reciprocal (-x)=-reciprocal x from ?_]; swap; · ext i; simp [reciprocal]
 linear_combination (norm:=abel) -hx
def tide_pos (a:Axis) : Tide N (spark a (pinch N)):=by -- def
 let S:= advance (N:=N) a; let x:=pinch N; have hx:0<x:=pinch_pos _
 refine ⟨by simp [physical,spark_star],?_,S,?_⟩
 · intro w
   unfold mode spark; simp only [Pi.smul_apply,smul_eq_mul,Lattice.step_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,sum_ite_eq',mem_univ,ite_true]
   push_cast; rw [show Complex.I * ((pinch N:ℂ)*_)= (w a:ℂ)*(2*Real.pi*Complex.I) from ?_,Complex.exp_int_mul, Complex.exp_two_pi_mul_I,one_zpow]
   push_cast; simp [nsmul_eq_mul,More,pinch]; field_simp -- tune
 intro k
 have he(u:Per N): BZ.phase (principal (u+1))=BZ.phase (principal u+2*x):=by
   unfold BZ.phase; push_cast; rw [add_mul,Complex.exp_add]; push_cast
   suffices hf : BZ.phase (winding (u+1))=BZ.phase (winding u)*BZ.phase (2*x) by
     rw [←wind_eq, ←wind_eq] at hf; simpa only [BZ.phase,Complex.ofReal_mul,Complex.ofReal_ofNat] using hf
   let r:=u.val; let v:= r+1
   have hr:(u+1).val=v%N.val:=by rw [←ZMod.natCast_zmod_val u, ←Nat.cast_one (R:=Per N),←Nat.cast_add, ZMod.val_natCast]
   have hv:v≤N.val:= ZMod.val_lt u
   rcases hv.eq_or_lt with hp|hp
   · rw [hp,Nat.mod_self] at hr
     have hz:winding (u+1)+2*Real.pi=winding u+2*x:=by
       have hh: (r:ℝ)+1= (N.val:ℝ):=by exact_mod_cast hp
       rw [tone,tone,hr,payH (N:=N)]; simp only [Nat.cast_zero,mul_zero,zero_add,one_mul]; change x+ 2*((N.val:ℝ)*x)= (2*r+1)*x+2*x; nlinarith -- tune
     have hk:=congr_arg BZ.phase hz; unfold BZ.phase at hk; push_cast at hk; simp only [add_mul,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one] at hk; unfold BZ.phase; push_cast; exact hk
   rw [Nat.mod_eq_of_lt hp] at hr; rw [tone,tone,hr]; simp only [v,r, Nat.cast_add, Nat.cast_one]; rw [show ((2:ℝ)*(u.val+1)+1)*pinch N=(2*(u.val:ℝ)+1)*pinch N+2*x by unfold x; ring]
   generalize (2*(u.val:ℝ)+1)*pinch N=y; unfold BZ.phase; push_cast; rw [add_mul,Complex.exp_add]
 obtain ⟨i,hi⟩:∃ i:ℤ, (pm k a)+2*x= pm (S k) a+2*Real.pi*i:=by
   have hf: pm (S k) a=Lat.principal (k a+1):=by simp [pm,S,advance]
   have hh := league (x:=pm k a+2*x) (y:=-pm (S k) a) (by rw [neg_neg,hf]; exact (he (k a)).symm); simpa using hh
 let z:Cover:= i • Lattice.step a; refine ⟨z,?_⟩; ext1 j; by_cases hv:j=a
 · subst j; have ht:=congr_arg (fun x:ℝ=>(x:ℂ)) hi; push_cast at ht; unfold spoon mel; simp only [z,spark,reciprocal,tmap,Lattice.step_apply, ite_true, Pi.add_apply, Pi.smul_apply,smul_eq_mul,mul_one, zsmul_eq_mul,Int.cast_mul,Int.cast_id,Int.cast_one, Pi.mul_apply,Pi.intCast_apply]; unfold x at ht; linear_combination ht
 simp [spoon,spark,hv,z,reciprocal,S,advance,Lattice.step_apply,mel,tmap,pm]
namespace Tide
variable {q:Momentum}(F:Tide N q)
include F
lemma money (t:Cover): dialH q (wrap (More N) t)=mode q t:=by
 nth_rw 2 [← carrying (More N) t]; rw [mode_shift,F.live,mul_one]; rfl -- tune
lemma fresh (x:Site (More N)) : dialH q x= mode q (lift x):=by rw [← F.money,wrap_lift]
lemma plusT (x:Site (More N))(t:Cover):dialH q (x+wrap (More N) t)=dialH q x*mode q t:=by nth_rw 1 [← nat_true x]; rw [←map_add,F.money,mode_shift]; rfl
lemma wages (k:Site N)(x: Cover): mode (mel (F.σ k)) x = mode (mel k) x*mode q (2 • x):=by
 obtain ⟨w,hw⟩:= F.cost k
 rw [←mode_scale,two_smul, ← mode_phase, show mel k+(q+q)=_ from hw, mode_phase,mode_periodic,mul_one]
lemma door (x k:Site N): frequency (F.σ k) x= frequency k x * mode q (2 • natural x):=by simp_rw [←freq_mode,F.wages]
end Tide
end YM.CF.Aroma
