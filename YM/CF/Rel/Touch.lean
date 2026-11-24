import YM.CF.Rel.Bass
import YM.Push.LOOP_COEFFICIENT.LoopSymbol
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev FileM(n:Side)(G:Gauge):= Site n→ SpaceX G n
abbrev te(v: InputZ G n)(i:Site n):InputZ G n:=fun j=> v (j.1+i,j.2)
def tagT(G:Gauge)(i:Site n):InputZ G n→L[ℝ]InputZ G n:=LinearMap.toContinuousLinearMap { toFun:=fun v=> te v i,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
lemma trn (i:Site n)(v: InputZ G n): represent (te v i)= Lattice.translate i (represent v):=by ext1 j; unfold Lattice.translate; simp_rw [Work.F03.represent_link]
abbrev pulseP(k:Site n):=fun i:Site n=> (cell k i)⁻¹
abbrev shapeV(k:Site n)(X:FileM n G):Prop:= ∀ i:Site n,∀ U:Config G n,X i U=pulseP k i * X 0 (Lattice.translate i U)
abbrev Sean (k:Site n)(f:SpaceX G n): FileM n G:=fun i U=> pulseP k i * f (Lattice.translate i U)
lemma pulse_ne (k i:Site n): pulseP k i ≠ 0:=inv_ne_zero (cell_ne k i)
lemma pulse_l (k i j:Site n):pulseP k (i+j)=pulseP k i*pulseP k j:=by simp [pulseP,mul_comm]
@[simp] lemma pulse_z (k:Site n): pulseP k 0=1:=by simp
@[simp] lemma pulse_a (k i:Site n): ‖pulseP k i‖=1:=by simp only [pulseP,norm_inv,legX,inv_one]
lemma Nth (X:FileM n G)(k:Site n)(h: shapeV k X)(he:ContDiffAt ℝ m (satX (X 0)) 0)(x:Site n)(V:Fin m→InputZ G n):
   cake m (satX (X x)) V=pulseP k x * cake m (satX (X 0)) (fun i=> te (V i) x):=by
 let T:ℂ→L[ℝ]ℂ:= (ContinuousLinearMap.lsmul ℝ ℂ (pulseP k x)) -- tune
 let f:=satX (X 0); let J:=tagT G x; have hx:satX (X x)= (T ∘ f) ∘ J:=by
    ext1 v; change X x _= _; rw [h]; change _= T (X 0 (represent (te v x))); rw [trn]; rfl
 have hw:ContDiffAt ℝ (↑m:WithTop ℕ∞) (T ∘ f) (J 0):=by rw [map_zero]; exact T.contDiff.contDiffAt.comp 0 he
 rw [hx,cake]; simp only [_root_.smul_apply]; rw [Push.Uniform.iter_lin_at hw,map_zero,T.iteratedFDeriv_comp_left he le_rfl]; change _ • (T (iteratedFDeriv ℝ m f _ _)) = T (_); unfold cake; rw [_root_.smul_apply,map_smul]; rfl
lemma sumHt(i:Body 2 n)(V: InputZ G n)(x:Site n): sumH G (te V x) i=sumH G V (i.1+x,i.2):=by
 obtain ⟨⟨a,b⟩,rfl⟩:= (ŧ n).surjective i; change dColor _ _ _ _ (a,plaquette b)=dColor _ _ _ _ (a+x,plaquette b); rw [← fundamental,← fundamental]
 have hp(o:Site n)(W:Walk):linkSum (collect G (te V x)) o W=linkSum (collect G V) (o+x) W:=by induction W generalizing o with
   | nil=>rfl
   | cons i W H=> rcases i with ⟨i,b⟩; cases b <;> simp [linkSum,collect,te,Step.used,Step.vec,H,sub_eq_add_neg,add_assoc,add_comm x] -- tune
 exact hp .. -- tune
end YM.CF.Rel
