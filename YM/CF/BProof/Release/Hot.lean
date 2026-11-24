import YM.CF.BProof.Gauss.Drive
import YM.CF.BProof.Release.Locale
import YM.CF.BProof.Release.Limit

/- The truncation uses square event pit at z=s_y^4. Buying Hold at the indicated
PL settings should NOT depend on Period; inverse norm permits near regardless of severe x. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.hot
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision RealM SignScalar
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
abbrev radius (y:ℝ) := scaleY y^2
abbrev trunc (y:ℝ) := radius y^2
variable (K:Chart G) (A:Pub G)
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}{M:ℕ}(θ κ:ℝ){P y q w:ℝ}(X:Beam c P Y.short M y)
-- M param shared. hold κ small paid. definition uses U.time which is analytic radius estimate, depends on `Base` but actually only dim. express bound comparisons external.
structure Warm (c:Clip)(d M R:ℕ)(y κ L:ℝ) : Prop where
 k : 0<κ
 t : K.C*κ ≤ 1
 d₀ : scaleD κ y≤ K.radius
 on_plane : scaleD κ y+xi y≤ thresh y/16
 grant : thresh y≤ A.radius
 beam_to : g y*((SU.group.lieDim+1:ℕ)*(Beam.cost c d R*radius y)) ≤ A.radius
 reach : (Beam.guard d:ℝ)*(L*scaleY y)^2 ≤ trunc y
 pos : 0≤L -- L = T sup inv cost
 wallet : 1≤trunc y
 scarcity : 2*xi y≤ κ*thresh y
abbrev bid := (Beam.tide c Y.short)⁻¹ * X.time
abbrev Book := Warm K A c Y.short M X.horizon' y κ (bid Y X)
variable (H:Room Y M)(u:T.Bounds c w P q)(h: θ∈Set.Icc (1/2) 2)(Z:Finset Y.Col)(x:Plan Y)
-- x v coordinates condition at z
abbrev pin (Z: Finset Y.Col)(x:Plan Y)(b:Y.Col):= Function.curry (Beam.drive T θ X Z x) b
abbrev entry (x:Plan Y)(b:Y.Col) := Function.curry x b
abbrev Field := Y.Col → Pub.Stamp G Y.Apt
def Fares (Y:Yard s)(y:ℝ)(x:Plan Y):= ∀ b, entry Y x b∈ Day.pit (trunc y)
def tape (T:PathData G) (θ:ℝ) (X:Beam c P Y.short M y)(Z:Finset Y.Col)(x:Plan Y) : Y.Branch:= g y • lowerMap Y (Beam.drive T θ X Z x)
lemma tape_grant (b:Y.Col)(i:Y.Apt) : tape Y T θ X Z x (b,i)= Pub.grant (g y) (Pub.key («G»:=G) (pin Y T θ X Z x b) i):=rfl
@[fun_prop] lemma tape_m : Measurable (tape Y T θ X Z):=by
 have hp:(tape Y T θ X Z)= fun x=> ((g y) • (lowerMap Y).toLinearMap) (((Beam.ζ T θ X Z).mulVecLin) x):=rfl -- wrong syntax `equiv •`?
 rw [hp]; fun_prop
@[simp] lemma depth (x:Plan Y)(b:Y.Col): Gauss.fans Y (lowerMap Y x) b=Day.ar (entry Y x b):= (Roll.tally₀ Y x b).symm
lemma venues (b:Y.Col)(r:ℝ)(p: entry Y x b∈ Day.pit (r^2))(v:0≤r) (i: Roll.Place Y): |x (b,i)|≤ r := by
 have hp : x (b,i)^2 ≤ r^2:= (Finset.single_le_sum (f:=fun i:Roll.Place Y=>x (b,i)^2) (fun _ _=>sq_nonneg _) (mem_univ _)).trans p
 nlinarith [sq_abs (x (b,i))]
lemma fairs {y:ℝ}(p:Fares Y y x)(i:Stamp Y):|x i| ≤ radius y:= venues Y x _ _ (p i.1) (sq_nonneg _) i.2
variable (a:Book K A Y κ X)
include H h u a
-- regular: x_i bound via all matrix column indices it reads. version without p for healthy.
lemma beam_cost (b:Y.Col)(z:ℝ)(k:0≤z)(i:Y.Apt)(v:∀ j:Stamp Y,(Gauss.base Y).N b j.1 X.horizon' → |x j|≤z) :
    ‖tape Y T θ X Z x (b,i)‖ ≤ g y*((SU.group.lieDim+1:ℕ)*(Beam.cost c Y.short X.horizon'*z)):=by
 let V:= Beam.cost c Y.short X.horizon'*z; let B:=Gauss.base Y; have hx (t:Gauss.Color)(j:Stamp Y)(h: Beam.ζ T θ X Z (b,i,t) j≠0) : B.N b j.1 X.horizon' :=by
    by_contra p; exact h ((Beam.ζ_v T θ X H).door _ _ _ p)
 have he:=coin_pos y (-1/2) 0 0; let W:=lowerMap Y (Beam.drive T θ X Z x) (b,i)
 have hp : 0≤ Beam.tide c Y.short:= (norm_nonneg _).trans ((Beam.measured T θ X H u h Z).2.2.1); have hP :0≤ V:=by unfold V Beam.cost; positivity
 have hh: ‖W‖^2≤ SU.group.lieDim*V^2:=by
   have hd(t:Gauss.Color): ‖W t‖≤V:= beam_charge (Beam.ζ T θ X Z) (b,i,t) z _ k (Beam.sup_meter T θ X Z H u h _) (fun i w=> v i (hx _ i w))
   rw [PiLp.norm_sq_eq_of_L2]; apply le_trans (b:=∑ i:Gauss.Color,V^2) (sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hd i) _)); rw [sum_const]; simp [Gauss.Color,nsmul_eq_mul]
 change ‖g y • W‖ ≤_; rw [norm_smul,Real.norm_of_nonneg he.le]; apply mul_le_mul_of_nonneg_left _ he.le; push_cast; change ‖W‖ ≤ ((SU.group.lieDim:ℝ)+1)*V; apply le_of_sq_le_sq _ (by positivity); exact hh.trans (by rw [mul_pow _ V]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); nlinarith [show 0≤ (SU.group.lieDim:ℝ) by positivity]) -- tune teeth
lemma recipient (p:Fares Y y x)(b:Y.Door): ‖tape Y T θ X Z x b‖≤ A.radius:= (beam_cost K A Y T θ κ X H u h Z x a b.1 _ (sq_nonneg _) b.2 (fun i _=> fairs Y x p i)).trans a.beam_to -- tune arg includes
lemma admitted (p:Fares Y y x) (b:Y.Col)(i:Y.Apt): Pub.key («G»:=G) (pin Y T θ X Z x b) i∈ Pub.input A (g y):= mem_ball_zero_iff.mpr ((recipient K A Y T θ κ X H u h Z x a p (b,i)).trans_lt A.holds)
-- v all nonsevere from support ∏. inverse doesn't charge severe w.
omit a -- lounge needs K A? omit later.
private lemma inv_row (i:Stamp Y)(v:i.1∈ Z)(j:Stamp Y): (Beam.ζ T θ X Z)⁻¹ i j=(1:Pool (Stamp Y)) i j:=by
 let t:= Beam.ζ T θ X Z; have he:t*t⁻¹=1:=t.mul_nonsing_inv (IsUnit.mk0 _ (Beam.bright T θ X Z H u h).ne') -- tune
 have hx:(t*t⁻¹) i j=(t⁻¹) i j:=by
   rw [Matrix.mul_apply, sum_eq_single i]; unfold t; rw [Beam.held T θ X H Z i i v,Matrix.one_apply_eq,one_mul] -- tune
   intro k hk he; unfold t; rw [Beam.held T θ X H Z _ _ v,Matrix.one_apply_ne (Ne.symm he),zero_mul]; simp
 exact hx.symm.trans (congrFun (congrFun he i) j)
private lemma inv_closed (i:Stamp Y)(v:i.1∉ Z)(j:Stamp Y)(hj:j.1∈Z): (Beam.ζ T θ X Z)⁻¹ i j=0:=by
 have hx:j≠i:= fun p=>v (p ▸ hj); have hT:=(Beam.measured T θ X H u h Z).1.inv; have he: (Beam.ζ T θ X Z)⁻¹ i j=(Beam.ζ T θ X Z)⁻¹ j i:= by simpa using (hT.apply _ _)
 rw [he, inv_row Y T θ X H u h Z j hj i, Matrix.one_apply_ne hx]
lemma stable (b:Y.Col)(p:b∈Z) : pin Y T θ X Z x b= entry Y x b:= funext fun i=> X.still T θ Z H x _ p
abbrev doors (b:Y.Col) := A.vault (scaleD κ y) (g y) (Locale.A Y y b) (pin Y T θ X Z x b)
omit H h u
include a
lemma scaleA : K.C*(scaleD κ y) ≤ thresh y:= by rw [scaleD, ← mul_assoc]; exact (mul_le_mul_of_nonneg_right a.t (coin_pos ..).le).trans_eq (one_mul _)
lemma plane (j:Y.Col)(v:doors A Y T θ κ X Z x j)(i:Y.Apt): ‖tape Y T θ X Z x (j,i)‖≤ thresh y:= (A.identify K _ _ _ (v i) a.d₀ ((scaleA K A Y κ X a).trans a.grant)).trans (scaleA K A Y κ X a)
include H h u
lemma reverse (p:∀ b∉ Z, doors A Y T θ κ X Z x b)(b:Y.Col)(hp:b∉ Z): entry Y x b∈ Day.pit (trunc y):=by
 let t:= Beam.ζ T θ X Z; let w:= Beam.drive T θ X Z x; have he:t⁻¹ *ᵥ w=x:=by unfold w Beam.drive; change t⁻¹ *ᵥ (t *ᵥ x)=_; rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ (Beam.bright T θ X Z H u h).ne'),one_mulVec] -- tune
 have hg:=coin_pos y (-1/2) 0 0; have hx(i:Roll.Place Y)(j:Stamp Y)(hj:t⁻¹ (b,i) j≠0): |w j|≤ scaleY y:= by
   have hj':j.1 ∉ Z:= fun p=> hj (inv_closed Y T θ X H u h Z (b,i) hp j p); let W:= lowerMap Y w (j.1,j.2.1); have ht:= plane K A Y T θ κ X Z x a j.1 (p _ hj') j.2.1
   change ‖g y • W‖ ≤_ at ht; rw [norm_smul, Real.norm_of_nonneg hg.le, show thresh y=g y* scaleY y by unfold g thresh scaleY; rw [coin_mul]; ring_nf,mul_le_mul_iff_right₀ hg] at ht; exact (PiLp.norm_apply_le W j.2.2).trans ht
 let V:= bid Y X* scaleY y
 have hv(i:Roll.Place Y) : |x (b,i)|≤ V:= (by rw [←he]; exact beam_charge t⁻¹ (b,i) _ _ (coin_pos ..).le (Beam.fast T θ X Z H u h _) (hx i))
 refine le_trans (b:=_) (?_ : Day.ar (entry Y x b)≤(Beam.guard Y.short:ℝ)*V^2) a.reach; unfold Day.ar; apply le_trans (b:=∑ _:Roll.Place Y,V^2) (sum_le_sum (fun i _=>?_)); rw [sum_const]; exact le_of_eq (by simp [Beam.guard,Roll.Place,nsmul_eq_mul,Apt,TAxis,Gauss.Color]); rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv _) _
end YM.CF.BProof.Release.hot
