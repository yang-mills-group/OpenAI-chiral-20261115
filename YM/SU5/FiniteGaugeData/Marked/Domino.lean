import YM.SU5.FiniteGaugeData.Marked.Core
import YM.CF.Vp929.Borel.Tape

/-!
# `cash` calculus for the repeated reflection estimate.
Factors are multiplied regardless of the sign of the interacting density;
independence used here is only under the raw integration law AND the
reconstruction at that period. In particular there is ONE reconstruction.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

section factor
variable {n:Side} {S T : Support (More n)} {w : ℕ} {l:Loom n}


structure Levy (S : Support (More n)) (f: Fields n→ℝ): Prop where
  env : Envelope f
  area (x y:Fields n) : Agrees S x.1 y.1 → Agrees S x.2 y.2 → f x=f y
namespace Levy
variable {f g : Fields n → ℝ} (p:Levy S f) (t:Levy T g) (v:Measurable l) (d:LoomLaw l w)
include p v
lemma funded : Integrable (f ∘ drawn l) (city n) := Env.integrableX (Env.along p.env (drawn_m l v)) _
include t
lemma funded2 : Integrable ((f ∘ drawn l)*(g ∘ drawn l)) (city n) :=
  Env.integrableX (env_mult (markfee f p) (markfee g t)) _
where
  markfee (f:Fields n→ℝ){S}(p:Levy S f) : Envelope (f ∘ drawn l) := Env.along p.env (drawn_m l v)

omit t
/-- Mean local bill holding U fixed. -/
def tariffAt (l:Loom n) (f:Fields n→ℝ) (U:Pane n) := ∫ i, f (drawn l (U,i)) ∂depot n
lemma tariffAt_m : Measurable (tariffAt l f) :=
  (StronglyMeasurable.integral_prod_right (f:=fun (x:Pane n) y=> f (drawn l (x,y)))
    ((p.env.meas.comp (drawn_m l v)).stronglyMeasurable)).measurable
include d
lemma tariffAt_local : Lattice.LocalOn (Lattice.halo w S) (tariffAt l f) := by
  intro x y h
  calc
    _ = ∫ i, f (x,l (y,i)) ∂depot n := loom_integral d v x y S h (fun W=> f (x,W))
      (p.env.meas.comp (measurable_const.prodMk measurable_id)) (fun u z v=> p.area _ _ (fun _ _ _=>rfl) v)
    _ = _ := integral_congr_ae (Eventually.of_forall fun i=> p.area _ (y,l (y,i)) (agrees_mono h (halo_subset w S)) (fun _ _ _=>rfl))

omit p v d
private def store (S:Support (More n)) (x:LEData S):Pane n := fun i=> if h: i.1∈ S ∧ i.1+step i.2∈ S then x ⟨i,h⟩ else 1
private lemma store_m (S:Support (More n)) : Measurable (store S) := by
  apply measurable_pi_lambda; intro i; unfold store; split; exact measurable_pi_apply _; exact measurable_const
include p
private lemma stored (y x:Pane n): f (y,store S (extract S x)) = f (y,x) := p.area _ _ (fun _ _ _=>rfl)
  (fun i h t=> by change store S (extract S x) i=x i; unfold store; rw [dif_pos ⟨h,t⟩]; rfl)
include t v d
lemma inside (e:∀ i∈ S,∀ j∈ T,w < separation i j) (y:Pane n) :
    tariffAt l (f*g) y = tariffAt l f y * tariffAt l g y := by
  let F(X:LEData S):=f (y,store S X)
  let G(X:LEData T):=g (y,store T X)
  let h(z:Ids n):= drawn l (y,z)
  have V : Measurable h:=(drawn_m l v).comp (measurable_const.prodMk measurable_id)
  have H(X: Fields n→ℝ)(S:Support (More n))(q:Levy S X):
      (fun z=> X (y,store S z)) ∘ (fun z=> extract S (l (y,z))) = X ∘ h :=
    funext fun _=> stored q y _
  have he:IndepFun (f ∘ h) (g ∘ h) (depot n):= by
    rw [←H f S p,←H g T t]
    exact (d.splitS S T e y).comp (p.env.meas.comp (measurable_const.prodMk (store_m S))) (t.env.meas.comp (measurable_const.prodMk (store_m T)))
  exact he.integral_mul_eq_mul_integral (p.env.meas.comp V).aestronglyMeasurable (t.env.meas.comp V).aestronglyMeasurable

omit p t v d
private def keys (S:Support (More n)):Finset (reach n):= univ.filter (fun i=> i.1 ∈ S) -- enough to retain outgoing links
private lemma keys_disj (p:Disjoint S T): Disjoint (keys S) (keys T) :=
  Finset.disjoint_left.mpr fun _ i j=> Finset.disjoint_left.mp p ((mem_filter.mp i).2) ((mem_filter.mp j).2)

include p t v d
lemma factor (e:∀ i∈ S,∀ j∈ T,2*w < separation i j):
    (∫ x,(f ∘ drawn l) x*(g ∘ drawn l) x ∂city n)= (∫ x,f (drawn l x) ∂city n) * ∫ x,g (drawn l x) ∂city n := by
  have hd : Disjoint (Lattice.halo w S) (Lattice.halo w T):= by
    apply Finset.disjoint_left.mpr; intro i h k
    obtain ⟨x,hx,r⟩:= halo_spec.mp h; obtain ⟨y,hy,s⟩:=halo_spec.mp k
    have he:= e _ hx _ hy; have ht:= Lattice.separation_triangle x i y
    rw [separation_comm i y] at ht; omega
  have he:=p.tariffAt_m v; have h':=t.tariffAt_m v
  have V {S:Support (More n)} (X:Pane n→ℝ)(p:Lattice.LocalOn S X)(A B:Pane n)(i:∀ j∈keys S,A j=B j) : X A=X B:= p _ _ fun j x _=> i j (mem_filter.mpr ⟨mem_univ _,x⟩)
  have hp:IndepFun (tariffAt l f) (tariffAt l g) (Wilson.prior SU.group (More n)) :=
    VolumeCape.Borel.independenceTape SU.group.probHaar he h'
      (V _ (tariffAt_local p v d)) (V _ (tariffAt_local t v d)) (keys_disj hd)
  unfold Scree.city
  rw [integral_prod (fun x=> (f ∘ drawn l) x * _) (funded2 p t v), integral_prod (fun x=> f _) (funded p v), integral_prod (fun x=> g _) (funded t v)]
  change (∫ x, tariffAt l (f*g) x ∂_)=(∫ x, tariffAt l f x ∂_) * ∫ x, tariffAt l g x ∂_
  simp_rw [inside p t v d (fun i u j z=> lt_of_le_of_lt (by omega : w ≤ 2*w) (e i u j z))]
  exact hp.integral_mul_eq_mul_integral he.aestronglyMeasurable h'.aestronglyMeasurable
end Levy

lemma duty {b:Bool} {f:Mark n} (p:AtSupport b S f) : Levy S (fun x=> ‖f x‖) :=
  ⟨Girt.pole_w f _ continuous_norm p.env, fun _ _ u v=> congrArg norm (p.dep _ _ u v)⟩

lemma cash_turn {f:Mark n} {u e:ℝ} {r:ℕ} (A:Roof n u e r l) (i:Axis)(s:ℤ):
    cash l (reflMark i s f) = cash l f := by
  unfold cash
  rw [← (Advance.reflOrbit_mp (N:=n) i s).integral_comp' (fun x=> ‖f (drawn l x)‖)]
  apply integral_congr_ae; filter_upwards [Advance.roof_move l i s A] with x h
  rw [h,reflMark,theta_fee]

lemma cash_mult {f g:Mark n} {a b:Bool} (h:AtSupport a S f)(p:AtSupport b T g)
    (u:Measurable l) (v:LoomLaw l w) (t:∀ i∈S,∀ j∈ T,2*w<separation i j) :
    cash l (f*g) ≤ cash l f * cash l g := by
  have he:= duty h; have hp:= duty p
  unfold cash
  apply (Levy.factor he hp u v t).le.trans'
  refine integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) (Levy.funded2 he hp u) (Eventually.of_forall fun x=>?_)
  exact norm_mul_le ..
end factor

namespace Wick
variable {K:Calibration} {H:Histories K} {m:Side} {t:ℕ} (p: Wick H m t) (i:Axis)(z:ℤ)
local notation "S" => band (K.c m) i (Heat.gaugeShift K.B z) K.ℓ
local notation "μ" => H.loom m 0
local notation "R" => reflMark i (Heat.gaugeShift K.B z)
include p
lemma domino {f:Mark (K.c m)} (w:AtSupport false S f):
    cash μ (R f * f) ≤ cash μ f ^ 2 := by
  suffices he: ∀ x∈(S).image ((plane i (Heat.gaugeShift K.B z)).anon (K.c m)), ∀ y∈S, 2*K.w < separation x y by
    have hp:= cash_mult (w.refl i (Heat.gaugeShift K.B z)) w p.loom_m (H.lawn m p.allowed.1 0) he
    let A:=p.shot.sharp.roof 0
    rw [cash_turn A.paid] at hp
    rw [sq]; exact hp
  intro x h y v; have he:= margin_separate i (Heat.gaugeShift K.B z) K.buffer x y h v
  omega
end Wick
end YM.CF.Buffered.Afterglow
