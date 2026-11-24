import Velour.Organza.Gauze
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

/-- The one domain at S: every energy price. -/
def muslin : Submodule ℂ H.space:= ⨅ n:ℕ, LinearMap.range (S.gauze ^ n).toLinearMap
local notation "R" => S.gauze
local notation "D" => S.muslin

lemma muslin_exhibits (x:H.space) : x ∈ D ↔ ∀ n:ℕ, ∃ y, (R^n) y=x:=Submodule.mem_iInf _

lemma muslin_exhibit (x:D)(n:ℕ):∃ y, (S.gauze^n) y=x.val:=(S.muslin_exhibits _).mp x.property n

lemma gauze_power_inj (n:ℕ): Injective (S.gauze^n):=by
 induction n with
 | zero=> rw [pow_zero]; exact injective_id
 | succ n ih=> rw [pow_succ]; exact ih.comp S.gauze_injective

private noncomputable def weigh (n:ℕ)(x:D): H.space:= (S.muslin_exhibit x n).choose
private lemma weighback (n:ℕ)(x:D): (R^n) (S.weigh n x)=x.val:= (S.muslin_exhibit x n).choose_spec

private lemma knit (n:ℕ)(x:D) : S.weigh n x ∈ S.muslin:= by
 refine (S.muslin_exhibits _).mpr fun m=> ⟨S.weigh (n+m) x, S.gauze_power_inj n ?_⟩
 rw [←mul_apply_eq_comp,← pow_add, S.weighback,S.weighback]


def weight (n:ℕ): D →ₗ[ℂ] D where
 toFun x:= ⟨S.weigh n x,S.knit n x⟩
 map_add' x y:= Subtype.ext (S.gauze_power_inj n (show (R^n) (S.weigh n (x+y))=
     (R^n) (S.weigh n x+S.weigh n y) from by rw [map_add,S.weighback,S.weighback,S.weighback]; rfl))
 map_smul' c x:= Subtype.ext (S.gauze_power_inj n (show (R^n) (S.weigh n (c • x))=
     (R^n) (c • S.weigh n x) from by rw [map_smul,S.weighback,S.weighback]; rfl))
local notation "B" => S.weight

lemma weight_cancel (n:ℕ)(v:D):
   (S.gauze^n) (S.weight n v).val=v.val:= S.weighback n v
@[simp] lemma weight0 (v:D): S.weight 0 v=v := by
 have h:=S.weight_cancel 0 v; rw [pow_zero] at h; exact Subtype.ext h
lemma weight_div (n m:ℕ)(v:D): S.weight n (S.weight m v)=S.weight (m+n) v:=by
 ext1
 refine S.gauze_power_inj (m+n) ?_
 rw [S.weight_cancel, pow_add, mul_apply_eq_comp,S.weight_cancel,S.weight_cancel]



lemma weight_mono {n m:ℕ}(p:n≤m)(v:D) :
 ‖S.weight n v‖≤ ‖S.weight m v‖:=by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_add_of_le p
  change ‖(B _ v).val‖≤ ‖(B _ v).val‖
  rw [←S.weight_cancel r (B n v),S.weight_div]
  exact ((R^r).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
     (by
       by_cases h:r=0
       · rw [h,pow_zero]; exact ContinuousLinearMap.opNorm_le_bound _ (by simp) (by intro; rw [one_mul,one_apply_eq_self])
       -- submultiplicative ring maybe not NormOneClass (empty H)
       exact (norm_pow_le' _ (Nat.pos_of_ne_zero h)).trans (pow_le_one₀ (norm_nonneg _) S.gauze_norm)))
lemma muslin_cure (t:ℝ≥0)(ht:0<t)(x:H.space):
  S.E t x ∈ S.muslin := by
   refine (S.muslin_exhibits _).mpr fun n=> ?_
   obtain ⟨Z,z⟩:= S.heat_scale t ht n
   exact ⟨Z x, by rw [z,mul_apply_eq_comp]⟩

lemma muslin_dense : Dense (S.muslin : Set H.space):=
  (S.whole 1).mono (by rintro _ ⟨x,rfl⟩;exact S.muslin_cure _ zero_lt_one x)

lemma muslin_vac {x:H} (h:∀ t, S.E t x = x) : x∈S.muslin := by
  rw [←h 1]
  exact S.muslin_cure _ zero_lt_one x



/-- A simple way for bounded ops to preserve D. -/
def Sealed (T:H.Op): Prop:= ∀ n:ℕ, ∃U, T * S.gauze^n= S.gauze^n * U
lemma sealed_commute (T:H.Op)(h:Commute T S.gauze): S.Sealed T:=
 fun n=> ⟨T,(h.pow_right n).eq⟩
namespace Sealed
variable {S} {T : H.Op}
lemma safe (h:S.Sealed T) (v:S.muslin) : T v.val∈S.muslin:= by
 rw [S.muslin_exhibits]
 intro n
 obtain ⟨U,u⟩:=h n
 exact ⟨U (S.weight n v).val, by rw [←mul_apply_eq_comp,← u, mul_apply_eq_comp, S.weight_cancel]⟩
end Sealed
/-- Lift. -/
def label (T:H.Op)(h:S.Sealed T): Module.End ℂ S.muslin where
 toFun v:=⟨T v.val,h.safe v⟩
 map_add' v w:=Subtype.ext (map_add T v.val w.val)
 map_smul' z v:=Subtype.ext (map_smul T z v.val)

lemma label_val (T:H.Op)(h:S.Sealed T)(v:D) :
 (S.label T h v).val=T v.val:=rfl


lemma label_lift (T:H.Op)(h:S.Sealed T)(n:ℕ)(U:H.Op)
   (s: T*S.gauze^n=S.gauze^n*U)(v:S.muslin):
 (S.weight n (S.label T h v)).val= U (S.weight n v).val:= by
  apply S.gauze_power_inj n
  rw [S.weight_cancel, S.label_val,←mul_apply_eq_comp,←s,mul_apply_eq_comp,S.weight_cancel]

/-- Quantitative transfer *identity*. Obtain products e.g. on all iterated fields,
and commutations on B; useful also next to composite gauge smears. -/
def Refines (L:Module.End ℂ S.muslin)(s n:ℕ)(M:H.Op) : Prop:=
 ∀ v:D,(S.weight n (L v)).val=M (S.weight (s+n) v).val

lemma label_refines (T:H.Op)(h:S.Sealed T)(n:ℕ)(U:H.Op)
   (s: T*S.gauze^n=S.gauze^n*U) : S.Refines (S.label T h) 0 n U := by
 rw [Refines,zero_add]
 exact S.label_lift T h n U s

lemma weight_refines (m n:ℕ) : S.Refines (S.weight m) m n 1:= by
 intro v
 rw [S.weight_div]; rfl
namespace Refines
variable {S} {T U:H.Op} {L N : Module.End ℂ S.muslin} {k l n : ℕ}
lemma bill (h:S.Refines L k n T)(v:S.muslin):‖S.weight n (L v)‖ ≤‖T‖*‖S.weight (k+n) v‖:= by
  change ‖(S.weight n (L v)).val‖ ≤ _; rw [h]; exact T.le_opNorm _
lemma mul (h:S.Refines L k n T) (g:S.Refines N l (k+n) U): S.Refines (L*N) (l+k) n (T*U):=by
 intro x
 change (S.weight n (L (N x))).val= _; rw [mul_apply_eq_comp,h,g, add_assoc]
end Refines

/-- Graph convergence (first-countability not needed). Not D's native subtype topology! -/
def Ruffles {ι} (p:Filter ι) (f:ι→D) (x:D): Prop:=
 ∀ n, Tendsto (fun i=> (B n (f i)).val) p (𝓝 (B n x).val)

namespace Ruffles
variable {S} {ι:Type} {p:Filter ι} {x:S.muslin} {f : ι→S.muslin}
lemma lean_on (x:S.muslin) : S.Ruffles p (fun _=>x) x := fun _=> tendsto_const_nhds
lemma plain (h:S.Ruffles p f x) : Tendsto (fun i=> (f i).val) p (𝓝 x.val):= by
 simpa only [S.weight0] using h 0
/-- graph convergence stable under fixed words (use also varying prices via pointwise heat) -/
lemma reach (h:S.Ruffles p f x)(L : Module.End ℂ S.muslin)(q:∀n,∃k T,S.Refines L k n T):
 S.Ruffles p (fun i=> L (f i)) (L x):= by
  intro n; obtain ⟨m,T,r⟩:=q n
  unfold Refines at r
  simp_rw [r]
  exact (T.continuous.tendsto _).comp (h _)
end Ruffles


/-- D-map closability criterion, adjoint on D. -/
def Faces (L J : Module.End ℂ D): Prop:= ∀ x y:D, inner ℂ (L x).val y.val=inner ℂ x.val (J y).val
namespace Faces
variable {S} {L J M K: Module.End ℂ S.muslin}
lemma mul (h:S.Faces L J)(p:S.Faces M K): S.Faces (L*M) (K*J):= fun x y=> (h (M x) y).trans (p x (J y))

lemma closableCore (h:S.Faces L J){v : ℕ→S.muslin}{y:H.space}
 (p:Tendsto (fun i=> (v i).val) atTop (𝓝 0))
 (q:Tendsto (fun i=> (L (v i)).val) atTop (𝓝 y)): y=0:=by
 have hh (x:S.muslin) : inner ℂ y x.val=0:= by
   have e:= (p.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=(J x).val)))
   rw [inner_zero_left] at e
   exact tendsto_nhds_unique (q.inner (𝕜:=ℂ) tendsto_const_nhds) (e.congr fun i=> (h (v i) x).symm)
 have d₀ : DenseRange (fun x:S.muslin=>x.val):= S.muslin_dense.mono
   (fun x px=>⟨⟨x,px⟩,rfl⟩)
 have t: (fun z:H=>inner ℂ y z)=(fun _=>0):= d₀.equalizer (continuous_const.inner continuous_id) continuous_const (funext hh)
 exact inner_self_eq_zero.mp (congrFun t y)
end Faces



/-- D-preserving heat & translation. -/
def heatL (t:ℝ≥0) : Module.End ℂ S.muslin:= S.label (S.E t) (S.sealed_commute _ (S.gauze_heated t))

lemma heatL_refines (t:ℝ≥0) (n:ℕ) : S.Refines (S.heatL t) 0 n (S.E t):=
 S.label_refines _ _ _ _ ((S.gauze_heated t).pow_right n).eq -- .. 
lemma heatL_faces (t:ℝ≥0): S.Faces (S.heatL t) (S.heatL t):= fun _ _=> by
 change inner ℂ (S.E t _) _=inner ℂ _ (S.E t _)
 rw [← ContinuousLinearMap.adjoint_inner_right,S.sym] -- orientation?
lemma heatL_coe (t:ℝ≥0)(x:D) : (S.heatL t x).val=S.E t x.val:= rfl

lemma heat_breed : Continuous (fun z:ℝ≥0×H.space=>S.E z.1 z.2):=by
  apply continuous_iff_continuousAt.mpr; rintro ⟨t,x⟩
  apply Metric.tendsto_nhds.mpr; intro ε he
  have hz: 0< ε/2:= half_pos he
  have p :=(S.continuousE x).comp (continuous_fst (Y:=H.space)) -- name
  filter_upwards [Metric.tendsto_nhds.mp (continuous_snd.tendsto (t,x)) _ hz,
    Metric.tendsto_nhds.mp (p.tendsto (t,x)) _ hz] with i hi hq
  change dist (S.E i.1 i.2) (S.E t x)<ε
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub _ (S.E i.1 x) _)
  rw [←map_sub]
  rw [← add_halves ε]
  rw [dist_eq_norm] at hi hq
  exact add_lt_add (((S.E _).le_opNorm _).trans_lt
     ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans_lt hi)) hq


lemma Ruffles.warm {ι:Type} {p:Filter ι} {x:D} {f : ι→D}
   (h:S.Ruffles p f x){s:ι→ ℝ≥0} (k:Tendsto s p (𝓝 0)) :
 S.Ruffles p (fun i=>S.heatL (s i) (f i)) x:=by
 intro n
 have Y (i:ι):=S.heatL_refines (s i) n (f i)
 simp_rw [Y, zero_add]
 have g := (S.heat_breed.tendsto _).comp (k.prodMk_nhds (h n))
 rw [show (S.E (0:ℝ≥0) ((B n x).val))=(B n x).val by rw [S.eZero];rfl] at g
 exact g

/-! Mink -/
lemma unit_heat (b:E4)(t:ℝ≥0): Commute (S.unit.translation b) (S.E t):=by
  by_cases h:t=0
  · rw [h,S.eZero];exact Commute.one_right _
  have e:duration t ∈ inside:=dur.mpr (bot_lt_iff_ne_bot.mpr h) -- t⊥?
  change (S.edge _ * S.U _) * S.E t=S.E t*(S.edge _ * S.U _)
  have hu(c): S.U c * S.E t=S.E t*S.U c:= (S.independent t c).symm
  have he(u): S.edge u * S.E t=S.E t*S.edge u:= by
    rw [←S.roots_heat (dur.mp e)]; exact (S.along e u).trans (S.either e u).symm
  rw [mul_assoc,hu,←mul_assoc, he, mul_assoc]


lemma unit_weight (b:E4) : Commute (S.unit.translation b) S.gauze:= S.gauze_unbroken _ (S.unit_heat _)
def liftL (b:E4): Module.End ℂ S.muslin:= S.label _ (S.sealed_commute _ (S.unit_weight b))
lemma liftL_refines (b:E4) (n:ℕ):S.Refines (S.liftL b) 0 n (S.unit.translation b):=S.label_refines _ _ _ _ ((S.unit_weight b).pow_right _).eq
lemma liftL_coe (b:E4)(x:D) : (S.liftL b x).val=S.unit.translation b x.val:= rfl
lemma liftL_add (b c:E4) : S.liftL (b+c) = S.liftL b * S.liftL c:= by
 ext1
 apply Subtype.ext
 change S.unit.translation (b+c) _= S.unit.translation b (S.unit.translation c _)
 rw [←S.unit.sends]; rfl
lemma liftL_zero : S.liftL 0=1:= by
 ext1; apply Subtype.ext
 rw [S.liftL_coe,S.unit.origin];rfl

#print axioms liftL_refines
#print axioms Faces.closableCore
#print axioms Ruffles.warm

