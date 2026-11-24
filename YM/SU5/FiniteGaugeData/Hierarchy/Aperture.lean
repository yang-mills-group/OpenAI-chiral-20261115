import YM.SU5.FiniteGaugeData.Hierarchy.Glass
/-! # General Buffered reflection using the direct PSD resource on aligned planes -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Heat
variable (a:Axis) (t z:ℤ)
local notation "W"=> GridStep Λ l
local notation "η"=> reserve Λ l
abbrev Ahead (a:Axis) (z:ℤ) (r:ℕ) (S: Finset Cover): Prop:= ∀ x∈S, z + (r:ℤ) ≤ x a
lemma ahead_union {r:ℕ}(p:Ahead a t r S)(q:Ahead a t r T): Ahead a t r (S∪T):=fun i e=> (mem_union.mp e).elim (p i) (q i)
lemma ahead_grid (p: Ahead a t (reserve Λ l) S) : Ahead a ((Λ.R.L.val:ℤ)*t) η (GridStep Λ l S) := by
  intro y v; obtain ⟨x,u,r⟩:= mem_biUnion.mp v; obtain ⟨k,s,rfl⟩:= mem_image.mp u; obtain ⟨x,h,rfl⟩:= mem_image.mp r
  specialize p k s; let ℓ:= Λ.R.L.val; let d:= gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
  have he : -((ℓ*d:ℕ):ℤ) ≤ x a:= (box_test.mp h).1 a; have hv:((reserve Λ l):ℤ)+↑(ℓ*d)≤ (ℓ:ℤ)*(reserve Λ l:ℤ):= by exact_mod_cast (margin_step (Journey.prepared Λ l) Λ.R.coarse)
  rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; change (ℓ:ℤ)*t+_≤ _+(ℓ:ℤ)*_; nlinarith
-- effective native buffer separates far enough on every step
private lemma bill_margin : spaceBill Λ l < 2*(reserve Λ l) := by
  let r:= aliasLaw Λ; let u:= distanceLaw l; let L:=Λ.R.L; have e:0<L.val:= L.property
  unfold spaceBill Journey.reserve r₃ r₁ Advance.nearZero; nlinarith -- unfold size and *
lemma ahead_split (p:Ahead a t (reserve Λ l) S)(q:Ahead a t η T): Range (spaceBill Λ l) (refract a t S) T:=by
  intro x hx y hy z; obtain ⟨k,z',e⟩:=mem_image.mp hx; subst x; have hv:= (box_test.mp z).2 a; rw [Pi.sub_apply,fling_move,if_pos rfl] at hv; have h:= p k z'; have r:= q y hy; have he:= bill_margin (Λ:=Λ) (l:=l); omega

-- E.s on Family even supported (narrow Singlet not needed); AHEAD.
private lemma often (K:Calibration) (r:ℕ)(p:Ahead a z r S): ∀ᶠ m:Side in atTop, region S (K.c m) ⊆ band (K.c m) a z r:=by
  classical
  have hx :∀ᶠ m:Side in atTop,∀ x∈ S,x a + r≤ z+(K.c m).val:=by
    rw [S.eventually_all]; intro x h; let b:= x a + r - z; filter_upwards [(c_grows K).eventually_ge_atTop b.toNat] with m w; change _≤ (K.c m).val at w; unfold b at w; omega
  filter_upwards [hx] with m t; rintro x ht; obtain ⟨x,h,rfl⟩:=mem_image.mp ht; apply (band_spec ..).mpr; let v:=x a-z; let n:=K.c m; have hp:=p _ h; have hv:=t _ h; have hu:0<(K.c m).val:=(K.c m).property
  have hg:0 ≤ v:=by unfold v; omega
  have hw:v.toNat<(More n).val:=by change _<n.val*2; unfold n v at *; omega
  rw [show (wrap (More (K.c m)) x) a-(z:Per (More n))=(v.toNat:Per (More n)) from ?_, ZMod.val_natCast_of_lt hw]; swap; · rw [←Int.cast_natCast, Int.toNat_of_nonneg hg,show (v:Per (More n))=(↑(x a) : Per (More n)) - (z:Per (More n)) from Int.cast_sub ..]; rfl
  unfold v; omega

local notation "z₀"=> gaugeShift Λ.block z
include K
lemma ahead_positive (g: Family Kₜ)(f: InTest Kₜ true S false g)(p:Ahead a (gaugeShift Λ.block z) (reserve Λ l) S): 0≤ E s (reflector a (gaugeShift Λ.block z) g * g) := by
 let F:= reflector a z₀ g * g; have hv:TestFamily Kₜ true F:= TestFamily.mul ⟨⟨_,reflects a z₀ f⟩,by simp⟩ ⟨⟨S,f⟩,by simp⟩
 change 0≤ E s F
 rw [← mood_eq Y h s K F hv]; apply ge_of_tendsto (K.pick.booked Y h s hv).1.periods
 filter_upwards [((momentum Y s).comp K.pick.grow_i.tendsto_atTop).eventually (often S a _ Kₜ _ p)] with i t
 apply ge_of_tendsto ((K.pick.booked Y h s hv).1.inner (u i)); filter_upwards [K.pick.pass Y h s (u i)] with n T; unfold hot; rw [dif_pos T.depth]; exact (boxprice Y h _ _ T.depth s T.fire T.enters).fund a z (g (momentm Y (u i) s)) ((f.support _).mono t)

lemma unit_I : I s 1 i=1:= (internal_eq Y h s i K _ TestFamily.oneT).symm.trans (K.pick.unit Y h s i)
-- polarization helper for arbitrary spaces on this lim. no positivity of contact star-conjugation
omit K in
lemma screenshots {V:Type*}[AddCommMonoid V][Module ℂ V](G: V→ₗ⋆[ℂ] V→ₗ[ℂ] ℂ)(p:∀ x:V,0 ≤ G x x):
  (∀ x y,G x y=star (G y x)) ∧ ∀ (I:Type*)[Fintype I] (f:I→ V), Matrix.PosSemidef (Matrix.of fun i j=>G (f i) (f j)):= by
  classical
  have h(x y:V):star (G y x)=G x y:=by
    have he (x:V) : (G x x).im=0:= ((Complex.le_def.mp (p x)).2).symm
    have hx:=he x; have hy:=he y; have hu:=he (x+y); have hv:=he (x+Complex.I • y)
    simp_rw [map_add G,LinearMap.add_apply,map_add] at hu hv
    rw [map_smulₛₗ,map_smulₛₗ (f:=G),LinearMap.smul_apply,LinearMap.smul_apply,map_smulₛₗ] at hv
    simp [hx,hy,Complex.mul_re,Complex.mul_im] at hu hv; apply Complex.ext <;> simp <;> linarith
  refine ⟨fun x y=>(h x y).symm, fun I _ f=>?_⟩
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
  · ext i j; exact h _ _
  intro x; have he:= p (∑ i,x i • f i); rw [map_sum G,LinearMap.sum_apply] at he; simp_rw [map_sum,map_smulₛₗ (f:=G)] at he
  change 0 ≤ ∑ i, star (x i)*∑ j,G (f i) (f j) * x j
  simpa only [smul_eq_mul,starRingEnd_apply,map_smulₛₗ,LinearMap.smul_apply, RingHom.id_apply,Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] using he
#print axioms screenshots
#print axioms ahead_positive
end YM.CF.Buffered.Afterglow.Hierarchy
