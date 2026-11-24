import YM.SU5.FiniteGaugeData.Marked.Variation.Crimson
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake

/-!
# Toward a resolution tower on the direct FiniteGaugeData election

`Y`: same physical course (terminal coupling `(Journey.tent Y H).x=Λ.x`,
independent of period and cutoff; see `coupling_clock`). `i k`: sequences
issuing `Journey.Universal` V (e.g. `u ∘ i, π ∘ k` in diamond, this file's i
argument indexes Y.ir, not the thinning relative to Query). DO NOT need a
per-period replication of heat/color data, even for the positivity statements
here. Use E on *all* fixed-level Wide supported marks (even); the physical
singlets, with or without auxiliary-link argument, can be evaluated there.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

section family
variable (K':Calibration) (S:Finset Cover) (wide:Bool)
attribute [local simp] Algebra.smul_mul_assoc
-- Algebra for fixed support; wide=true also permits local bounded Borel functions
-- of *both* link inputs. Singlet to be imposed separately. Does not depend
-- on the election's period or cutoff. Arguments evaluated on native sites of
-- observing lattice (no fixed-continuum-separation assertion for these arguments
-- with s moving). Supports refer to gauge endpoints.
def supported : Subalgebra ℂ (Family K') where
  carrier:= {f|InTest K' wide S false f}
  mul_mem' := fun a b=> InTest.mul a b
  add_mem' := fun a b=> InTest.add a b
  zero_mem' := InTest.zero
  one_mem' := InTest.one
  algebraMap_mem' := fun r=> by rw [Algebra.algebraMap_eq_smul_one]; exact .smul r InTest.one
variable {K' wide S}
lemma aux_test {f:Family K'} (x: InTest K' true S false f): TestFamily K' true f:= ⟨⟨S,x⟩, by simp⟩
lemma InTest.negOp {b} {f:Family K'} (x: InTest K' wide S b f): InTest K' wide S b (-f):= by simpa using InTest.smul (-1:ℂ) x
lemma InTest.subOp {b}{f g:Family K'} (x:InTest K' wide S b f)(u:InTest K' wide S b g):InTest K' wide S b (f-g):= by rw [sub_eq_add_neg]; exact x.add (InTest.negOp u)
lemma finer_box {f:Family K'}(x:f∈supported K' S wide){T:Finset Cover}(u:S⊆T):f∈supported K' T wide:= InTest.mono x u

/-- Operator bound on *all* tori and pair configurations. -/
def pay {c:Calibration}(F:Family c)(A:ℝ):Prop:=∀ (t:Side)(x:Fields (c.c t)), ‖F t x‖ ≤ A
lemma pay_nonneg {F:Family K'}{A:ℝ}(x:pay F A):0≤A:= (norm_nonneg _).trans (x 1 (1,1))
lemma pay_add {F G:Family K'}{A B:ℝ}(x:pay F A)(y:pay G B): pay (F+G) (A+B) :=fun i a=>(norm_add_le ..).trans (add_le_add (x ..) (y ..))
lemma pay_neg {F:Family K'}{A:ℝ}(x:pay F A):pay (-F) A:=fun i a=>by simpa only [Pi.neg_apply,norm_neg] using x i a
lemma pay_sub {F G:Family K'}{A B:ℝ}(x:pay F A)(y:pay G B): pay (F-G) (A+B):=by rw [sub_eq_add_neg]; exact pay_add x (pay_neg y)
lemma pay_mul {F G:Family K'}{A B:ℝ}(x:pay F A)(y:pay G B):pay (F*G) (A*B):=fun i a=>(norm_mul_le ..).trans (mul_le_mul (x ..) (y ..) (norm_nonneg _) (pay_nonneg x))
lemma pay_scale {F:Family K'}{A:ℝ}(x:pay F A)(z:ℂ):pay (z • F) (‖z‖*A):=fun i a=>by change ‖z • (F i a)‖≤_; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (x ..) (norm_nonneg _)
lemma pay_unit :pay (1:Family K') 1:=fun i a=> (norm_one : ‖(1:Fock.FC (Single (K'.c i)))‖=(1:ℝ)).le
lemma pay_ref {F:Family K'}{A:ℝ}(x:pay F A)(z:ℤ):pay (reflected K' z F) A:= by
  intro i a; change ‖Fock.theta _ (F i _)‖ ≤ _
  -- norm preservation
  rw [theta_fee]; exact x _ _

end family

include V
section common

lemma common_I {f:Family (tent Y H)}(x:TestFamily (tent Y H) true f) (n:ℕ): I s f n=V.pick.field Y H s f n:=
  tendsto_nhds_unique ((V.together s f x).inner n) ((V.pick.booked Y H s x).2.inner n)
lemma common_E {f:Family (tent Y H)}(x:TestFamily (tent Y H) true f): E s f= V.pick.audience Y H s f :=
  tendsto_nhds_unique_of_eventuallyEq (V.together s f x).periods
    (V.pick.booked Y H s x|>.2.periods) (Eventually.of_forall fun _=> common_I Y H V s x _)
lemma I_add {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g)(m:ℕ): I s (f+g) m= I s f m+I s g m:= by
  rw [common_I Y H V s (x.add u),common_I Y H V s x,common_I Y H V s u]; exact congrFun (V.pick.field_add Y H s x u) m
lemma E_add {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g): E s (f+g)= E s f+E s g:= by
  rw [common_E Y H V s (x.add u),common_E Y H V s x,common_E Y H V s u]; exact V.pick.addA Y H s x u
lemma I_scale {f:Family (tent Y H)}(x:TestFamily K true f)(z:ℂ)(m:ℕ): I s (z • f) m=z*I s f m:= by rw [common_I Y H V s (x.scale z),common_I Y H V s x]; exact congrFun (V.pick.field_smul Y H s z x) m
lemma E_scale {f:Family (tent Y H)}(x:TestFamily K true f)(z:ℂ): E s (z • f)=z*E s f:= by rw [common_E Y H V s (x.scale z),common_E Y H V s x]; exact V.pick.smulA Y H s z x
lemma E_unit: E s 1=1:= (V.gaugeMatter s).1
lemma I_unit (m:ℕ): I s 1 m=1:= by rw [common_I Y H V s TestFamily.oneT]; exact V.pick.unit Y H s m
lemma I_sub {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g)(m:ℕ): I s (f-g) m=I s f m-I s g m:=by
 rw [sub_eq_add_neg, ←neg_one_smul ℂ g, I_add Y H V s x (u.scale (-1)),I_scale Y H V s u,neg_one_mul,←sub_eq_add_neg]
lemma E_sub {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g): E s (f-g)=E s f-E s g:=by
 rw [sub_eq_add_neg, ←neg_one_smul ℂ g, E_add Y H V s x (u.scale (-1)),E_scale Y H V s u,neg_one_mul,←sub_eq_add_neg]
def expect : probes (tent Y H) true →ₗ[ℂ] ℂ :=
 ⟨⟨fun f=> E s f.val,fun f g=> E_add Y H V s f.property g.property⟩,fun c f=> E_scale Y H V s f.property c⟩

lemma warm_limit {f:Family (tent Y H)}(x:TestFamily K true f):
  Couplet i k (fun m n=>hot Y H s m n f) (I s f) (E s f) (fun v=>∀ᶠ r in atTop,legacy Y (i r) (k (v r))):= by
 rw [common_E Y H V s x, show I s f=V.pick.field Y H s f from funext (common_I Y H V s x)]; exact (V.pick.booked Y H s x).1

end common
omit V
section sharp_linearity

lemma sharp_scale (f:Family (tent Y H))(a:ℂ)(m n:ℕ): sharp Y H s m n (a • f)=a*sharp Y H s m n f:= by
 have he:= (transformed Y H s m f f a (fun _=>0) 0 0 (Classical.arbitrary _)).2.1
 dsimp only at he
 unfold sharp Journey.listen Journey.compass; rw [he,mark_smul,mul_div_assoc]
lemma sharp_plus {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g){m n:ℕ}(p:Ferry Y s m n):sharp Y H s m n (f+g)=sharp Y H s m n f+sharp Y H s m n g:=by
 have hv:= (transformed Y H s m f g 0 (fun _=>0) 0 0 (Classical.arbitrary _)).1
 unfold sharp Journey.listen Journey.compass; dsimp only at hv; rw [hv,mark_add _ _ _ (Marks.can_read _ _ _ _ p.fire.priceA),add_div]
 · exact ((Y.voyage m).ownership s).paid.bill
 · exact liftEnvelope (terrain Y H (Y.ir m) s) _ (x.paid.choose_spec.support _).env
 · exact liftEnvelope (terrain Y H (Y.ir m) s) _ (u.paid.choose_spec.support _).env
where
 liftEnvelope{m n:Side}(h:m=n)(i:Mark m)(p:Envelope i): Envelope (show Mark n from h ▸ i):=by subst m; exact p
lemma sharp_unit {m n:ℕ}(p:Ferry Y s m n): sharp Y H s m n 1=1:=by
 have hv:= (transformed Y H s m 1 1 0 (fun _=>0) 0 0 (Classical.arbitrary _)).2.2.2.1
 unfold sharp Journey.listen Journey.compass; dsimp only at hv; rw [hv,markvac]; exact div_self p.fire.priceA.valid
lemma sharp_sub {f g:Family (tent Y H)}(x:TestFamily K true f)(u:TestFamily K true g){m n:ℕ}(p:Ferry Y s m n):sharp Y H s m n (f-g)=sharp Y H s m n f-sharp Y H s m n g:=by
 rw [sub_eq_add_neg,←neg_one_smul ℂ g,sharp_plus Y H s x (u.scale (-1)) p,sharp_scale Y H,neg_one_mul,←sub_eq_add_neg]

end sharp_linearity

lemma coupling_clock (n t:ℕ)(p:(Y.voyage n).kick≤ t):
 ((((Y.voyage n).X (Y.uv t)).gram 0).beta)=Λ.x ∧ (((Y.voyage n).Q t p).gram 0).beta=Λ.x:=
 let x:= fullness Y n t p
 ⟨x.cap_pivot,x.pivot⟩

include V
lemma floor_pays: ∀ᶠ r:ℕ in atTop,∀ j,legacy Y (i r) (k j)→ Ferry Y s (i r) (k j):=by
 obtain ⟨p₀,T⟩:= eventually_atTop.mp (ferry_all Y s)
 have t:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp (Y.ir_grows.comp V.pick.grow_i).tendsto_atTop)
 filter_upwards [t.eventually_ge_atTop (Y.uv p₀)] with r b j v
 exact T _ (Y.uv_grows.le_iff_le.mp (b.trans v)) _ (V.pick.ticket r j v)

lemma legacy_above (r t:ℕ): ∃ m ≥ t, legacy Y (i r) (k m):=by
 have hx:= ((Y.uv_grows.comp V.pick.grow_k).tendsto_atTop.eventually_ge_atTop ((Y.ir (i r)).val^5)).and (eventually_ge_atTop t)
 obtain ⟨m,u,v⟩:= hx.exists; exact ⟨m,v,u⟩

lemma hosp_later (S:Finset Cover): ∀ᶠ r:ℕ in atTop, Hosp S ((tent Y H).c (momentm Y (i r) s)):=
 (((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (separates K S)).mono fun r t=>⟨t⟩

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.coupling_clock
