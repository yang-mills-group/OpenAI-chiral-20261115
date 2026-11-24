import YM.SU5.FiniteGaugeData.Tower.Control
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
/-!
# Buying box, resolution and tolerance on the norm cone

`crimson` grants *eventual*, with thresholds dependent on both!
We can supply paired periods/cutoffs purchasing prechosen increasing resolutions,
growing cover boxes, and rescaling operation errors. We retain the Level-s
target functional paid through those choices and the terminal physical Λ.x.
No Printed/alternative schedules. Keep joint calibration provisos unchanged.
One new thinning of the Crimson line suffices to get any prescribed regulator
accuracy, even on the whole unit ball of the supported grammar with the level
and support *changing* as indicated (and hence even, say, all polynomials
and translated products of tests on that ball; if wanting correlation prices
with scaling, buy that factor upfront too). In particular this doesn't finance
the remaining *resolution boundary comparisons between evaluation functionals*
in any such use; equipment for that in other modules.
-/
local notation "m" r:max s:max=> momentm Y r s

def StepCost (S:Finset Cover)(r:ℕ)(e:ℝ):Prop:=
 let M:= i r; let t:= m M s
 Hosp S ((tent Y H).c t)∧(∀ j,legacy Y M (k j)→ Ferry Y s M (k j)) ∧
 ∀ (f:Family (tent Y H)), InTest K true S false f→ ∀ C:ℝ, (∀ x, ‖f t x‖≤C)→
    ‖I s f M-E s f‖ ≤ e*C∧
    ∀ j,legacy Y M (k j)→ ‖sharp Y H s M (k j) f-E s f‖≤ e*C

variable {q:ℕ→ℕ}(Q:CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q)
local notation "P" => StepCost (i:=i) (k:=k) (I:=I) (E:=E) Y H
local notation "d" r:max=> (1/2:ℝ)^r
lemma relax {S:Finset Cover}{r:ℕ}{e e':ℝ}(h:P s S r e)(v:e≤e'):P s S r e':=by
 refine ⟨h.1,h.2.1,?_⟩; intro f x C p; have h':= h.2.2 f x C p; have t:0≤C:=(norm_nonneg _).trans (p (1,1)); exact ⟨h'.1.trans (by gcongr), fun j g=> (h'.2 _ g).trans (by gcongr)⟩
lemma clip {S T:Finset Cover}{r:ℕ}{e:ℝ}(h:P s S r e)(v:T⊆S):P s T r e:=by
 exact ⟨⟨h.1.seat_.mono v⟩,h.2.1,fun f p=> h.2.2 f (p.mono v)⟩
private lemma cheaper (e:ℝ)(p:0<e):∀ᶠ r:ℕ in atTop,d r≤e:= by
 have h:Tendsto (fun r:ℕ=>(1/2:ℝ)^r) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num); exact h.eventually (ge_mem_nhds p)
include Q

lemma hires (s b:ℕ)(e:ℝ)(p:0<e):∀ᶠ r in atTop, ∀ j ≤ s,∀ S:Finset Cover,S⊆Lattice.box b→ P j S (q r) e:=by
 have ht(j):∀ᶠ r in atTop,P j (Lattice.box b) (q r) (d r):=Q.budget j _
 filter_upwards [((eventually_all_finset (Iic s)).mpr fun j _=>ht j),cheaper e p] with r h t j hj S u
 exact clip Y H j (relax Y H j (h j (mem_Iic.mpr hj)) t) u

-- election from a moving floor/tolerance schedule
omit Q in
private lemma elect_fin (Pv:ℕ→ℕ→Prop)(h:∀i:ℕ,∀ᶠ j:ℕ in atTop,Pv i j):∃ t:ℕ→ℕ, StrictMono t∧ ∀i,Pv i (t i):=by
 have hx(x r:ℕ):∃ i≥ r+1,Pv x i:= ((eventually_ge_atTop (r+1)).and (h x)).exists
 choose F c w using hx
 let t:= Nat.rec (motive:=fun _=>ℕ) (F 0 0) (fun r u=> F (r+1) u)
 refine ⟨t,strictMono_nat_of_lt_succ (fun r=>c ..),fun i=>?_⟩
 cases i
 · exact w 0 _
 exact w _ _
lemma sponsor (r b:ℕ→ℕ)(e:ℕ→ℝ)(he:∀ x,0<e x):∃ t:ℕ→ℕ,StrictMono t∧ ∀ x, ∀ s≤r x,∀ S:Finset Cover, S⊆ Lattice.box (b x) → P s S (q (t x)) (e x) := elect_fin _ fun x=>hires Y H Q _ _ _ (he x)

include V
-- and pay those paired cone entries. The assertion doesn't require any chosen
-- `j` above the other period picks later; it truly works for EVERY admitted `j`
lemma immediately (r b:ℕ→ℕ)(A e:ℕ→ℝ)(he:∀ x,0<e x)(ha:∀ x,0≤A x):
 ∃ t c:ℕ→ℕ, StrictMono t∧ StrictMono c∧
 ∀ x, let n:=i (q (t x))
 legacy Y n (k (c x))∧
 ∀ s≤r x,∀ S:Finset Cover,S⊆ Lattice.box (b x) → let N:=m n s
 Hosp S ((tent Y H).c N)∧
 (∀ f:Family K, InTest K true S false f→ (∀ i, ‖f N i‖≤ A x)→ ‖I s f n-E s f‖≤e x) ∧
 ∀ j,legacy Y n (k j)→ Ferry Y s n (k j)∧
   (∀ f:Family K, TestFamily K true f→
    let a:=send Y H n s (f N); let v:= ((Y.voyage n).X (Y.uv (k j))).gram s; let T:=(Y.voyage n).CapeT s; let Z:= partitionZ v Λ.U T
    Integrable (fun x=> inner ℂ (Dial.mateK (side Y n s)) (acts (a (drawn T x)) (denZ v Λ.U T x))) (city (side Y n s)) ∧ Z≠0 ∧
    sharp Y H s n (k j) f=(∫ x, inner ℂ (Dial.mateK (side Y n s)) (acts (a (drawn T x)) (denZ v Λ.U T x)) ∂city (side Y n s))/Z) ∧
   (∀ f:Family K,InTest K true S false f→ (∀ i, ‖f N i‖≤A x)→ ‖sharp Y H s n (k j) f-E s f‖ ≤ e x):=by
 let dx(x:ℕ):ℝ:= e x/(A x+1); have v(x):0<dx x:=by specialize he x; specialize ha x; unfold dx; positivity
 obtain ⟨t,p,v'⟩:= sponsor Y H Q r b dx v
 let n(x:ℕ):=i (q (t x))
 obtain ⟨c,g,w⟩:=elect_fin (fun x j=>legacy Y (n x) (k j)) (fun x=> (Y.uv_grows.comp V.pick.grow_k).tendsto_atTop.eventually_ge_atTop _)
 refine ⟨t,c,p,g,fun x=>?_⟩; change legacy Y (n x) _ ∧ _
 have he':dx x * A x ≤ e x:=by have p:dx x* (A x+1)=e x:=div_mul_cancel₀ _ (by have h:=ha x; linarith); have u:=v x; nlinarith
 refine ⟨w x,fun s h S u=>?_⟩
 obtain ⟨p',t',z⟩:=v' x s h S u
 exact ⟨p',fun f h g=> (z f h _ g).1.trans he',fun j h=> ⟨t' j h, fun f p=> Journey.paid Y H s (p:=t' j h) p,fun f t w=> ((z _ t _ w).2 _ h).trans he'⟩⟩

lemma approaching (r b:ℕ→ℕ)(A:ℕ→ℝ)(ha:∀ x, 0≤ A x):∃ t c:ℕ→ℕ, StrictMono t∧ StrictMono c ∧ (∀ x, legacy Y (i (q (t x))) (k (c x)))∧
   ∀ (s:ℕ→ℕ)(F:ℕ→Family (tent Y H))(p:∀ᶠ x:ℕ in atTop, InTest K true (Lattice.box (b x)) false (F x))(v:∀ᶠ x in atTop,s x ≤r x)(j:ℕ→ℕ)(u:∀ᶠ x:ℕ in atTop, legacy Y (i (q (t x))) (k (j x)))(a:∀ᶠ x:ℕ in atTop, ∀ i', ‖F x (momentm Y (i (q (t x))) (s x)) i'‖≤A x),
   Tendsto (fun x=>I (s x) (F x) (i (q (t x)))-E (s x) (F x)) atTop (𝓝 0) ∧
   Tendsto (fun x=>sharp Y H (s x) (i (q (t x))) (k (j x)) (F x)-E (s x) (F x)) atTop (𝓝 0):=by
 obtain ⟨t,c,p,f,V⟩:= immediately Y H V Q r b A (fun x=> (1/2:ℝ)^x) (fun x=>by positivity) ha
 refine ⟨t,c,p,f,fun x=>(V x).1,?_⟩; intro s F h v j w u
 have ht:Tendsto (fun x:ℕ=>(1/2:ℝ)^x) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 constructor
 · rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ ht; filter_upwards [h,v,u] with x p y z; exact ((V x).2 (s x) y _ (by rfl)).2.1 (F x) p z
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ ht; filter_upwards [h,v,u,w] with x p y z w; exact (((V x).2 (s x) y _ (by rfl)).2.2 (j x) w).2.2 (F x) p z

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.approaching
