import YM.SU5.FiniteGaugeData.Tapestry.Symphony
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Haro
attribute [local instance] opCStarAlgebra

/-!
# The running beta and Q (counterterm, expense multiplier for modes)

Retain and track the effects at named level. beta zero *level* is prescribed
exactly, throughout. This is the terminal *always*, even for period-dependent
data. `betaNext` (patternβ) belongs to the NEXT higher (finer) level. We prove
local estimate (geometric along the cone of this election) for its convergence &
that of its accompanying Q at any **fixed level**. At a fixed period, these are
enough to pass to operator-norm limit on ALL Mark tests. For the period-varying
sharp steps and sharp readers you'll need the (parallel) statements exposed by
`Exhibition` (including support thresholds); the mere convergence of these
parameters is NOT the argument.
-/
set_option quotPrecheck false
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Py.Period
abbrev Tariff := ℝ× Haro.SpaceM
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H: Real.exp 1 ≤ Λ.x)
variable (S: Finset Cover) (s i k:ℕ)
abbrev rawTariff : Tariff := (patternβ Y s i k, patternQ Y s i k)
lemma betaQ_ranges (h:Satin.PairIdx Y s i k):
   (patternβ Y s i k)∈ Set.Icc (hat Λ.R.L Λ.x (s+1)/2) (Course.ceiling Λ s) ∧ ‖patternQ Y s i k‖≤ Λ.R0 (hat Λ.R.L Λ.x s):= by
  have v : ((rawTariff Y s i k).1)∈ Set.Icc _ _:= ((Carousel.standard Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ (Y.visit i k))).sift (s+1) h.2
  exact ⟨v, ((Y.voyage i).X (Y.uv k)).pull.tip s h.2⟩

-- ornament and coupon are clipped; patternQ, patternβ are not.
def ornament : Tariff:= if Satin.PairIdx Y s i k then rawTariff Y s i k else 0
abbrev inbounds (Λ:Preparation)(s:ℕ) := Set.Icc (hat Λ.R.L Λ.x (s+1)/2) (Course.ceiling Λ s) ×ˢ Metric.closedBall (0:Haro.SpaceM) (Λ.R0 (hat Λ.R.L Λ.x s))
lemma compact_bounds (Λ:Preparation)(s:ℕ): IsCompact (inbounds Λ s):= isCompact_Icc.prod (isCompact_closedBall ..)
lemma decor {p : Satin.PairIdx Y s i k} : ornament Y s i k=rawTariff Y s i k:=by simp [ornament,p]
lemma keptTariff (p:Satin.PairIdx Y s i k):rawTariff Y s i k∈ inbounds Λ s:= let h:= betaQ_ranges Y s i k p; ⟨h.1,mem_closedBall_zero_iff.mpr h.2⟩
lemma ornament_in (p:Satin.PairIdx Y s i k): ornament Y s i k∈inbounds Λ s:=by rw [decor Y s i k (p:=p)]; exact keptTariff Y s i k p

variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l}
section
variable (X:Exhibition Y H a b I E L B)
include X
lemma Exhibition.poll(x y:ℕ→ℕ)(p:StrictMono x)(q:StrictMono y)(h:∀ r j,legacy Y (a (x r)) (b (y j)) ↔ r ≤ j): Exhibition Y H (a∘x) (b∘y) I E L B:= by
  refine ⟨subsystems Y H X.univ_ x y p q,fun S s=> burgundyFurther Y H S s X.parallel x y p,h,fun S s i=>(X.inner S s i).comp q.tendsto_atTop,fun S s=>?_,fun S s=>(X.IR S s).comp p.tendsto_atTop ⟩
  filter_upwards [p.tendsto_atTop.eventually (X.road S s)] with i v'
  refine ⟨v'.1,fun j t=>?_⟩; have z:=v'.2 (y j) ((X.status _ _).mp ((h ..).mpr t)); exact ⟨z.1,z.2.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (StrictMono.id_le p i))⟩
lemma Exhibition.poll_equal(u:ℕ→ℕ)(p:StrictMono u): Exhibition Y H (a∘u) (b∘u) I E L B:= X.poll Y H u u p p (fun r j=> (X.status _ _).trans (by exact p.le_iff_le))
end
structure Fashion (a b:ℕ→ℕ) (I:ℕ→Family (tent Y H)→ℕ→ℂ)(E:ℕ→Family (tent Y H)→ℂ)(L:Rack Λ l)(B:Clay Λ l) (T:ℕ→ℕ→Tariff)(t:ℕ→Tariff):Prop extends Exhibition Y H a b I E L B where
  stripe (s i:ℕ): Tendsto (fun j=> rawTariff Y s i (b j)) atTop (𝓝 (T s i))
  ribbon (s:ℕ): Tendsto (fun r=> T s (a r)) atTop (𝓝 (t s))
  scroll (s:ℕ): ∀ᶠ r in atTop,∀ j,r≤ j→ Satin.PairIdx Y s (a r) (b j) ∧ dist (rawTariff Y s (a r) (b j)) (t s) ≤ propeller r
lemma selectFashion (X:Exhibition Y H a b I E L B) : ∃ u v T t, StrictMono u ∧ StrictMono v ∧ Fashion Y H (a∘u) (b∘v) I E L B T t:=by
  obtain ⟨u,v,F,t,p,q,D⟩:= YM.SU5.FiniteGaugeData.LocalLimit.Rings.two_steps (f:=fun _ : ℕ=> Tariff) (ornament Y) (fun i s=>True) (fun i k s=> Satin.PairIdx Y s i k) (legacy Y) Iic propeller
   (fun j=> ⟨insert 0 (inbounds Λ j),(compact_bounds Λ j).insert _,fun i k=> Classical.byCases (p:=Satin.PairIdx Y j i k) (fun p=> Set.mem_insert_of_mem _ (ornament_in Y j i k p)) (fun p=>by simp [ornament,p])⟩) (fun _=> Eventually.of_forall fun _=>trivial) (fun i j _=>eventualPairIdx Y j i) (cadence Y id strictMono_id) (absent Y id strictMono_id) (fun i=>pow_pos (by norm_num) _) a b X.univ_.pick.grow_i X.univ_.pick.grow_k
  let e:=X.poll Y H u v p q D.card
  refine ⟨u,v,F,t,p,q,e,fun s i=>(D.cut s i).congr' ((D.dep.tendsto_atTop.eventually (eventualPairIdx Y s i)).mono fun j p=> decor Y s i ((b∘v) j) (p:=p)),D.ir,?_⟩
  intro s; filter_upwards [eventually_ge_atTop s] with i h; intro j t'; have e:=D.line i j t' s (mem_Iic.mpr h); exact ⟨e.1, by rw [← decor (Y:=Y) (p:=e.1)]; exact e.2⟩
namespace Fashion
variable {T:ℕ→ℕ→Tariff}{t:ℕ→Tariff} (X:Fashion Y H a b I E L B T t)
include X
lemma inherit_ (x y:ℕ→ℕ)(u:StrictMono x)(v:StrictMono y)(h:∀ r j,legacy Y (a (x r)) (b (y j)) ↔ r ≤ j): Fashion Y H (a∘x) (b∘y) I E L B T t:=by
  refine ⟨X.toExhibition.poll Y H x y u v h,fun s i=>(X.stripe s i).comp v.tendsto_atTop,fun s=> (X.ribbon s).comp u.tendsto_atTop,?_⟩
  intro s; filter_upwards [u.tendsto_atTop.eventually (X.scroll s)] with i p; intro j x'; have g:= p (y j) ((X.status _ _).mp ((h ..).mpr x')); exact ⟨g.1,g.2.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (StrictMono.id_le u i))⟩
lemma inherit_diag(u:ℕ→ℕ)(p:StrictMono u): Fashion Y H (a∘u) (b∘u) I E L B T t:= X.inherit_ Y H u u p p (fun r j=> (X.status _ _).trans (by exact p.le_iff_le))

lemma UVPrices: T s i∈inbounds Λ s := (compact_bounds Λ s).isClosed.mem_of_tendsto (X.stripe s i) ((X.univ_.pick.grow_k.tendsto_atTop.eventually (eventualPairIdx Y s i)).mono fun k p=> keptTariff Y s i (b k) p)
lemma IRPrices: t s∈inbounds Λ s:= (compact_bounds Λ s).isClosed.mem_of_tendsto (X.ribbon s) (Eventually.of_forall fun r=> X.UVPrices Y H s (a r))
lemma conePrices: ∀ᶠ r in followStage, Satin.PairIdx Y s (a r.vol) (b r.uv) ∧ dist (rawTariff Y s (a r.vol) (b r.uv)) (t s) ≤ propeller r.vol:= (overStage.eventually (X.scroll s)).mono fun i p=> p i.uv i.inside
lemma pricesRowIR : ∀ᶠ r in atTop, dist (T s (a r)) (t s)≤ propeller r:=by
  filter_upwards [X.scroll s] with i p; apply le_of_tendsto ((X.stripe s (a i)).dist (tendsto_const_nhds (x:= t s))) ((eventually_ge_atTop i).mono fun j h=> (p j h).2)
end Fashion
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.selectFashion
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.pricesRowIR
#print axioms YM.CF.Buffered.Afterglow.Tapestry.betaQ_ranges
