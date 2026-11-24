import YM.SU5.FiniteGaugeData.Tapestry.Neutral
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Harmony of local interlevel maps
-/
set_option quotPrecheck false
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
variable (K:Calibration) (S:Finset Cover)
variable (T:Cover→ SU.E)

lemma circularUnique (f g e:Swatch S)(p: Circular S T (render S K f) (render S K e)) (m:Side)(t:Hosp S (K.c m))(h: ∃ v,TraceGauge S T (m:=K.c m) v ∧ Harmony v (appear S K m f) (appear S K m g)):
  g=e:=by
  apply appear_inj S K m t; funext x; obtain ⟨v,u,w⟩:=h; exact (twist (quantU (tradew (K.c m) v))).injective ((w x).symm.trans (p m v u x))

lemma turnScore (f: Swatch S): ∃ g: Swatch S, Circular S T (render S K f) (render S K g):=by
  obtain ⟨u,q,p⟩:= reColor T (texture S K f); obtain ⟨g,rfl⟩:= rendered S K q; exact ⟨g,p⟩
lemma pegOutput (f g e: Swatch S)(p: Circular S T (render S K f) (render S K e))(q:Circular S T (render S K f) (render S K g)) : g=e:=by
  obtain ⟨m,p'⟩ := (separates K S).exists; obtain ⟨g',v⟩:= scoreTrace T (show Hosp S (K.c m) from ⟨p'⟩)
  exact circularUnique K S T f g e p m ⟨p'⟩ ⟨g',v,q m g' v⟩
noncomputable def ocellus : Swatch S →ₗ[ℂ] Swatch S where
  toFun f:= (turnScore K S T f).choose
  map_add' x y:= by
    apply Eq.symm; apply pegOutput K S T (x+y) _ _ (turnScore K S T _).choose_spec; rw [map_add,map_add]; exact Circular.add _ _ (turnScore K S T x).choose_spec (turnScore K S T y).choose_spec
  map_smul' z x:= by
    apply Eq.symm; apply pegOutput K S T (z • x) _ _ (turnScore K S T _).choose_spec; simp only [map_smul,RingHom.id_apply]; exact Circular.scale _ _ (turnScore K S T _).choose_spec z -- maybe map_smul instance tune
lemma decorates (x:Swatch S): Circular S T (render S K x) (render S K (ocellus K S T x)):= (turnScore K S T x).choose_spec
-- norm cost controlled with same two-sided field convention, no comparing periods
noncomputable def ocelli : Swatch S →L[ℂ] Swatch S:= (ocellus K S T).mkContinuous (spread S) fun x=>by
  obtain ⟨m,v⟩:= (separates K S).exists; obtain ⟨g,p⟩:= scoreTrace T (show Hosp S (K.c m) from ⟨v⟩)
  apply sampling S K m ⟨v⟩; intro y; rw [←appearRender, ← twist_norm (quantU (tradew (K.c m) g)), ← decorates K S T x m g p y]; exact renderLe ..

lemma continuousColor {J:Type*}{L:Filter J}[NeBot L]{A B:J→Swatch S}{f F:Swatch S}
  (p:Tendsto A L (𝓝 f))(q:Tendsto B L (𝓝 F))(h:∀ᶠ i in L,Circular S T (render S K (A i)) (render S K (B i))) : Circular S T (render S K f) (render S K F):=by
    let W:= ocelli K S T
    have he:F= W f:= tendsto_nhds_unique_of_eventuallyEq q (W.continuous.continuousAt.tendsto.comp p) (h.mono fun i u=> pegOutput K S T _ _ _ (decorates K S T (A i)) u)
    rw [he]; exact decorates K S T f -- too many args again?

open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
  {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l}(X:Exhibition Y H a b I E L B)
  (s i k:ℕ)
local notation "K₀"=>tent Y H
local notation "U"=>followBox (Λ:=Λ) (l:=l) S
local notation "P"=> side Y i s
local notation "m"=>momentm Y i s -- syntax conflict
local notation "i₀" t:max=> a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)

lemma truePrinting {f g:Family K₀}(p:Circular S T f g){t:Seat (side Y i s)→ SU.E}(e:TraceGauge S T t) : Harmony t (exhibit Y H s i f) (exhibit Y H s i g):= overcast S T _ _ (terrain Y H (Y.ir i) s) _ _ (p m) e
where overcast(S:Finset Cover)(T':Cover→SU.E)(N M: Side)(h:N=M)(f g:Mark N)(p:∀ u:Seat N→ SU.E, TraceGauge S T' u→ Harmony u f g){u:Seat M→ SU.E}(e:TraceGauge S T' u): Harmony u (arrange N M h f) (arrange N M h g):=by subst N; exact p u e
lemma validate {f:Family K₀}(p: Neutral K₀ f): covariant (exhibit Y H s i f):= trueBlue _ _ (terrain Y H (Y.ir i) s) _ (p m)
where trueBlue(N M:Side)(h:N=M)(f:Mark N)(p:covariant f):covariant (arrange _ _ h f):=by subst N; exact p

-- exact support criterion at a single hospitable torus. convenient port for arbitrary S,s
lemma nativeColor {f F: Swatch S}(t:Seat (side Y i s)→ SU.E)(p:Hosp S (side Y i s))(h:TraceGauge S T t)
    (e:Harmony t (present Y H s i S f) (present Y H s i S F)): Circular S T (render S K₀ f) (render S K₀ F):=by
    let Z:= ocelli K₀ S T f; have H': Circular S T (render S K₀ f) (render S K₀ Z):= decorates K₀ S T f
    have v:F= Z:= by
       have H'': Harmony t (present Y H s i S f) (present Y H s i S Z):=by rw [present_exhibit,present_exhibit]; exact truePrinting S T Y H s i H' h
       apply present_inj Y H s i S p; funext x; exact (twist (quantU (tradew (side Y i s) t))).injective ((e x).symm.trans (H'' x))
    rwa [v]

abbrev parentGauge (Λ: Preparation) (T: Cover→ SU.E): Cover → SU.E:=fun a=> T (Λ.R.L.val • a)
lemma hierarchyTrace (t:Seat (side Y i (s+1))→ SU.E) (h:TraceGauge U T t) : TraceGauge S (parentGauge Λ T) (Peaks.scaleG (Vale.apt (Y.ir i) Λ.block Λ.R.L s) t):=by
  unfold Peaks.scaleG TraceGauge; intro x p; dsimp only [Function.comp_apply]; rw [Ratio.embed_wrap]; exact h _ (liner_here _ _ (mem_image_of_mem _ p))

lemma couponColor (f F:Swatch S)(e:Circular S (parentGauge Λ T) (render S K₀ f) (render S K₀ F))(p: Spanned Y S s i k):
  let r:=coupon Y H S s i k
  Circular U T (render U K₀ (r f)) (render U K₀ (r F)):=by
  intro r
  obtain ⟨t,v⟩:= scoreTrace T (Roomy.seats p.2.2)
  refine nativeColor U T Y H (s+1) i t (Roomy.seats p.2.2) v ?_; unfold r; rw [onSpanned _ _ _ _ _ _ p,onSpanned _ _ _ _ _ _ p]
  exact ascendHarmony Y s i k p.1 (presented Y H s i S F) t (presented Y H s i S f).env (by rw [present_exhibit,present_exhibit]; exact truePrinting S (parentGauge Λ T) Y H s i e (hierarchyTrace S T Y s i t v))

include X
lemma visibleColor (f F:Swatch S)(e:Circular S (parentGauge Λ T) (render S K₀ f) (render S K₀ F)): Circular U T (render U K₀ (B S s f)) (render U K₀ (B S s F)) := continuousColor K₀ U T (X.buoy Y H S s f) (X.buoy Y H S s F) ((X.uniformRoad Y H S s).mono fun i t=> couponColor S T Y H s _ _ f F e t)
lemma remainsNeutral (f:Swatch S)(p:Neutral K₀ (render S K₀ f)) : Neutral K₀ (render U K₀ (B S s f)):= (harmonicHere (S:=U)).2 (fun t=> visibleColor S t Y H X s f f ((harmonicHere (S:=S)).1 p (parentGauge Λ t))) -- order
lemma ensembled {f F:Swatch S}(e:Circular S T (render S K₀ f) (render S K₀ F)): E s (render S K₀ f)=E s (render S K₀ F):=by
  have t:= X.coneReader Y H S s
  have he(x:Swatch S):=cn_apply (X:=Swatch S) (Y:=ℂ) t (tendsto_const_nhds (x:=x))
  apply tendsto_nhds_unique_of_eventuallyEq (he f) (he F)
  filter_upwards [X.payStage Y H s,X.uniformRoom Y H S s] with i v a'
  obtain ⟨q,z⟩:= scoreTrace T (Roomy.seats a'); rw [tapReader_compass Y H S s _ _ f v,tapReader_compass Y H S s _ _ F v, present_exhibit,present_exhibit]; exact trueHarmony Y _ _ _ v q (truePrinting S T Y H s _ e z)
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.visibleColor
#print axioms YM.CF.Buffered.Afterglow.Tapestry.remainsNeutral
#print axioms YM.CF.Buffered.Afterglow.Tapestry.ensembled
