/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Momenta.Retreat
/-!
 # Which tables can be read. Even gauge-invariant point sector excitations.
 adapts from `Work/C26`. (Tests pure-gauge references there only.)
 On these EP charges obtain equivalence W ↔ Eu, in particular testing isn't just label semantics.
 Geometry/Raster rel interpretation is still needed. Then can work modulo null charges.
 This asserts no operator content at field coincidence or an identification of chiral matter yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Filter Set Function MeasureTheory Distribution Boundary
open _root_.YM.Boundary.Probe Mink
open scoped Topology
variable {V V':Type*} [AddCommGroup V][Module ℂ V][AddCommGroup V'][Module ℂ V']
variable {F:InkWaves V}{W:WView V}{n:ℕ}{R:Courts V}
namespace Palette
variable {Z:Palette W blanket}
lemma time_visible (x:SpacePoints n)(y:Heights n)(v: Fin n→V): F.entrance (place x y) v=F.F n (fun i=>(y i : ℂ)*Complex.I) x v:=by rw [InkWaves.entrance,line_place',trace_place']
lemma time_unique {g:Times n→SpacePoints n→ℂ}(v:Fin n→V)(p:F.Region)(q:∀ s:SpacePoints n,DifferentiableOn ℂ (fun z=> g z s) (strict n)) (h:∀ x y, y∈east n→ F.entrance (place x y) v=g (fun i=>(y i:ℂ)*Complex.I) x)(z:Times n)(s:SpacePoints n)(hz:z∈strict n): F.F n z s v=g z s:=by
 simpa only [Complex.ofReal_zero,add_zero] using (Work.C09.time_compare _ _ (p.hol n v s) (q s) 0 (fun y p _=>by
    have hx:=h s y p
    simpa only [mul_zero,add_zero,time_visible] using hx) z hz)
lemma wheel_place(x:SpacePoints n){y:Heights n}(h:y∈east n): place x y∈ Wheeled n:= by change lineK _ ∈ east n; rw [line_place']; exact h
lemma permute (u:R.Carriage F)(p:F.Region)(v: Fin n→V) (r: Equiv.Perm (Fin n))(x:Points n) : helio R F n (Points.rearrange r x) (v ∘ r)=helio R F n x v:=by
 let t:Frames n:= (1,r); rw [show Points.rearrange r x=reFrame t x from PiLp.ext fun i=>(Ortho.move_one _).symm, show v ∘ r= reSup t R v from funext fun i=>(R.eu1 _).symm]; exact helio_carries u p t Courts.proper_one x v
-- lifting on any permutation branch. Works even conf not generic.
lemma preserving (u:R.Carriage F)(p:F.Region)(v: Fin n→V) (f:(Fin n→V)→Points n→ℂ) (x:Points n)(hx:x∈conf n) (h:∀ (r:Equiv.Perm (Fin n)) (p:Points n),p∈ Wheeled n→ F.entrance p (v ∘ r)=f (v ∘ r) p) (h₁:∀ (r:Equiv.Perm (Fin n)), ContinuousOn (f (v ∘ r)) (conf n)) (q:∀ (r:Equiv.Perm (Fin n)), f (v ∘ r) (Points.rearrange r x)=f v x) : helio R F n x v=f v x:=by
 let r:= Tuple.sort (fun i:Fin n=> time (x i)); let y:= Points.rearrange r x; have hy: Work.C20.readings y∈ sunrise n:= Tuple.monotone_sort (fun i:Fin n=> time (x i)); have hp:y∈conf n:=Points.rearrange_in r hx; have hb:(𝓝[Wheeled n] y).NeBot := Work.C20.ordered_neBot hy; rw [← permute u p v r, ← q r];
 refine tendsto_nhds_unique_of_eventuallyEq (((helio_cont u p (v∘r)) _ hp).mono (fun q (h:q∈Wheeled n)=>wheel_at h) |>.tendsto) (((h₁ r) y hp).mono (fun q (h:q∈Wheeled n)=> wheel_at h) |>.tendsto) ?_
 filter_upwards [self_mem_nhdsWithin] with z hz; rw [helio_local u p z hz]; exact h r z hz
-- Damped Palette change. independence of blanket with spectrum on W (not needed uses canonical everywhere).
variable {F₁:InkWaves V'}{W₁:WView V'}{Q:Palette W₁ blanket} {R':Courts V'}
-- arbitrary different label permutation branches for second: compare on same V? use map-only linear extension. To compare fixed W with different v' ∀r, need preserving for r chosen vs direct.
lemma any_permutation (P: V→V') (x:Points n)(e:x∈conf n)(p:F.Region)(p':F₁.Region)(h:R.Carriage F)(h':R'.Carriage F₁) (v:Fin n→V)(q:∀ (r:Equiv.Perm (Fin n))(y:Points n), y∈ Wheeled n→ F.entrance y (v ∘ r)= F₁.entrance y (P ∘ v ∘ r)): helio R F n x v=helio R' F₁ n x (P ∘ v):= by
 refine preserving h p v (fun v y=> helio R' F₁ n y (P ∘ v)) x e (fun r y t=> (q r y t).trans (helio_local h' p' y t _).symm) (fun r=> helio_cont h' p' _) (fun r=> permute h' p' (P ∘ v) r x)
lemma visible {v:Fin n→V}{v':Fin n→V'}(p: (ticket blanket W).FullBody F) (h:(ticket blanket W₁).FullBody F₁)(e: W.W n v = W₁.W n v')(x:Points n)(t:x∈Wheeled n) : F.entrance x v = F₁.entrance x v':=by rw [views p _ t,views h _ t]; unfold emit; rw [e]; rfl
lemma holding {v:Fin n→V} (p: (ticket blanket W).FullBody F) (e: W.W n v=0)(x:Points n)(t:x∈Wheeled n): F.entrance x v=0:=by rw [views p _ t,emit,e]; simp
lemma all_unseen_zero (v:Fin n→V)(r:F.Region)(h:F.NonTangentialFree W) (e:∀ p : Points n, p∈Wheeled n→ F.entrance p v=0) : W.W n v=0:=by
 have he(p:Points n)(y:Heights n)(u:y∈east n): F.restricted v y p=0:=by
    have h0: Boundary.shift p y∈strict n:= by intro i j hij; simpa [Boundary.shift] using (u hij) -- check lemma
    exact time_unique (g:=fun _ _=>0) v r (fun _=> differentiableOn_const 0) (fun i _ p=> e _ (wheel_place i p)) _ _ h0
 haveI := Boundary.awaits (light n) -- args
 ext1 f; apply tendsto_nhds_unique_of_eventuallyEq (h.corner n v f) tendsto_const_nhds; filter_upwards [self_mem_nhdsWithin] with y u; simp only [he _ y u,zero_mul, integral_zero]; rfl
lemma wakes_compare {v: Fin n→V} {v':Fin n→V'} (p:F.Region) (p':F₁.Region)(C:F.NonTangentialFree W)(T:F₁.NonTangentialFree W₁)(e:∀ x:Points n,x∈ Wheeled n→ F.entrance x v=F₁.entrance x v') : W.W n v=W₁.W n v':=by
 have he(p₂:Points n)(y:Heights n)(h:y∈east n) : F.restricted v y p₂=F₁.restricted v' y p₂:= time_unique v p (p'.hol n v') (fun x y hx=> (e _ (wheel_place x hx)).trans (time_visible ..)) (Boundary.shift p₂ y) _ (by intro i j hij; simpa [Boundary.shift] using (h hij))
 haveI:= Boundary.awaits (light n)
 ext1 f; apply tendsto_nhds_unique_of_eventuallyEq (C.corner n v f) (T.corner n v' f); filter_upwards [self_mem_nhdsWithin] with y u; simp only [he _ y u]
lemma on_wheel (v:Fin n→V)(r:F.Region)(f:Points n→ℂ)(p:ContinuousOn f (Wheeled n))(h:∀ x:Points n,x∈generic n → x∈Wheeled n→F.entrance x v=f x): EqOn (fun x=>F.entrance x v) f (Wheeled n):=by
 let t:=wheel_open n; apply Measure.eqOn_open_of_ae_eq (μ:=volume) (?_) t (entrance_cont _ r _) p; exact (ae_restrict_iff' t.measurableSet).mpr ( (Extraction.almostGeneric n).mono fun i t x=> h i t x )
end Palette
-- apply across actual INK stores.
namespace WView
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{B:Carton S V}
variable {H':Hilbert}{T:OS.Semigroup H' timeAxis}{B':Carton T V'}{R':Courts V'}{F':InkWaves V'}{W':WView V'}
variable (u:InkPort B F W)(h:R.Carriage F)(m:InkPort B' F' W')(p:R'.Carriage F')
include u h
lemma spectrum_paid: (Palette.ticket Palette.blanket W).FullBody F:= Palette.available _ (WView.on_shape (u.fades h) u.half_price) u.region u.gap_cost u.weighted u.looks
include m p
-- map permits arbitrary label relabel for question.
lemma stays_surface (P:V→V') : (∀ n (x:Fin n→ V), W.W n x= W'.W n (P ∘ x)) ↔ (∀ n (v: Fin n→V)(x:Points n), x∈ conf n→ helio R F n x v=helio R' F' n x (P ∘ v)):= by
 refine ⟨fun f n v x t=> Palette.any_permutation P x t u.region m.region h p v (fun r y hy=> Palette.visible (spectrum_paid u h) (spectrum_paid m p) (f _ (v∘r)) y hy),?_⟩
 intro f n v; apply Palette.wakes_compare u.region m.region u.level m.level; intro x hx; rw [← helio_local h u.region x hx,← helio_local p m.region x hx]; exact f n v x (wheel_at hx)
lemma all_generic_price (P:V→V') : (∀ n (x:Fin n→V), W.W n x=W'.W n (P ∘ x)) ↔ ∀ n (v:Fin n→V)(x:Points n), x∈ generic n→ x∈ Wheeled n→ F.entrance x v= F'.entrance x (P ∘ v):= by
 constructor
 · exact fun g n v x _ hp=> Palette.visible (spectrum_paid u h) (spectrum_paid m p) (g n v) x hp
 intro f n v; exact Palette.wakes_compare u.region m.region u.level m.level (fun i p=> Palette.on_wheel v u.region (fun p=> F'.entrance p (P ∘ v)) (entrance_cont _ m.region _) (f n v) p)
-- since material tensor form; expectation ALL polynomial prices paid iff W pair on all slots. does not assert equivalence across label lists mixing corners unless so admitted.
omit u h m p
lemma material_eq (P:V→V') : (∀ n (x:Fin n→V), W.W n x=W'.W n (P ∘ x)) ↔ ∀ n (v:Fin n→V)(f:Fin n→Test4), W.expect (List.ofFn fun i=>(v i,f i))= W'.expect (List.ofFn fun i=>(P (v i), f i)):=by
 simp_rw [expect_ofFn]; constructor
 · intro h n v f; rw [h]; rfl
 intro p n v; apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:=Set.range (Joint.materialize n))
 · intro x; change x∈(Submodule.span ℂ (Set.range (Joint.materialize n))).topologicalClosure; rw [Work.C25.answer n]; exact Submodule.mem_top
 rintro _ ⟨z,rfl⟩; exact p n v z
end WView
end YM.SatinWFixed
