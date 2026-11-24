import YM.SU5.FiniteGaugeData.Poin.Velvet
import YM.SU5.FiniteGaugeData.Poin.Embargo
import YM.SU5.FiniteGaugeData.Poin.DeSoto
/-! # The Wightman-direction result (parameterized by Eu receipts; see next)

 on the actual charge $G measures` (captured via Eu stamps): fields linear on all finite-dimensional multiplets. representation of proper Lorentz on them. Use common Word domain (as submodule of the polynomial time-energy domain; embed by `lens` into H).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (V:Boundary.Action H)
structure Arrival : Prop where
 time (x:E4) : V.orbit.translation x = M S x
 -- @word-domain in H. (Use Horizon α-degree Ω formula)
 dense : DenseRange (M'.lens S Ω)
 cyclic : Submodule.span ℂ (Set.range (M'.focus S Ω))=⊤
 focuses (t:M'.Token) (w:List M'.Token) : M'.fieldMap S Ω t.1 t.2 (M'.focus S Ω w)= M'.focus S Ω (t::w)
 lift(p:Mink.Poincare): M'.Use S Ω p (V.V p)
 omega : ‖Ω.val‖=1
 pinned (p:Mink.Poincare): V.V p Ω.val=Ω.val
 respect(p:Mink.Poincare)(i:M'.Model S Ω) : V.V p (M'.lens S Ω i)=M'.lens S Ω (M'.emergeC S Ω p V lift i)
 covariance (p:Mink.Poincare)(t:M'.Chip)(f:Test4)(x:M'.Model S Ω):V.V p (M'.lens S Ω (M'.fieldMap S Ω t f x))=M'.lens S Ω ( M'.fieldMap S Ω (M'.βL p.Λ t) (Joint.push p f) (M'.emergeC S Ω p V lift x))
 field_linear (n:α)(x y:colorP (M'.P n).amount)(a:ℂ)(f:Test4):M'.fieldMap S Ω (⟨n,x+a • y⟩:M'.Chip) f= M'.fieldMap S Ω (⟨n,x⟩) f+a • M'.fieldMap S Ω (⟨n,y⟩) f
 hermitian (t:M'.Chip)(f:Test4)(x y:M'.Model S Ω): inner ℂ (M'.lens S Ω (M'.fieldMap S Ω t f x)) (M'.lens S Ω y)= inner ℂ (M'.lens S Ω x) (M'.lens S Ω (M'.fieldMap S Ω (M'.mirrorK t) (Probe.bar f) y))
 tempered (t:M'.Chip)(x:M'.Model S Ω): Continuous (fun f=> M'.lens S Ω (M'.fieldMap S Ω t f x))
 localC (t u:M'.Chip)(f g:Test4)(p:Fields.causal f g): Commute (M'.fieldMap S Ω t f) (M'.fieldMap S Ω u g)
 pvm : V.orbit.Spectrum S.ℚmeasure
 forward : S.ℚmeasure.region Mink.coneᶜ=0
 -- only claim Unique if appointment chooses such α.E (available; see WP7)
 unique : (∀ x:H,(∀ p:E4,M S p x=x)→ ∃ z:ℂ,x=z • Ω.val) →∀ x:H,(∀ p:E4,V.orbit.translation p x=x)→∃ z:ℂ,x=z • Ω.val
 determines (t:M'.Chip)(A:H.Op) : A=M'.dep t ↔ ∀ (x:M'.Model S Ω) (g:Test4), M'.lens S Ω (M'.fieldMap S Ω t g x)=(ℑ S A g (M'.grade t) x.val).val
 rec_clock (S': OS.Semigroup H timeAxis) : (∀ x:E4,V.orbit.translation x=M S' x)→ S=S'
 -- don't propagate Eu analytic assertions under extramultiplet siblings
structure Earned : Prop where
 -- Include separated moment fits.A.P
 realRoad (n:ℕ)(x:Points n)(f:Fin n→ M'.Chip) (L:List (Fin n)) (e:L.Perm (Each n))(t: ProofOrder x timeAxis L): ornate M' S Ω x f= Sr M' S Ω x f L
 smoothNow (n:ℕ)(f:Fin n→ M'.Chip): ContinuousOn (fun x=> ornate M' S Ω x f) (conf n)
 Euclidean(n:ℕ)(x:Points n)(p:x∈conf n)(f:Fin n→ M'.Chip)(s:SO)(u:E4): ornate M' S Ω x f= ornate M' S Ω (moving u (turnO s.val x)) (M'.stampE s f)
 symmetry(n:ℕ)(x:Points n)(p:x∈conf n)(e:Equiv.Perm (Fin n))(f:Fin n→ M'.Chip): ornate M' S Ω x f = ornate M' S Ω (regP e x) (f ∘ e)
 history0(n:ℕ)(t:Ray)(f: Fin n→ M'.Chip) : ∃ X, PCost M' S Ω t f X
 history(n:ℕ)(t:Ray)(f: Fin n→ M'.Chip)(g:Fin n→ Test4)(Y:ℕ→Points n→ℂ→ℂ)(p:PCost M' S Ω t f Y):
      (∀ i:ℕ,Integrable (fun x=> Joint.materialize n g x * Y i x I)) ∧ Tendsto (fun i=> ∫ x,Joint.materialize n g x * Y i x I) atTop (𝓝 (Canopy.Wval M' S Ω f g))
 Wmoment (n:ℕ)(t:Fin n→ M'.Token): M'.Wval S Ω (fun i=>(t i).1) (fun i=>(t i).2)=inner ℂ Ω.val (M'.lens S Ω (M'.focus S Ω (List.ofFn t)))
variable (k:∀ b:Mink.Ray,Shelf S (magnet b))(V':Tile M' S Ω)(E:M'.Climb S Ω=⊤)
include hΩ k V'
lemma arrivals (E:M'.Climb S Ω=⊤)(v:‖Ω.val‖=1)(p:S.ℚmeasure.region Mink.coneᶜ=0)(l:Loom M' S Ω): ∃ V:Boundary.Action H,M'.Arrival S Ω V:=by
 obtain ⟨V, Z⟩:=actionC M' S Ω hΩ (M'.tilt_good S Ω V') k E; let G:=V.orbit; have he(x:E4):G.translation x=M S x:= M'.subsidiary S Ω hΩ E V Z x; refine ⟨V, he, Model_foot M' S Ω E,road .., fun x w=> convene .., Z,v, fun p=> Z p [], fun p t=> (rootR M' S Ω p V Z t).symm, fun p t f x=>M'.costs S Ω p (t,f) V Z x, ?_,fun t f x y=> agenda M' S Ω t f x y,fun t x=> spaces .. ,fun t u f g p=> leanR M' S Ω t u f g V Z l p, ?_,p,?_,?_,?_⟩
 · intro n x y c f; change M'.operator S Ω _ f= M'.operator S Ω _ f+ c • M'.operator S Ω _ f; rw [oV_add,oV_smul]
 · rw [show V.orbit=S.unit from ?_]; exact S.joint
   apply (show ∀ U Z:Spectral.Orbit H E4,U.translation=Z.translation → U=Z from fun U Z H=>by cases U; cases Z; congr); exact funext he
 · intro t x q; apply t; intro p; rw [← he]; exact q p
 · intro x A; exact ⟨fun p i g=> p ▸ rfl, fun h=> (priority M' S Ω hΩ x E A h).symm⟩
 exact fun S' p=> derive_full S S' (funext fun x=> (he x).symm.trans (p x))
lemma eldership : Earned M' S Ω := { realRoad := fun _ x f L E t=>sing M' S Ω x f L V' E t
                                     smoothNow := fun _ f x h=> (openly M' S Ω x f V' h).continuousWithinAt
                                     Euclidean := fun _ x h f s u=> (fluent M' S Ω s x f V' h).trans (bliss M' S Ω hΩ _ _ V' (warm_π x s h) u)
                                     symmetry := fun _ x p e f=> uniformizes M' S Ω x f V' e p
                                     history0:= fun _ t f=> ⟨_,embarks M' S Ω hΩ t (k t) f⟩
                                     history := fun _ t f g _ p=> resurgence M' S Ω hΩ t (k t) f g _ p
                                     Wmoment:=fun _ _=> worlddoc .. }
#print axioms eldership
#print axioms arrivals
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
