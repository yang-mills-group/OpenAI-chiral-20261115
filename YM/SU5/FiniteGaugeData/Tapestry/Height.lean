import YM.SU5.FiniteGaugeData.Tapestry.Levels
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
# Common physical plane and paid half space

Planes use **gauge coordinates** (at level s), so in propagation of reflection
or the positive-half input to a form, use the *same* plane scaled by Λ.R.L at
each successive level. The absolute margin in these units can stay fixed in the
upper level.
-/
open Mir Phase RP Nacre Girt
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S T:Finset Cover)(s i k:ℕ)(α:Axis)(z:ℤ)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (X:Exhibition Y H a b I E L B)

local notation "K"=> tent Y H
local notation "Ω" i:max => side Y i s
local notation "U"=> followBox (Λ:=Λ) (l:=l) S
local notation "R" => reserve Λ l

abbrev Ledge (Λ:Preparation)(l:ℕ)(S:Finset Cover)(α:Axis)(z:ℤ):Prop:=∀ x∈S, z+reserve Λ l ≤ x α
abbrev Scaled (Λ:Preparation)(z:ℤ):=(Λ.R.L.val:ℤ)*z
theorem Ledge.taller (p:Ledge Λ l S α z): Ledge Λ l (followBox (Λ:=Λ) (l:=l) S) α (Scaled Λ z) := by
  let r:= Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
  have he : R+r ≤ Λ.R.L.val * R := margin_step (prepared Λ l) Λ.R.coarse
  intro x v; obtain ⟨a,u,V⟩:= mem_biUnion.mp v; obtain ⟨y,t,rfl⟩:= mem_image.mp V; obtain ⟨a,hK,rfl⟩:= mem_image.mp u
  have ht:-(r:ℤ)≤ y α:= (box_test.mp t).1 α
  simp only [Pi.add_apply,nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]; have hg: (R:ℤ)+r ≤ (Λ.R.L.val:ℤ)*R:=by exact_mod_cast he
  unfold Scaled; nlinarith [p a hK, (show 0 < (Λ.R.L.val:ℤ) by positivity)]
theorem Ledge.join (p:Ledge Λ l S α z)(q:Ledge Λ l T α z) : Ledge Λ l (S∪T) α z:=fun x e=> (mem_union.mp e).elim (p x) (q x)

private lemma fitsHere (K':Calibration){e:ℕ}(p:∀ x∈S,z+e ≤ x α) : ∀ᶠ m in atTop, region S (K'.c m) ⊆ band (K'.c m) α z e:=by -- band K ambiguity
  have h : ∀ᶠ m in atTop, ∀ x∈ S, x α + e ≤ z+(K'.c m).val := (eventually_all_finset S).mpr fun x hx=> by
    filter_upwards [(c_grows K').eventually_ge_atTop (x α + (e:ℤ) - z).toNat] with n v; change _≤(K'.c n).val at v; omega
  filter_upwards [h] with m w x t
  obtain ⟨x,h,rfl⟩:= mem_image.mp t; apply (band_spec ..).2
  let n:=K'.c m; let j:=x α - z; have hp:= p x h; have he:=w x h; have hz : 0 ≤ j:= by unfold j; omega
  have hn: 0 < (K'.c m).val:= n.property; have ht: j.toNat < (More n).val:=by change _<n.val*2; unfold j n; omega
  have hl : (wrap (More n) x) α - (z:Per (More n))= (j.toNat:Per (More n)):=by rw [←Int.cast_natCast,Int.toNat_of_nonneg hz,show (j:Per (More n))=(x α:Per (More n))-(z:Per (More n)) from Int.cast_sub ..]; rfl
  rw [hl,ZMod.val_natCast_of_lt ht]; unfold j; omega
include H
lemma eventuallyFits (p:Ledge Λ l S α z): ∀ᶠ i:ℕ in atTop, region S (side Y i s) ⊆ band (side Y i s) α z R:=by
  filter_upwards [(momentum Y s).eventually (fitsHere S α z K p)] with i w; unfold side; rw [←terrain Y H]; exact w

lemma reflectedSep (p:Ledge Λ l S α z) (k:Ledge Λ l T α z) : ∀ᶠ i:ℕ in atTop,∀ x∈region (negativeSide S z α) (Ω i),∀ y∈region T (Ω i),2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation x y:=by
  filter_upwards [eventuallyFits Y H S s α z p,eventuallyFits Y H T s α z k] with i g t x e y u
  apply margin_separate α z (prepared Λ l) x y _ (t u)
  refine image_subset_image g ?_
  obtain ⟨b,v,rfl⟩:= mem_image.mp e; obtain ⟨m,w,rfl⟩:= mem_image.mp v
  rw [←Shape.anno]; exact mem_image_of_mem _ (mem_image_of_mem _ w)

include X
open Heat
private lemma canopy (f:Family K) (h:TestFamily K true f): I s f=X.univ_.pick.field Y H s f ∧ E s f=X.univ_.pick.audience Y H s f:=by
  let p:= X.univ_.pick.booked Y H s h; have e:= X.univ_.together s _ h; have he:I s f=X.univ_.pick.field Y H s f:=funext fun i=> tendsto_nhds_unique (e.inner i) (p.2.inner i)
  refine ⟨he, tendsto_nhds_unique e.periods ?_⟩; rw [he]; exact p.2.periods
lemma fireside (p: Ledge Λ l S α (gaugeShift Λ.block z)) (f: Swatch S) :
  0 ≤ E s (bounce K (gaugeShift Λ.block z) α (render S K f) * render S K f):= by
  let z':= gaugeShift Λ.block z; let F:=render S K f; let t:=bounce K z' α; let G:= t F*F; let p':= X.univ_.pick
  have he : TestFamily K true G:= (broadCompile K (negativeSide S _ _) (bounceEligible z' α (texture S K f))).mul (broadCompile K S (texture ..))
  rw [(canopy Y H s X G he).2]; apply ge_of_tendsto (p'.booked Y H s he).1.periods
  filter_upwards [((momentum Y s).comp X.univ_.pick.grow_i.tendsto_atTop).eventually (fitsHere S α z' K p)] with i v
  apply ge_of_tendsto ((p'.booked Y H s he).1.inner (a i))
  filter_upwards [p'.pass Y H s (a i)] with j q; unfold hot; rw [dif_pos q.depth]; let m:= momentm Y (a i) s
  exact (boxprice Y H _ _ q.depth s q.fire q.enters).fund α z (F m) (((texture S K f).support m).mono v)
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.fireside
