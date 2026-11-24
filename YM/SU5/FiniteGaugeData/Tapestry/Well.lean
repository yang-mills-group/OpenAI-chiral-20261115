import YM.SU5.FiniteGaugeData.Tapestry.Cloudburst
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Gauge-invariant local polynomials (can take **only** genuine first-Pane
probes with continuous link data, as determining resolution observable system).
Caveats about cross-even and continuation beyond this resolution system discussed
in the guide. No extraneous quotient by possible degeneracies of the state when
we say `well` is the physical algebra. Show it exactly covers all cylinder
questions in this hierarchy using the indicated chiral fields and original
frames. And at any single observing level with enough room, ALL local chiral-spin
Mark/Eval inputs even (with qualification first-field continuous where appropriate)
can be expressed with those probes. Thus not merely bare Wilson terms and ads
for the paid words, it is a full algebra as measured at these resolutions.
-/
set_option quotPrecheck false
section
variable (Λ:Preparation)(K:Calibration)
private def standing : Subalgebra ℂ (Cloud (Dome K)) where
 carrier:= {f| ∀ u:GPhysical,rainfall Λ K u f=f}
 zero_mem':= fun u=> map_zero _
 one_mem':= fun u=> map_one _
 add_mem':= fun (p : ∀ u,_) (q : ∀ u,_) u=> (map_add (rainfall Λ K u) _ _).trans (congrArg₂ (·+·) (p u) (q u))
 mul_mem':= fun (p : ∀ u,_) (q : ∀ u,_) u=> (map_mul (rainfall Λ K u) _ _).trans (congrArg₂ (·*·) (p u) (q u))
 algebraMap_mem':=fun z u=> (rainfall Λ K u).commutes z
-- ignore field type assignments before calibration K; here consumes Λ even in action
variable (l:ℕ)(wide: Bool)(V W:Set RSpace)(s t:Set ℕ)
def well : Subalgebra ℂ (Cloud (Dome K)):= jetty Λ l K wide V s⊓ standing Λ K
lemma well_spec {x: Cloud (Dome K)}: x∈ well Λ K l wide V s ↔ x∈ jetty Λ l K wide V s ∧ ∀ u:GPhysical,rainfall Λ K u x=x:= Iff.rfl
-- 'exactly the coherent gauge-invariant polynomials'
lemma determinant {x: Cloud (Dome K)} : x∈ well Λ K l wide V s ↔
  x∈ Algebra.adjoin ℂ (⋃ i∈s,(pinhole (Dome K) i) '' (keep Λ l i K wide V:Set (Dome K))) ∧
   ∀ u:GPhysical, rainfall Λ K u x=x:=by rw [well_spec,generating]
lemma wellGrows (p:s⊆t)(h: V⊆W): well Λ K l wide V s ≤ well Λ K l wide W t:= inf_le_inf (admits Λ l K wide V W s t p h) le_rfl
lemma wellWider : well Λ K l wide V s≤well Λ K l true V s:=inf_le_inf (exposes ..) le_rfl
lemma wellPolynomial : well Λ K l wide V s≤ FiniteGaugeDataPoly K:= le_trans inf_le_left (jets ..)
lemma gateIssued(n:ℕ): well Λ K l wide V (s∩ Set.Iic n)≤ shorter (Dome K) n:= le_trans inf_le_left (jettyBan ..)
lemma declaredGate {x:Cloud (Dome K)}(h:x∈ well Λ K l wide V s): ∃ n:ℕ, x∈ well Λ K l wide V (s∩ Set.Iic n):=by
 have v:= (well_spec ..).mp h; obtain ⟨n,u⟩:= entrusted Λ l K wide V s v.1; exact ⟨n,(well_spec ..).mpr ⟨u,v.2⟩⟩
lemma wellExhaustion (x:Cloud (Dome K))(p:x∈well Λ K l wide V s) : ∀ᶠ n:ℕ in atTop,x∈well Λ K l wide (V∩ cabin n) s:=
 let z:= (well_spec ..).1 p; (cabined Λ l K wide V s x z.1).mono fun n v=> (well_spec ..).2 ⟨v,z.2⟩
lemma flipWell (α:Axis) (z: Sunlight Λ)(t:s⊆ z.arena Λ){x: Cloud (Dome K)}(h:x∈well Λ K l wide V s):
    Sunlight.oppose Λ α z K x∈ well Λ K l wide (mirrorE α (z.hinge Λ) '' V) s:=by
 obtain ⟨p,g⟩:= (well_spec ..).1 h; refine (well_spec ..).2 ⟨z.opposition Λ l α K t V wide p, fun u=>?_⟩; rw [rainReflect Λ K u l s V wide z α t p, g]
-- including generator (and e.g. every Native in a bounded region depending on it)
lemma oneSlotColor (i:ℕ) (x:Dome K): (∀ u:GPhysical, rainfall Λ K u (pinhole _ i x)=pinhole _ i x) ↔ x∈enclave K:=by
 rw [colorFixed]; refine ⟨fun h R=>?_,fun p u=>?_⟩
 · obtain ⟨U,hU⟩:=iceExtension Λ i R; rw [← hU]; exact localDomeInj K i ((gaugesSlot Λ K i U x).symm.trans (h _))
 rw [gaugesSlot,p]
lemma oneSlotWell (i:ℕ)(p:i∈s){x:Dome K}(h:x∈keep Λ l i K wide V)(t:x∈enclave K): pinhole (Dome K) i x∈ well Λ K l wide V s:= (well_spec ..).mpr ⟨pokes s _ p h,(oneSlotColor ..).2 t⟩
lemma allNative (i:ℕ)(p:i∈s){x:Dome K}(h:x∈Native K): pinhole _ i x∈ well Λ K l false Set.univ s := by
  rcases (show x∈vestibule K false∧ _ from h) with ⟨u,q⟩; exact oneSlotWell Λ K l false _ s i p ((fullKeep Λ l i K false).symm ▸ u) q
end
section torus
variable (K:Calibration)(m:Side)(S:Finset Cover)
-- all local continuous questions in room, from regulator into `Dome`
private lemma growsCont (n:Side): Continuous (graft S n) := by
 apply continuous_pi; intro t; unfold Satin.graft; split
 · exact continuous_apply _
 exact continuous_const
private lemma firstAppear {g:Window.Evaluation (K.c m)} (h:Continuous g) (x:Swatch S)(p: Hosp S (K.c m))(q : appear S K m x=toMark g): InTest K false S false (render S K x):=by
  rw [render_eq]; refine InTest.sum _ _ ?_; intro i t
  have e:Coeff true S (daub S (x i)):= authentic ..
  have f:Coeff false S (daub S (x i)):= by
     refine ⟨fun _=>?_,e.env, e.locus⟩
     let V(z:LinksC):= eye S K m p i (g (graft S (K.c m) z)); refine ⟨V,(LinearMap.continuous_of_finiteDimensional _).comp (h.comp (growsCont S _)),funext fun z=>?_⟩; rw [←eye_readCover S K m p x z i,q]; rfl
  simpa only [i.property] using note_t K (tagWord S i.val) f (brand S i.val)
-- includes support even & covariant condition on m. Needs injectivity + tips exactly, survives at all other periods.
lemma completeBay (f : Mark (K.c m))(p:AtSupport false (region S (K.c m)) f)(Z:Roomy S (K.c m))(wide: Bool)(g:wide=false → ∃ W:Window.Evaluation (K.c m), f=toMark W ∧ Continuous W) :
    ∃ x : Swatch S, badge K S x ∈ bay K S wide ∧ (badge K S x).val m=f∧(covariant f → badge K S x∈enclave K) ∧ ∀ (C:ℝ), (∀ v, ‖f v‖ ≤ C) → ‖x‖ ≤ C:=by
  let u:= mend S K m Z p; have hv:appear S K m u=f:= appear_mend S K m Z p; refine ⟨u,?_,hv,(fun k=>?_), fun C W=>sampling S K m (Roomy.seats Z) u (fun v=>by rw [hv]; exact W v)⟩
  · cases wide; swap; exact locatesBadge ..
    obtain ⟨v,e,w⟩:=g rfl; exact firstAppear K m S w u (Roomy.seats Z) (hv.trans e)
  exact onceNeutral (texture S K u) (m:=m) (Roomy.seats Z) (by change covariant (appear S K m u); rw [hv]; exact k)
end torus
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.completeBay
#print axioms YM.CF.Buffered.Afterglow.Tapestry.determinant
#print axioms YM.CF.Buffered.Afterglow.Tapestry.allNative
#print axioms YM.CF.Buffered.Afterglow.Tapestry.flipWell
