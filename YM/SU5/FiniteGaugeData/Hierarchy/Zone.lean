import YM.SU5.FiniteGaugeData.Hierarchy.Rigid
/-! # The algebra at each observing resolution

All of the wide physically gauge-invariant families (pair marks allowed), and therefore all narrow as well. `Sites` and `Placeable` below are always the cover sites at that SAME resolution. No uniformly supported-family fiction here: integer changes of resolution and Frontier propagation are real. Include one advancement layer globally. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Charm
open Tint
section gauge
variable (K:Calibration)(S:Finset Cover)

def allG : Subalgebra ℂ (Family K) where
  carrier:={x| Durable K x}
  algebraMap_mem' c:=by rw [Algebra.algebraMap_eq_smul_one]; change Durable K _; intro n g x; simp only [Pi.smul_apply,Pi.one_apply,twist_scalar,map_one]
  mul_mem' {a b} (v: Durable K a) (t:Durable K b):=by change Durable K _; intro n g x; simp only [Pi.mul_apply,v n g x,t n g x,map_mul]
  add_mem' {a b} (v: Durable K a) (t:Durable K b):=by change Durable K _; intro n g x; simp only [Pi.add_apply,v n g x,t n g x,map_add]

def well : Subalgebra ℂ (Family K):= wideAlg K ⊓ allG K

def zone : Subalgebra ℂ (Family K):= localWide K S ⊓ allG K
lemma zone_mono : Monotone (zone K):=fun _ _ p=> inf_le_inf (localWide_mono K p) le_rfl
lemma zone_le: zone K S ≤ well K:= inf_le_inf (localWide_le ..) le_rfl
lemma well_for (x:↥(well K)): TestFamily K true x.val ∧ Durable K x.val:= x.property
lemma sites (x:↥(well K)): ∃ S,x.val∈ zone K S:= by obtain ⟨s,p⟩:=(well_for K x).1.paid; exact ⟨s,p,(well_for K x).2⟩
abbrev W := ↥(well K)

def Locator (x:W K)(S:Finset Cover):Prop:= InTest K true S false x.val
theorem testimony (x:W K):∃ S,Locator K x S:= (well_for K x).1.paid

def reading (x:W K)(p:Locator K x S):Catalog S:=certifyAs S K _ p
lemma reading_p (x:W K)(p:Locator K x S):composeQ K S (reading K S x p)=x.val:=certified ..
@[simp] lemma joinW (x y:W K) : Subtype.val (p:=fun a=>a∈well K) (x*y)=x.val*y.val := rfl
lemma identityW : (1:W K).val=(1:Family K):= rfl
lemma locate_one : Locator K 1 S:= InTest.one
lemma locate_sub {S T:Finset Cover}{x:W K}(p:Locator K x S)(e:S⊆T):Locator K x T:= InTest.mono p e
lemma locate_scale (a:ℂ){x:W K}(e:Locator K x S) :Locator K (a • x) S:= InTest.smul a e
lemma locate_sum {x y:W K}(p:Locator K x S)(q:Locator K y S):Locator K (x+y) S:= InTest.add p q
lemma locate_zero :Locator K 0 S:=InTest.zero
lemma locate_join {x y:W K}(p:Locator K x S)(q:Locator K y S):Locator K (x*y) S:= InTest.mul p q
lemma commW (x y:W K):x*y=y*x:= Subtype.ext ((well_for K _).1.comm (well_for K _).1)

-- across a calibration `takes` proviso -> actual singlet because check a roomy period, even small accidental symmetries then agreed across all periods
lemma narrow_indeed (x:Family K)(p:TestFamily K false x): x∈ well K:=by
  obtain ⟨S,t⟩:=p.paid; refine ⟨⟨⟨S,t.widen⟩,by simp⟩,?_⟩; change Durable K x
  obtain ⟨n,e⟩:= eventually_atTop.mp ((roomy_sides S K).and (p.allowed rfl))
  let A: Side:=⟨2*n.val+1,by positivity⟩; let m:=K.q*A; have hm:n≤ m:=by change n.val≤ K.q.val*(2*n.val+1); have he:1≤ K.q.val:=K.q.property; nlinarith
  exact budgeted t.widen (roomy_hosp _ ((e m hm).1)) ((e m hm).2 ⟨A,⟨n.val,rfl⟩,rfl⟩)

-- reflection * at any plane (not translation-free star of ordinary CAR C* algebra).
def fire (a:Axis)(z:ℤ)(x:W K): W K:=
  let v:= well_for K x; let P:= v.1.paid.choose_spec
  ⟨reflector a z x.val,⟨⟨⟨_,reflects a z P⟩,by simp⟩,(show Durable K _ from fun m=> covariant_reflected (P.support m) (v.2 m) _ _)⟩⟩
lemma ice_central (a:Axis)(z:ℤ): fire K a z 1=1 := Subtype.ext (ice_identity ..)
lemma ice_print (a:Axis)(z:ℤ)(x:W K): (fire K a z x).val=reflector a z x.val:=rfl
lemma ice_join (a:Axis)(z:ℤ)(x y: W K):fire K a z (x*y)=fire K a z x*fire K a z y:=Subtype.ext (ice_times ..)
lemma ice_more (a:Axis)(z:ℤ)(x y: W K):fire K a z (x+y)=fire K a z x+fire K a z y:=Subtype.ext (ice_plus ..)
lemma ice_paid (a:Axis)(z:ℤ)(x:W K) (t:ℂ):fire K a z (t • x)=star t • fire K a z x:=Subtype.ext (ice_scale ..)
lemma locate_cold (a:Axis)(z:ℤ){x: W K}(p:Locator K x S):Locator K (fire K a z x) (refract a z S):= reflects a z p
lemma burning_ice (a:Axis)(z:ℤ)(x:W K):fire K a z (fire K a z x)=x:=Subtype.ext (ice_twice a z (well_for K x).1.paid.choose_spec)
end gauge
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
local notation "U"=> W (tent Y h)
local notation "D"=> GridStep Λ l
include K R
-- include cutoff schedule only for genuine representative choice

def next (x: W (tent Y h)) : W (tent Y h) :=
 let s' := (testimony Kₜ x).choose
 let p:=reading Kₜ s' x (testimony Kₜ x).choose_spec
 let q: Durable Kₜ (composeQ Kₜ s' p):= (reading_p Kₜ s' x _).symm ▸ (well_for Kₜ x).2
 ⟨composeQ Kₜ (GridStep Λ l s') (P s' s p), ⟨compose_test .., Tint.preserved Y h s' s K R _ q⟩⟩

private lemma inherits {S T:Finset Cover}(p:S⊆ T) (x:U)(a:Locator Kₜ x S)(e:Locator Kₜ x T):
 composeQ Kₜ (GridStep Λ l S) (P S s (reading Kₜ S x a))= composeQ Kₜ (GridStep Λ l T) (P T s (reading Kₜ T x e)) := by
 rw [←incl_id (K:=Kₜ) (grid_mono S T (Λ:=Λ) (l:=l) p), coherence Y h S T s K R p]
 have hu:incl Kₜ p (reading Kₜ S x a)= reading Kₜ T x e:= compose_inj T Kₜ (by rw [incl_id, reading_p,reading_p]); rw [hu]
lemma keeps (x:U)(p:Locator Kₜ x S): (next Y h s K R x).val= composeQ Kₜ W₀ (P S s (reading Kₜ S x p)) := by
 unfold Charm.next; let e:=(testimony Kₜ x).choose_spec; let T:=(testimony Kₜ x).choose; let h:= locate_sub Kₜ e (T:=T∪S) subset_union_left; exact (inherits Y _ s K R subset_union_left x e h).trans (inherits Y _ s K R subset_union_right x p h).symm
lemma locate_next (x:U)(p:Locator Kₜ x S): Locator Kₜ (next Y h s K R x) (GridStep Λ l S):=by unfold Locator; rw [keeps Y h S s K R x p]; exact compose_t ..
lemma next_cert (x:U)(p:Locator Kₜ x S)(u:Catalog S)(e:composeQ Kₜ S u=x.val):
    (next Y h s K R x).val=composeQ Kₜ W₀ (P S s u):=by
  rw [keeps Y h S s K R x p]; rw [show reading Kₜ S x p=u from compose_inj S Kₜ ((reading_p _ _ _ p).trans e.symm)]
lemma next_mir (a:Axis)(z:ℤ)(x:U) : next Y h s K R (fire Kₜ a z x)=fire Kₜ a ((Λ.R.L.val:ℤ)*z) (next Y h s K R x):=by
  obtain ⟨S,p⟩:= testimony Kₜ x
  apply Subtype.ext
  let f:= reading Kₜ S x p; have e:composeQ Kₜ S f=x.val := reading_p ..
  rw [ice_print,next_cert Y h S s K R x p f e,next_cert Y h (refract a z S) s K R _ (locate_cold Kₜ S a z p) (mirrorL Kₜ a z S f) ?_,turn_P Y h S s K R]
  exact (mirrorC_id Kₜ a z S f).trans (congrArg (reflector a z) e)
lemma next_sum {x y:U}: next Y h s K R (x+y)=next Y h s K R x+next Y h s K R y:=by
  obtain ⟨T,t⟩:= testimony Kₜ x; obtain ⟨S,q⟩:=testimony Kₜ y
  let a:=locate_sub Kₜ t (T:=T∪S) subset_union_left; let b:= locate_sub Kₜ q (T:=T∪S) subset_union_right
  let x':= reading Kₜ _ x a; let y':= reading Kₜ _ y b
  have e: composeQ Kₜ _ x'=x.val:=reading_p ..; have h': composeQ Kₜ _ y'= y.val:= reading_p ..
  apply Subtype.ext; rw [Subalgebra.coe_add,next_cert Y h _ s K R x a x' e,next_cert Y h _ s K R y b y' h',next_cert Y h _ s K R (x+y) (locate_sum Kₜ _ a b) (x'+y') (by rw [map_add,e,h']; rfl), map_add,map_add]
lemma next_smul (x:U)(z:ℂ):next Y h s K R (z • x)=z • next Y h s K R x:=by
  obtain ⟨T,t⟩:= testimony Kₜ x
  let x':= reading Kₜ _ x t
  have e: composeQ Kₜ _ x'=x.val:=reading_p ..
  apply Subtype.ext; rw [Subalgebra.coe_smul,next_cert Y h _ s K R x t x' e,next_cert Y h _ s K R (z • x) (locate_scale Kₜ _ z t) (z• x') (by rw [map_smul,e]; rfl), map_smul,map_smul]
-- identity leaves no unsupported factors
lemma next_unit : next Y h s K R 1=1:= Subtype.ext ((next_cert Y h ∅ s K R 1 (locate_one ..) (unitQ Kₜ ∅) (unitQ_id ..)).trans (by rw [unit_roll Y h _ s K R,unitQ_id]; rfl))
lemma separate {x y:W (tent Y h)} (p:Locator Kₜ x S)(a:Locator Kₜ y T)(g:Range (spaceBill Λ l) S T):
    next Y h s K R (x*y)= next Y h s K R x * next Y h s K R y:=by
  let x':= reading Kₜ _ x p; let y':= reading Kₜ _ y a
  have e: composeQ Kₜ _ x'=x.val:=reading_p ..; have h': composeQ Kₜ _ y'= y.val:= reading_p ..
  apply Subtype.ext; rw [joinW, next_cert Y h _ s K R x p x' e, next_cert Y h _ s K R y a y' h', next_cert Y h (S∪T) s K R _ (locate_join Kₜ (S∪T) (locate_sub Kₜ p subset_union_left) (locate_sub Kₜ a subset_union_right)) (timesQ Kₜ subset_union_left subset_union_right x' y') ?_,festive Y h S T s K R (S∪T) _ _ _ _ g,timesQ_id]; rw [timesQ_id,e,h',joinW]
lemma foundation (x:U) : E (s+1) (next Y h s K R x).val=E s x.val:=by
  obtain ⟨S,p⟩:=testimony Kₜ x; rw [keeps Y h S s K R x p,←headlined Y h S s K R, reading_p]
#print axioms foundation
#print axioms separate
end Charm
end YM.CF.Buffered.Afterglow.Hierarchy
