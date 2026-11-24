import YM.SU5.Selected.Energy
/-!
# Keeling: Single-tick positivity (including for the conditioned states)

For time stamps of `Heat`, `Sunlight`, etc, there's a subtle point. Strip evolution on the OS
0-plane is given as a norm continuous law for *positive* length on the **even**-mesh; don't
assume its square roots at odd subdivision numbers are given by the label tick numbers.
`Coherent` does however buy reflection-positivity for all gaugeShift planes, including the
HALF-planes of even of the single-tick. We prove that this **gives nonnegativity on the full
space of the model of the single-tick**, even with the support buffer (the test already clears
this half plane when translated by ≥ twice that much). Thus the semigroup must be right also
at these half steps. Then we use the actual `station` representation to deduce that
in the selected state(s) the same applies. Needed before asserting positivity/coherence at planes
not based on 16B-aligned stamp in all levels.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open Tapestry.Exhibition Set
namespace Spine
variable (P : Spine)(j : Axis)
local notation "W"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "V"=> P.law
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "M"=> timeMesh P.par
local notation "σ" x:max => P.shifts j x
local notation "Ω"=> P.Hil j
local notation "R" n:max=> Heat.gaugeShift P.par.block n
local notation "Θ"=> P.reflectTest j
local notation "χ" n:max=> tick P.run P.large n j 0 false
local notation "Δ" n:max f:max=> P.voxTest j n f
local notation "κ" i:max=> P.piece j i
variable (s : ℕ)
def halfTime (n : ℕ):ℝ≥0:= MeshClock.whenly (timeMesh P.par) s n / 2
local notation "W₀" n:max=> P.halfTime s n
abbrev Keeling (n:ℕ) : P.Op0 j := ripple P.run P.large P.law s P.history.circuit j 0 false (P.room j) n
lemma keel_at (t n : ℕ) (p:s≤t) (f : P.Vox j t) : P.Keeling j s n ((κ t) f)=(κ t) ((χ t) (amount P.par s t n) f):= limited_time Y H V s (π).circuit j 0 false C₀ n p f
lemma keel_star (n : ℕ) : star (P.Keeling j s n)=P.Keeling j s n:=current_adjoint Y H V s (π).circuit j 0 false C₀ n

-- reflection/equal-time Haus grants
lemma keel_positive_base (n : ℕ)(x:P.Vox j s) : 0 ≤ inner ℂ ((κ s) x) (P.piece j s ((χ s) n x)):=by
  obtain ⟨v,Hw⟩:= (purpose_ok ..).mp x.property
  obtain ⟨S,p,v⟩:= (v:∃ S:Finset Cover, InTest W true S false (x.val) ∧ Tower.region j (meshface (Λ:=P.par) 0 s) (W).ℓ S)
  let z:=(R (n:ℤ)); let f:= chime W j z x.val
  have ht: mirror W j z f=mirror W j 0 x.val:= reversal W j z (axial W j 0 p)
  have h:0≤ z:=by unfold z gaugeShift; positivity
  let A:=address j z S; have ha: Tower.region j z (W).ℓ A:=by
    intro y q; obtain ⟨y,e,rfl⟩:= Finset.mem_image.mp q; rw [moves j j,if_pos rfl]; specialize v y e; rw [area0] at v; change 0+(W).ℓ ≤ y j at v; omega
  have hu:= boson_axial Y H V s (flow_port W j z p) ha
  rw [P.seed_pairing,← ht]; exact hu
private lemma keel_nonneg_ (n:ℕ) (x:Ω) : 0 ≤ inner ℂ x (P.Keeling j s n x):=by
  have hp : IsClosed {x|0 ≤ inner ℂ x (P.Keeling j s n x)} := isClosed_le continuous_const (continuous_id.inner (P.Keeling j s n).continuous)
  apply closure_minimal _ hp (sounds Y H V (π).circuit j 0 false C₀ x); intro a p; obtain ⟨t,p⟩:=Set.mem_iUnion.mp p; obtain ⟨b,rfl⟩:=p; let v:=max s t; let h:=le_max_left s t; let u:=le_max_right s t
  change 0≤ inner ℂ (actor Y H t (π).circuit j 0 false C₀ b) (P.Keeling j s n (actor Y H t (π).circuit j 0 false C₀ b))
  rw [←join_actor Y H V (π).circuit j 0 false C₀ t v u]; unfold Keeling; rw [limited_time Y H V s (π).circuit j 0 false C₀ n h]
  exact P.keel_positive_base j _ _ _
lemma keel_nonneg (n : ℕ) : 0 ≤ P.Keeling j s n:= by
  let K:=P.Keeling j s n; refine (ContinuousLinearMap.nonneg_iff_isPositive K).mpr ?_
  apply (ContinuousLinearMap.isPositive_iff' _).2 ⟨P.keel_star j s n,fun x=>?_⟩
  change 0 ≤ inner ℂ (K x) x; rw [← ContinuousLinearMap.adjoint_inner_right K,show K.adjoint=K from P.keel_star j s n]; exact P.keel_nonneg_ j s n x
lemma keel_along (n : ℕ) : P.Keeling j s n=P.euclOp j (W₀ n):=by
  have hp:0 ≤ P.Keeling j s n:=P.keel_nonneg j s n; have hv:0 ≤ P.euclOp j (W₀ n):= P.eucl_pos j (W₀ n)
  apply half_root _ hp hv; change (P.Keeling j s n).comp _= (P.euclOp j _).comp _; unfold Keeling euclOp; rw [breeds Y H V s,← advance_smag,halfTime,add_halves,advance_at,two_mul]
where half_root (A:Hilbert) {L M':A.Op} (p:0≤L)(q:0≤M') (h:L*L=M'*M'): L=M':=by
        nth_rw 1 [← CFC.sqrt_mul_self _ p]; rw [h,CFC.sqrt_mul_self _ q]
-- cap invariance via ground commutation. Single translations (first):
abbrev halfShiftL (x : ℤ): P.Test→ₗ[ℂ]P.Test where
  toFun f:= ⟨chime P.calibration j (R x) f.val,broadCompile _ _ (flow_port _ _ _ ((findsBay P.calibration f).choose_spec))⟩
  map_add' _ _:=Subtype.ext (chime_plus ..)
  map_smul' _ _:=Subtype.ext (chime_scale ..)
def halfShift (x:ℤ) : P.Test→ₐ[ℂ] P.Test := AlgHom.ofLinearMap (P.halfShiftL j x) (Subtype.ext (chime_unit ..)) (fun _ _=>Subtype.ext (chime_product ..))
local notation "Σh" x:max => P.halfShift j x
lemma halfShift_val (x:ℤ)(f:P.Test): (P.halfShift j x f).val=chime P.calibration j (R x) f.val:= rfl
lemma halfDouble (x : ℤ) : (Σh (2*x))=P.shifts j x:= AlgHom.ext (fun _=> rfl)
lemma halfSame (x y:ℤ)(f:P.Test): (Σh x) ((Σh y) f)= (Σh (x+y)) f:= by
  apply Subtype.ext; rw [P.halfShift_val,P.halfShift_val,P.halfShift_val,Tower.bumps W j _ _ ((marque ..).1 f.property).paid.choose_spec]
  unfold gaugeShift; ring_nf
lemma halfZero (f:P.Test): P.halfShift j 0 f=f:=Subtype.ext (by rw [P.halfShift_val,show R 0= 0 from by unfold gaugeShift; ring,wake W j ((marque ..).1 f.property).paid.choose_spec])
lemma halfMovesOf (n:ℕ)(x:P.Vox j s): Δ s ((χ s) n x)= (Σh (n:ℤ)) (Δ s x):=rfl
lemma forward_form (n:ℕ)(x:P.Vox j s): P.reading j s ((Σh (n:ℤ)) (Δ s x))= P.reading j s (Δ s x):=by
  rw [←P.halfMovesOf]; apply P.equal_reads
  rw [P.at_label,P.seed,P.at_label,P.seed,← amount_reset P.par s n,← P.keel_at j s s n (le_refl s) x];
  rw [P.keel_along]; apply ext_inner_left ℂ; intro a
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  let K:= P.euclOp j (W₀ n); have he : K.adjoint=K:=advance_adjoint ..; have hx:K a.val=a.val:=floor_rise ..; conv_lhs => rw [show P.euclOp j (W₀ n)=K.adjoint from he.symm]
  rw [ContinuousLinearMap.adjoint_inner_right,hx]
-- pi comp via star floor
lemma halfShiftReadN (f:P.Test)(n:ℕ): P.reading j s ((Σh (n:ℤ)) f)=P.reading j s f:= by
  obtain ⟨S,h⟩:=findsBay W f; obtain ⟨u,t⟩:= (P.supports_future j S).exists; let i:=u; let y:=P.positiveVox j s _ _ (P.shifts_support j u S h) t
  have hz : (σ (u:ℤ)) ((Σh (n:ℤ)) f)= (Σh (n:ℤ)) ((σ (u:ℤ)) f):=by rw [← halfDouble,P.halfSame,P.halfSame]; rw [add_comm]
  have hr:P.reading j s ((σ (u:ℤ)) ((Σh (n:ℤ)) f))=P.reading j s ((σ (u:ℤ)) f):=by rw [hz]; exact P.forward_form j s n y
  have H₁ :∀ f:P.Test,P.reading j s ((σ (u:ℤ)) f)=P.reading j s f:= fun f=>P.shifted_read j s u f
  rw [H₁,H₁] at hr; exact hr
lemma halfReads(x:ℤ)(f:P.Test): P.reading j s ((Σh x) f)=P.reading j s f:=by
  cases x with
  | ofNat n=> exact P.halfShiftReadN j s f n
  | negSucc n=> let t:ℤ:= ↑(n+1); rw [←P.halfShiftReadN j s _ (n+1),P.halfSame,show t + Int.negSucc n=0 from by unfold t; omega,P.halfZero]
lemma halfReflect (x:ℤ)(f:P.Test) : aureole W j (R x) f= (Σh x) ((Θ) f):=by
  apply Subtype.ext
  change mirror W j _ _= mirror W j _ (mirror W j 0 (mirror W j 0 f.val)); rw [mirror_invert W j 0 ((marque ..).1 f.property)]
lemma lightStar (x:ℤ)(f:P.Test): P.reading j s (aureole W j (R x) f)=star (P.reading j s f):=by rw [P.halfReflect,P.halfReads,P.reading_star]
-- sandwich paid slab in two same half pads (NO assumptions of bounded factors squeezed out of B)
def halfCard (n w:ℕ)(f:P.Card j s w): P.Card j s (w+n) := by
  let g:= tick Y H s j 0 false n f.val; refine ⟨g,?_⟩
  let z:=R (n:ℤ); obtain ⟨S,p,e⟩:=f.property
  have he:z≥0:=by unfold z gaugeShift; positivity
  have ht: ruler P.par.block*(n:ℤ)=4*z:=by unfold z ruler gaugeShift; ring
  have hp:InTest W true (address j z S) false g.val:=flow_port W j z p
  refine ⟨_,hp,?_⟩; intro y q; obtain ⟨y,t,rfl⟩:= Finset.mem_image.mp q; specialize e y t
  rw [moves j j,if_pos rfl,Nat.cast_add,mul_add,ht]; exact ⟨by linarith only [e.1,he],by linarith only [e.2,he]⟩
lemma half_card_val (n w:ℕ)(f:P.Card j s w):(P.halfCard j s n w f).val=(χ s) n f.val:= rfl
local notation "G" n:max p:max f:max=> furnished Y H s π j false _ f n p
lemma cardWalk (n t w:ℕ)(h:s≤t)(f:P.Card j s w): (G t h (P.halfCard j s n w f)).val=(χ t) (amount P.par s t n) (G t h f).val:=by
 change Raise Y H (π).circuit j 0 false s t h _= (χ t) _ (Raise Y H (π).circuit j 0 false s t h f.val)
 rw [P.half_card_val]; exact (tick_up Y H V s (π).circuit j 0 false t h f.val n).symm
def voxJoin (x y : P.Vox j s): P.Vox j s:= ⟨x.val*y.val,Subalgebra.mul_mem (purpose W (meshface (Λ:=P.par) 0 s) j false) x.property y.property⟩
lemma halfV_mul (t n : ℕ) (x y:P.Vox j t) : ((χ t) n (P.voxJoin j t x y)).val = ((χ t) n x).val*((χ t) n y).val := chime_product ..
lemma slab_view (n t : ℕ) (f:P.Card j t n)(x:P.Vox j t): slabT Y H t j false n f x=P.voxJoin j t f.val ((χ t) (2*n) x):= rfl
set_option maxHeartbeats 150000 in
lemma halfWalk (w n t:ℕ)(h:s≤t) (f:P.Card j s w) (x:P.Vox j t):
    slabT Y H t j false (amount P.par s t (w+n)) (G t h (P.halfCard j s n w f)) x= (χ t) (amount P.par s t n) (slabT Y H t j false (amount P.par s t w) (G t h f) ((χ t) (amount P.par s t n) x)) := by
  rw [P.slab_view j,P.slab_view j]
  apply Subtype.ext; rw [P.halfV_mul j]
  change (G t h (P.halfCard j s n w f)).val.val*((χ t) (2*amount P.par s t (w+n)) x).val = _*_
  let d:=amount P.par s t n; let r:=amount P.par s t w
  refine congrArg₂ (fun (x y:Family W)=> x*y) (congrArg Subtype.val (P.cardWalk j s n t w h f)) (congrArg Subtype.val ?_)
  change (χ t) (2*(amount P.par s t (w+n))) x = (χ t) d ((χ t) (2*r) ((χ t) d x))
  rw [tick_tock Y H t j 0 false d (2*r),tick_tock]; exact congrArg (fun n=> (χ t) n x) (by rw [amount_add]; unfold d r; omega)
set_option maxHeartbeats 150000 in
lemma halfCard_pads (w n : ℕ)(p:0<w)(f:P.Card j s w) : P.Box j s (w+n) (by omega) (P.halfCard j s n w f)= P.Keeling j s n * P.Box j s w p f * P.Keeling j s n:=by
  apply test_high Y H V s π j false C₀
  intro t h x
  let r:=amount P.par s t w; let d:=amount P.par s t n; let g:=P.halfCard j s n w f
  change boxOp Y H V s π Qt j false C₀ _ g _ ((κ t) x)= (P.Keeling j s n) (boxOp Y H V s π Qt j false C₀ _ f _ (P.Keeling j s n ((κ t) x)))
  unfold piece; rw [snatch Y H V s π Qt j false C₀ _ g (by omega) h,Keeling,limited_time Y H V s (π).circuit j 0 false C₀ n h,snatch Y H V s π Qt j false C₀ _ f p h,limited_time Y H V s (π).circuit j 0 false C₀ n h]
  exact congrArg (κ t) (P.halfWalk j s w n t h f x)
variable (x : P.Spectrum0 j)
lemma every_tick (n:ℕ)(v : P.Vox j s) : P.stateVox j x s ((χ s) n v) = P.innerEucl j x (W₀ n) (P.stateVox j x s v):=by
  obtain ⟨w,p,b,rfl⟩:=P.fits j s v; let g:= P.halfCard j s n w b
  let f:=(P.portion j x).gnsStarAlgHom; let t:= W₀ n
  change P.stateVox j x s g.val=_; rw [P.from_entry j x s (w+n) (by omega),P.from_entry j x s w p]
  let a:=P.atSide j s w p b; let u:=P.Eucl j t
  have he:P.atSide j s (w+n) (by omega) g=u*a*u:=Subtype.ext (by simp_rw [P.coe_prod0]; have hl:=P.halfCard_pads j s w n p b; rw [P.keel_along] at hl; exact hl)
  rw [fromPlane,he,map_mul,map_mul];
  change f u (f a (f u (P.emptyV j x)))=_; rw [show f u (P.emptyV j x)=P.emptyV j x from P.at_full j x t]
-- even in other axes; scales & spatial monotone extension later
lemma half_coin (Qq: P.Register) (x:ℤ) (f:P.Test):
    P.promote s Qq (P.halfShift j x f)=P.halfShift j ((P.par.R.L.val:ℤ)*x) (P.promote s Qq f):=by
  apply Subtype.ext; rw [P.promotes_to,P.halfShift_val,P.halfShift_val,P.promotes_to]; exact home_motion Y H V s j _ (π).circuit f.property
section glass
local notation "δ"=> P.par
local notation "P₀" t:max=>P.vacuum t
local notation "L"=>P.par.R.L.val
local notation "l"=>P.calibration.ℓ
local notation "℘" n:max=> P.singleState j n x
-- choose representation-neutral margin increment as in Flood
lemma halo_grow {S:Finset Cover} {z:ℤ} (h: Tower.region j z l S) (n:ℕ): Tower.region j ((L:ℤ)^n*z) (l+n) (volumeAround P.par P.width n S):=by
 induction n with
 | zero=>simpa [volumeAround] using h
 | succ n ih=> rw [volumeAround,pow_succ',mul_assoc,← Nat.add_assoc]; exact Tower.strict_one Y H j ih
lemma clearance (n:ℕ) (S:Finset Cover) (c:ℤ) (h: Tower.region j (R c) l S) : Tower.region j (R ((L:ℤ)^n*c)) (l+n) (volumeAround P.par P.width n S):=by
 rw [show R ((L:ℤ)^n*c)=(L:ℤ)^n * (R c) from by unfold gaugeShift; ring]; exact P.halo_grow j h n
abbrev conveying (n:ℕ) (f:P.Test): P.Test:= ⟨stream Y H P.projection.refine s n f.val, streams_test Y H (π).circuit s n f.property⟩
lemma carryReads(n:ℕ)(f:P.Test): P.reading j (s+n) (P.conveying s n f)= P.reading j s f:=by
  apply Subtype.ext; rw [at_label,at_label]; have ht:= Vacancy.cap_level Y H V s π Qt j false C₀ (F:=P.obs f) (s+n) (by omega); rw [Nat.add_sub_cancel_left] at ht; exact ht
local notation "K₀" n:max => P.conveying s n
lemma conveys_form (n:ℕ){c:ℤ} {S T:Finset Cover}{x y:P.Test} (p:x∈ bay W S true)(q:y∈ bay W T true)
    (t: Tower.region j c l S) (u: Tower.region j c l T) : P.conveying s n (aureole W j c x*y) = aureole W j ((L:ℤ)^n*c) ((K₀ n) x) * (K₀ n) y:=by
  apply Subtype.ext; change stream Y H P.projection.refine s n (mirror W j c x.val*y.val)= mirror W j _ (stream Y H P.projection.refine s n x.val)*_
  rw [woven_product Y H (π).circuit s n (axial W j c ((Tapestry.locates ..).1 p)) ((Tapestry.locates ..).1 q) (mirror_detached δ P.width t u),stream_flipped Y H (π).circuit s n j c ((marque ..).1 x.property)]
lemma halfConj (a : ℤ)(x : P.Test): P.reflectTest j ((Σh a) x)= (Σh (-a)) (P.reflectTest j x) := by
  apply Subtype.ext
  change mirror W j 0 (chime W j (R a) x.val)=chime W j (R (-a)) (mirror W j 0 x.val)
  rw [chime_diag W j (R (-a)) 0 ((marque ..).1 x.property).paid.choose_spec,show -(R (-a))=R a from by unfold gaugeShift; ring]
lemma frame_pair (z q : ℤ) (g:P.Test) :
    P.reading j s (aureole W j (R z) ((Σh q) g)*(Σh q) g)=
      P.reading j s (P.reflectTest j g * (Σh (q+q-z)) g):=by
  rw [P.halfReflect,P.halfConj,P.halfSame]
  rw [← P.halfReads j s (q-z) ((Σh (z+ -q)) (P.reflectTest j g) * (Σh q) g), map_mul,P.halfSame,P.halfSame];
  rw [show q-z+(z + -q)= 0 by abel, P.halfZero, show q-z+q=q+q-z by abel]
private def tollLight := 4*P.par.block.val
lemma mapped_above {S:Finset Cover} {z:ℤ}(p: Tower.region j (R z) ((W).ℓ+tollLight P) S) {w:ℤ}(hw:w+w≤z+1):
    Tower.region j 0 (W).ℓ (address j (R (-w)) S):=by
  intro y h; obtain ⟨y,e,rfl⟩:= Finset.mem_image.mp h
  rw [moves j j,if_pos rfl]; specialize p y e
  unfold gaugeShift tollLight at *; push_cast at *; have hu:0 ≤ (P.par.block.val:ℤ):=by positivity
  push_cast [Preparation.block] at hu
  nlinarith only [mul_le_mul_of_nonneg_left hw hu,p]
lemma elevated {S:Finset Cover} (f:P.Test) (c:ℤ) (p:f∈ bay W S true) (h: Tower.region j (R c) (W).ℓ S) :
    0 ≤ P.singleState j s x (aureole W j (R c) f*f) := by
  let n:= P.tollLight; let v:=(L:ℤ)^n*c; let S':= volumeAround P.par P.width n S; let g:= (K₀ n) f
  -- translate -w, where w is the NEXT point of the 8B grid. Might be beyond the support margin from the old level if pinned right at the glass; use lift clearance.
  let w:= (v+1)/2; have hw:v≤ w+w:=by unfold w; omega
  have hx : w+w ≤ v+1:=by unfold w; omega
  let y:= (Σh (-w)) g
  let U:=address j (R (-w)) S'
  have hp:y∈ bay W U true:=flow_port W j (R (-w)) (proceeds Y H (π).circuit s n ((Tapestry.locates ..).1 p)).1
  let t':= P.positiveVox j (s+n) U y hp (P.mapped_above j (P.clearance j n S c h) hx)
  have hy:g=(Σh w) y:=by unfold y; rw [P.halfSame,add_neg_cancel,P.halfZero]
  rw [P.single_state,←P.carryReads j s n,P.conveys_form j s n p p h h]; change 0≤ P.chi j x (P.reading j (s+n) (aureole W j _ g*g))
  have hm : (L:ℤ)^n*(R c) = R v:=by unfold gaugeShift v; ring
  rw [hm,hy,P.frame_pair,← P.single_state]
  let k:=(w+w-v).toNat
  rw [show w+w-v=(k:ℤ) from by unfold k; omega]; change 0≤ (℘ (s+n)) ((Θ) (Δ (s+n) t')*(Σh ↑k) (Δ (s+n) t'))
  rw [← P.halfMovesOf,← P.gram_at,P.every_tick]
  let T₀:=P.halfTime (s+n) k; let a:=(P.portion j x).gnsStarAlgHom
  have he : ContinuousLinearMap.IsPositive (a (P.Eucl j T₀)):= (ContinuousLinearMap.nonneg_iff_isPositive _).1 (map_nonneg a (P.eucl_pos j T₀))
  exact he.inner_nonneg_right _
end glass
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.keel_at
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.keel_along
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.every_tick
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.lightStar
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.elevated
