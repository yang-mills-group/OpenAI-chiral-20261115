/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Elected
/-!
# Selected portions read the actual multi-height tower. Dynamics: positive energy

Use `origin` for the GNS vacuum. `φ` on *crossed* Slabs with J=1 reads exactly
like cap conditioning on any single, but also at the separated concatenation of
all its slabs exactly like the selected Euclidean hierarchy (using its E' functional,
not equal to the original E). No assumption that products are separated without
qualification of the tower widths. Account also for time-continuity; the density of
some labels near the root of each `X` suffices because each is strictly advanced
by refinement **in the given representation** too.
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
namespace Spine
variable (P : Spine)(j : Axis)
local notation "K"=> P.calibration
local notation "π"=> P.history
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "V"=> P.law
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "M"=> timeMesh P.par
local notation "ℍ"=> P.Hil j
local notation "X"=> P.Spectrum0 j
local notation "A"=> P.Slabs j
local notation "φ" x:max=> P.portion j x
local notation "Φ" x:max=> (P.portion j x).gnsStarAlgHom
local notation "Γ" x:max=> origin (P.portion j x)
local notation "δ" f:max => P.voxTest j _ f
local notation "Θ"=> P.reflectTest j
local notation "σ" n:max => P.shifts j n
local notation "µ" n:max x:max=> P.singleState j n x
variable (x : P.Spectrum0 j)
abbrev PortionHil : Hilbert := { space:= (P.portion j x).GNS }
abbrev stateSpace := (P.portion j x).gnsStarAlgHom -- actually rep
abbrev emptyV := origin (P.portion j x)
abbrev fromPlane {s w:ℕ} (p:0<w)(f : P.Card j s w) := (Φ x) (P.atSide j s w p f) (Γ x)
lemma slide_single (s:ℕ)(n:ℤ)(b:P.Test) : P.singleState j s x (P.shifts j n b)= P.singleState j s x b:=congrArg (P.chi j x) (P.shifted_read j s n b)
lemma room_single (s w : ℕ)(p:0<w)(f : P.Card j s w) : (P.portion j x) (P.atSide j s w p f)=(µ s x) (δ f.val):=by rw [P.portion_val,P.boxes_here]; rfl
lemma concat (s w v : ℕ) (pw : 0 < w) (pv : 0 < v) (f : P.Card j s w)(g : P.Card j s v): P.atSide j s w pw f*P.atSide j s v pv g=P.atSide j s _ (add_pos pw pv) (edit Y H s j false w v f g):=Subtype.ext (edit_comp Y H V s π Qt j false C₀ w v f g pw pv)
lemma grainStar (s w : ℕ)(p:0<w)(f:P.Card j s w) : star (P.atSide j s w p f)=P.atSide j s w p (inverse Y H s j false w f):=Subtype.ext (respects Y H V s π Qt j false C₀ w f p)
lemma gram_word {s w v : ℕ}(p:0<w)(f:P.Card j s w)(q:0<v)(g:P.Card j s v) : inner ℂ (P.fromPlane j x p f) (P.fromPlane j x q g) = P.singleState j s x ((Θ) (δ f.val) * δ g.val) :=by
  let f₀:=P.atSide j s w p f; let g₀:=P.atSide j s v q g
  have he : inner ℂ (P.fromPlane j x p f) (P.fromPlane j x q g) = (φ x) (star f₀*g₀):=by
    rw [← gns_state (P.portion j x),map_mul (Φ x),map_star (Φ x) f₀]
    exact (ContinuousLinearMap.adjoint_inner_right ((Φ x) f₀) (Γ x) ((Φ x) g₀ (Γ x))).symm
  rw [he]; unfold f₀ g₀; rw [P.grainStar,P.concat,P.room_single]
  let i:= inverse Y H s j false w f; let F:= edit Y H s j false w v i g
  have ht : δ F.val= (σ (w:ℤ)) (Θ (δ f.val) * δ g.val):=by
    rw [map_mul]; apply Subtype.ext
    change (edit _ _ _ _ _ _ _ _ _).val.val=_*_
    rw [editor]; apply congrArg₂ (·*·) _ rfl
    change mirror K j (gaugeT K w) f.val.val = _
    have hz := mirror_cancel K j (w:ℤ) 0 (test_entry Y H s j false f); rw [gaugeT_zero,sub_zero] at hz; exact hz
  rw [show δ (edit Y H s j false w v (inverse Y H s j false w f) g).val=_ from ht, P.slide_single]
-- width-independence even in component
lemma same_width {s w v:ℕ}{p:0<w}{q:0<v}{f:P.Card j s w}{g:P.Card j s v}(e : f.val=g.val) : P.fromPlane j x p f=P.fromPlane j x q g :=by
  let a:=P.fromPlane j x p f; let b:= P.fromPlane j x q g
  apply sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ) ..).mp ?_); rw [inner_sub_right,inner_sub_left,inner_sub_left,P.gram_word,P.gram_word,P.gram_word,P.gram_word,e,sub_self]

noncomputable def stateVox (s : ℕ)(f : P.Vox j s) : P.PortionHil j x := P.fromPlane j x (P.fits j s f).choose_spec.1 (P.fits j s f).choose_spec.2.choose
lemma from_entry (s w : ℕ)(p : 0<w)(f : P.Card j s w): P.stateVox j x s f.val= P.fromPlane j x p f := P.same_width j x (P.fits j s f.val).choose_spec.2.choose_spec
lemma gram_at (s : ℕ)(f g : P.Vox j s) : inner ℂ (P.stateVox j x s f) (P.stateVox j x s g)=P.singleState j s x (P.reflectTest j (P.voxTest j s f) * P.voxTest j s g):=by
 obtain ⟨w,p,f,rfl⟩:=P.fits j s f; obtain ⟨v,q,g,rfl⟩:=P.fits j s g; rw [P.from_entry j x s w p f,P.from_entry j x s v q g]; exact P.gram_word j x p f q g
lemma refine_vox (s t : ℕ) (e:s≤t) (f : P.Vox j s) : P.stateVox j x t (Raise Y H (π).circuit j 0 false s t e f) = P.stateVox j x s f:=by
  obtain ⟨w,p,f,rfl⟩:=P.fits j s f
  let g:= furnished Y H s π j false w f t e
  let v:=P.par.R.L.val^(t-s)*w; have q:0<v:=by exact mul_pos (pow_pos P.par.R.L.property _) p
  change P.stateVox j x t g.val=P.stateVox j x s f.val
  rw [P.from_entry j x s w p f,P.from_entry j x t v q g]
  have hx: P.atSide j s w p f=P.atSide j t v q g:=Subtype.ext (refined_box Y H V s π Qt j false C₀ w f p t e)
  unfold fromPlane; rw [hx]
-- semigroup in GNS
abbrev innerEucl (t : ℝ≥0) : (P.PortionHil j x).Op := (Φ x) (P.Eucl j t)
local notation "κ" t:max=> P.innerEucl j x t
lemma eucl_star (t:ℝ≥0) : star (P.Eucl j t)=P.Eucl j t:=Subtype.ext (advance_adjoint ..)
lemma eucl_zero : P.Eucl j 0=1:=Subtype.ext (advance_source ..)
lemma eucl_along (t v : ℝ≥0): P.Eucl j (t+v)=P.Eucl j t * P.Eucl j v :=Subtype.ext (advance_smag ..)
lemma eucl_cont (t : ℝ≥0) (h : 0<t): ContinuousAt (P.Eucl j) t := by
  rw [Topology.IsInducing.continuousAt_iff (Topology.IsEmbedding.subtypeVal.isInducing)]
  let f (t:ℝ≥0):ℂ:= ((t:ℝ):ℂ)*Complex.I
  have p : f t∈ {x:ℂ|0<x.im}:=by change 0 < (f t).im; simpa [f] using (show (0:ℝ)<(t:ℝ) from h)
  refine (((holo Y H V (π).circuit j 0 false C₀ _ p).continuousAt).comp (by unfold f; fun_prop : Continuous f).continuousAt).congr ?_
  filter_upwards [lt_mem_nhds h] with i h
  exact agrees_euclid Y H V (π).circuit j 0 false C₀ h
lemma eucl_pos (t:ℝ≥0): 0 ≤ P.Eucl j t:=by
  let u:=t/2; rw [show t=u+u from (add_halves ..).symm,P.eucl_along]
  exact IsSelfAdjoint.mul_self_nonneg (P.eucl_star j u)
lemma all_vacuum (t:ℝ≥0): P.shadow j (P.Eucl j t)=1:= by
  apply Subtype.ext; ext1 u; change P.piZero j (advance Y H V (π).circuit j 0 false C₀ _ u.val)=u
  rw [floor_rise]; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
lemma at_small (t:ℝ≥0):‖P.innerEucl j x t‖≤1:=(NonUnitalStarAlgHom.norm_apply_le (Φ x) _).trans (P.heat_norm j t)
lemma at_star(t:ℝ≥0):(P.innerEucl j x t).adjoint=P.innerEucl j x t:= by
  change star ((Φ x) _)= _; rw [←map_star,P.eucl_star]
lemma at_zero : P.innerEucl j x 0=1:=by unfold innerEucl; rw [eucl_zero,map_one]
lemma at_full (t:ℝ≥0): P.innerEucl j x t (P.emptyV j x)=P.emptyV j x:=(gns_full _ (P.portion_unit j x) (P.Eucl j t) (P.heat_norm j t)).mpr (by rw [P.portion_val,P.all_vacuum,map_one]; rfl)
lemma at_plus (t v:ℝ≥0):κ (t+v)= (κ t).comp (κ v) :=by unfold innerEucl; rw [P.eucl_along,map_mul]; rfl
lemma moves_p (s n : ℕ)(f : P.Vox j s) : P.stateVox j x s (tick Y H s j 0 false (2*n) f)=(κ (whenly M s n)) (P.stateVox j x s f):=by
  obtain ⟨w,p,f,rfl⟩:= P.fits j s f
  rw [P.from_entry j x s w p f]; rcases Nat.eq_zero_or_pos n with rfl|h
  · rw [when_zero,P.at_zero]
    have hv : tick Y H s j 0 false (2*0) f.val=f.val:=by apply Subtype.ext; rw [timed_apply]; exact relocate_zero K j (test_entry ..)
    rw [hv,P.from_entry j x s w p f]; rfl
  let i:=SlabMark.identity Y H s j false n; let k:=edit Y H s j false n w i f
  have hi:k.val=tick Y H s j 0 false (2*n) f.val:=by apply Subtype.ext; rw [timed_apply]; unfold k; rw [editor]; exact one_mul _
  rw [←hi,P.from_entry j x s (n+w) (add_pos h p) k,fromPlane]
  have ht:P.atSide j s n h i= P.Eucl j (whenly M s n):=Subtype.ext (SlabMark.ticket_birth Y H V s π Qt j false C₀ n h)
  unfold k; rw [←P.concat j s n w h p, map_mul (Φ x),ht]; rfl
lemma voxel_stays : P.stateVox j x 0 (unity Y H j 0 false 0)= P.emptyV j x:=by
  let i:= SlabMark.identity Y H 0 j false 1; let t:= whenly M 0 1
  have ht:P.atSide j 0 1 zero_lt_one i=P.Eucl j t:=Subtype.ext (SlabMark.ticket_birth Y H V 0 π Qt j false C₀ 1 zero_lt_one)
  change P.stateVox j x 0 i.val= _; rw [P.from_entry j x 0 1 zero_lt_one,fromPlane,ht]; exact P.at_full j x t
lemma move_vac (g : Grid j) : (Φ x) (P.movesOf j g) (Γ x)= Γ x :=
  ((P.joint_ext j (P.PortionHil j x) (Φ x) _).mp (P.portion_root j x)).2 g
lemma move_use (s : ℕ)(d : Trans j)(v : ℤ) (f : P.Vox j s) : (Φ x) (P.movesOf j (s,v,d)) (P.stateVox j x s f)= P.stateVox j x s (sail Y H s j 0 false d.val d.property (2*v) f) := by
  obtain ⟨w,p,f,rfl⟩:=P.fits j s f; let g:= alongS Y H s j false w f d v
  change _=P.stateVox j x s g.val; rw [P.from_entry j x s w p f,P.from_entry j x s w p g]
  let a:=P.movesOf j (s,v,d); let b:=P.atSide j s w p f; let c:= P.atSide j s w p g
  have ht:a*b=c*a:=Subtype.ext (shape_across Y H V s π Qt j false C₀ w f p d v)
  change ((Φ x) a) (((Φ x) b) (Γ x))=((Φ x) c) (Γ x)
  rw [←ContinuousLinearMap.comp_apply]
  suffices T: (Φ x) (a*b) (Γ x)= (Φ x) c (Γ x) by
    rw [map_mul (Φ x) a b] at T; exact T
  rw [ht,map_mul (Φ x)]; exact congrArg _ (P.move_vac j x _)
local notation "E₀"=> P.stateVox j x
-- same seed Hilbert full! cyclic labels before projection onto any spatial-continuous part.
noncomputable def stateVoxLinear (s : ℕ): P.Vox j s →ₗ[ℂ] (P.PortionHil j x) :=by
  have he (f g h : P.Vox j s) : inner ℂ (E₀ s h) (E₀ s (f+g))=inner ℂ (E₀ s h) (E₀ s f) + inner ℂ (E₀ s h) (E₀ s g):=by
    rw [P.gram_at,P.gram_at,P.gram_at,show (δ (f+g))= δ f+ δ g from rfl,mul_add,map_add]
  have ht (f g : P.Vox j s) (k : ℂ) : inner ℂ (E₀ s g) (E₀ s (k • f))= k * inner ℂ (E₀ s g) (E₀ s f) :=by
    rw [P.gram_at,P.gram_at,show (δ (k • f))= k • δ f from rfl,Algebra.mul_smul_comm,map_smul,smul_eq_mul]
  refine ⟨⟨E₀ s,fun i j'=>?_⟩, fun k f=>?_⟩
  · apply sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ) ..).mp ?_); simp only
    have h (x' : P.Vox j s) : inner ℂ (E₀ s x') (E₀ s (i+j') - ((E₀ s i)+(E₀ s j')))=0:=by rw [inner_sub_right,inner_add_right,he,sub_self]
    simp only [inner_sub_left,inner_add_left,h]; ring
  simp only; rw [RingHom.id_apply]
  apply sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ) ..).mp ?_)
  have h (x' : P.Vox j s) : inner ℂ (E₀ s x') (E₀ s (k• f) - k• (E₀ s f))=0:=by rw [inner_sub_right, inner_smul_right,ht,sub_self]
  rw [inner_sub_left,inner_smul_left,h,h,mul_zero,sub_self]

open Set ContinuousLinearMap
open scoped Pointwise
lemma prepared0 (f : (ℍ).Op) (e : f∈ P.insertions j) : f∈ P.slabAlgebra j:= StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ (P.insertions j) e)
lemma in_raw {x':(ℍ).Op}(e : x'∈P.idleOr j): x'∈P.slabAlgebra j:= P.prepared0 j _ (Or.inl e)
lemma coe_prod0 (x y : P.Slabs j) : (x*y).val=x.val*y.val:=rfl
lemma shift_flight (l : List (Grid j)) : ((l.map (P.movesOf j)).prod).val=(l.map (P.shiftOp j)).prod := by
  induction l with|nil=>rfl|cons i l h=> simp only [List.map_cons,List.prod_cons,P.coe_prod0 j]; rw [h]
lemma settles (l : List (Grid j)) : (Φ x) (l.map (P.movesOf j)).prod (Γ x)= Γ x:=by
  induction l with|nil=> simp|cons i l h=> rw [List.map_cons,List.prod_cons,map_mul]; change (Φ x) _ ((Φ x) (l.map _).prod (Γ x))=_; rw [h,P.move_vac]

def principalSpan : Submodule ℂ (P.PortionHil j x):= Submodule.span ℂ (⋃ (s:ℕ), Set.range (P.stateVox j x s))
local notation "S₀"=> P.principalSpan j x
lemma span_mem (s:ℕ) (f:P.Vox j s): P.stateVox j x s f∈ P.principalSpan j x := Submodule.subset_span (mem_iUnion.mpr ⟨s,mem_range_self _⟩)
lemma span_one : P.emptyV j x∈ P.principalSpan j x := (P.voxel_stays j x) ▸ P.span_mem j x _ _
lemma boarding (f : P.Slabs j)(p : f.val∈P.normalForm j) : (Φ x) f (Γ x)∈ P.principalSpan j x:=by
  obtain ⟨t,p,l,h⟩:=p; let u:A:= ⟨t,P.in_raw j p⟩; have he:f = u*(l.map (P.movesOf j)).prod:= Subtype.ext (by rw [P.coe_prod0 j,P.shift_flight]; exact h)
  rw [he,map_mul]; change (Φ x) u ((Φ x) (l.map _).prod (Γ x))∈ S₀; rw [P.settles]
  have hx(t : P.Slabs j)(p:t.val∈ P.tiles j): (Φ x) t (Γ x)∈ S₀:=by
    obtain ⟨s,w,k,f,h⟩:=p; rw [show t=P.atSide j s w k f from Subtype.ext h.symm]; change P.fromPlane j x k f∈ _; rw [← P.from_entry]; exact P.span_mem j x s f.val
  rcases mem_insert_iff.mp (show u.val∈P.idleOr j from p) with t|t; · rw [show u=1 from Subtype.ext t,map_one]; exact P.span_one j x
  exact hx u t

lemma all_work (y : P.Slabs j) (p: y.val∈ StarAlgebra.adjoin ℂ (P.insertions j)) : (Φ x) y (Γ x)∈ P.principalSpan j x:=by
  let T:= P.slabAlgebra j
  let U: Submodule ℂ T:= (S₀).comap ((ContinuousLinearMap.apply ℂ (P.PortionHil j x) (Γ x)).toLinearMap.comp (Φ x).toLinearMap)
  let D: Submodule ℂ (ℍ).Op:= U.map T.subtype.toLinearMap
  change y.val ∈ (StarAlgebra.adjoin ℂ (P.insertions j)).toSubalgebra.toSubmodule at p; rw [StarAlgebra.adjoin_eq_span] at p
  let L:= P.insertions j ∪ star (P.insertions j)
  have hr: Submodule.span ℂ (Submonoid.closure L : Set (ℍ).Op)≤ D:=by
    rw [Submodule.span_le]; rintro a p
    have hp:= P.inMonoid j p; obtain ⟨t,r,l,h⟩:=hp
    let v:= (show T from ⟨t,P.in_raw j r⟩)*(l.map (P.movesOf j)).prod
    have he: v.val=a:=by unfold v; rw [P.coe_prod0 j,P.shift_flight,h]
    exact ⟨v,P.boarding j x v (show _ from ⟨t,r,l,he.trans h⟩),he⟩
  obtain ⟨b,h,t⟩:=hr p; exact Subtype.ext t ▸ (show (Φ x) b (Γ x)∈ _ from h)
lemma all_cyclic : Dense ((P.principalSpan j x) : Set (P.PortionHil j x)):=by
  let T:= StarAlgebra.adjoin ℂ (P.insertions j); let f : T → P.Slabs j:= StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure T)
  have hg:DenseRange f:= denseRange_inclusion_iff (StarSubalgebra.le_topologicalClosure T)|>.2 Subset.rfl
  have h: DenseRange (fun t=> (Φ x) t (Γ x)):= gns_dense _
  apply (h.comp hg (gns_operator_cont _)).mono; rintro _ ⟨i,rfl⟩; exact P.all_work j x _ (show _ from i.property)
-- time dynamics from actually dense range of strictly positive-time action on GNS labels
lemma advanced (s : ℕ)(f:P.Vox j s):∃ t:ℝ≥0,0<t∧∃ u:(P.PortionHil j x), P.stateVox j x s f= (κ t) u:= by
  obtain ⟨q,y,h⟩:= predecessor Y H s (π).circuit j 0 false f; let Qw:= P.stateVox j x (s+q) y
  refine ⟨whenly M (s+q) 1,when_pos M (s+q) 1 zero_lt_one,Qw,?_⟩
  unfold Qw; rw [←P.moves_p j x (s+q) 1,mul_one,h,P.refine_vox]
noncomputable def connected0 : P.Slabs j→L[ℂ](P.PortionHil j x).Op:= (Φ x).toLinearMap.mkContinuous 1 fun y=>by rw [one_mul]; exact NonUnitalStarAlgHom.norm_apply_le (Φ x) y
lemma portion_cont_at_zero (s : ℕ)(f:P.Vox j s) : Continuous (fun t=> (P.innerEucl j x t) (P.stateVox j x s f)):=by
  obtain ⟨t,p,f',h⟩:=P.advanced j x s f
  simp_rw [h,← ContinuousLinearMap.comp_apply,← P.at_plus]
  have hc: Continuous (Φ x):= (P.connected0 j x).continuous
  refine (ContinuousLinearMap.apply ℂ (P.PortionHil j x) f').continuous.comp (hc.comp ?_)
  apply continuous_iff_continuousAt.mpr; intro v
  exact (((P.eucl_cont j (v+t) (by positivity)).comp (f:=fun v:ℝ≥0=> v+t) (show ContinuousAt _ v from continuousAt_id.add_const t)))
lemma journey_cont (v:P.PortionHil j x) : Continuous (fun t=> (P.innerEucl j x t) v) := by
  have ht {w:P.PortionHil j x} (e:w ∈ S₀): Continuous (fun t=> (κ t) w):=by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ e
    · rintro w p; obtain ⟨s,p⟩:=Set.mem_iUnion.mp p; obtain ⟨f,rfl⟩:=p; exact P.portion_cont_at_zero j x s f
    · simp_rw [map_zero]; exact continuous_const
    · intro x y _ _; simp_rw [map_add]; exact Continuous.add
    intro k a _ h; simp_rw [map_smul]; exact (continuous_const (y:=k)).smul h
  apply continuous_iff_continuousAt.mpr; intro z; apply Metric.tendsto_nhds.mpr; intro ε p
  obtain ⟨w,h,e⟩:= Metric.mem_closure_iff.mp (P.all_cyclic j x v) (ε/3) (by positivity)
  have hx(a): dist ((κ a) v) ((κ a) w) < ε/3:=by rw [dist_eq_norm, ← map_sub]; exact lt_of_le_of_lt ((le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) (P.at_small j x a))) (by rwa [←dist_eq_norm])
  filter_upwards [Metric.tendsto_nhds.mp ((ht h).tendsto z) (ε/3) (by positivity)] with i hi
  have hG:=hx z; rw [dist_comm] at hG; have t:=dist_triangle ((κ i) v) ((κ i) w) ((κ z) w); have g:= dist_triangle ((κ i) v) ((κ z) w) ((κ z) v); change dist _ _ < ε/3 at hi; change dist _ _<ε; linarith [hx i]
noncomputable def dynamics0 : OS.Semigroup (P.PortionHil j x) j where
  E t:= P.innerEucl j x t
  U _:= ContinuousLinearMap.id ℂ _ -- spectator, not spacetime assertion!
  eZero:=P.at_zero j x
  time:= P.at_plus j x
  shrinks:=P.at_small j x
  sym:=P.at_star j x
  space _ _:=rfl
  uZero:=rfl
  unitary _ _:=rfl
  independent _ _:= by simp
  continuousE:=P.journey_cont j x
  continuousU _:=continuous_const

-- unicity tool, will also let us compare on portions & physical representation subspaces
section
open OS.Semigroup
lemma opaque_compare {G K':Hilbert}{j i:Axis}(S : OS.Semigroup G j)(T : OS.Semigroup K' i)(L:G→L[ℂ]K')
    (h : ∀ t, L.comp (S.E t)=(T.E t).comp L) : EqOn (fun z=> L.comp (S.F z)) (fun z=> (T.F z).comp L) inside := by
  let F (z:ℂ):G→L[ℂ]K':= L.comp (S.F z)-(T.F z).comp L
  have hp : AnalyticOnNhd ℂ F inside:= fun z hz=> (((ContinuousLinearMap.compL ℂ G G K' L).analyticAt _).comp (S.localHeat z hz)).sub ( ((ContinuousLinearMap.compL ℂ G K' K').flip L).analyticAt _ |>.comp (T.localHeat z hz))
  let t:ℝ≥0:=1
  have hu : EqOn F 0 inside := by
    apply hp.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (dur.mpr (by norm_num : 0<(1:ℝ≥0)))
    intro hn
    have hy : Tendsto duration (𝓝[>] t) (𝓝[≠] (duration t)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      have hI := mem_Ioi.mp hi
      change ¬duration i=duration t; exact fun he => hI.ne' (Subtype.ext (Complex.ofReal_injective he))
    obtain ⟨i,hi,hq⟩ := ((hy.eventually hn).and self_mem_nhdsWithin).exists
    have he:0< i:= (zero_lt_one (α:=ℝ≥0)).trans (mem_Ioi.mp hq)
    exact hi (show F (duration i)=0 by unfold F; rw [S.roots_heat he,T.roots_heat he,h,sub_self])
  intro v x; exact sub_eq_zero.mp (hu x)
lemma within_energy {G K':Hilbert}{j i:Axis}(S : OS.Semigroup G j)(T : OS.Semigroup K' i)(L:G→L[ℂ]K')
    (h : ∀ t, L.comp (S.E t)=(T.E t).comp L) (t : ℝ) : L.comp (S.edge t)=(T.edge t).comp L := by
  apply DFunLike.coe_injective; apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _); funext i
  change L (S.edge t (S.E 1 i))= T.edge t (L (S.E 1 i)); rw [S.high, ← ContinuousLinearMap.comp_apply L (S.E 1),h,ContinuousLinearMap.comp_apply,T.high]
  exact DFunLike.congr_fun (opaque_compare S T L h (show duration 1+sideways t∈ inside from OS.Semigroup.length.mpr (by norm_num))) i
-- ALSO equivalence of invariants real time and eucl time. analyticity for heat equates horizontal line. reverse from arbitrary real time trivial by analytic invariance.
lemma heat_iff_edge {G:Hilbert}(S : OS.Semigroup G j) (v:G):
    (∀ t, S.E t v=v) ↔ (∀ t, S.edge t v=v):= by
  -- only continuous time. analytic uniqueness.
  let Ω : ℂ→G:= fun z=> S.F z v - S.E 1 v
  have hp:AnalyticOnNhd ℂ Ω inside:= fun z hz=> (((ContinuousLinearMap.apply ℂ G.space v).analyticAt _).comp (S.localHeat z hz)).sub analyticAt_const
  have hne (L : ℂ→G)(p:AnalyticOnNhd ℂ L inside)(e: ∃ᶠ z : ℂ in 𝓝[≠] (duration 1), L z=0) : EqOn L 0 inside := by
    exact p.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (dur.mpr zero_lt_one) e
  constructor
  · intro h t
    have hr: EqOn Ω 0 inside:= hne Ω hp (by
      intro hn
      -- copy punct line sequence
      have hy : Tendsto duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (duration 1)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin] with i hi
        have hI := mem_Ioi.mp hi
        change ¬duration i=duration 1; exact fun he => hI.ne' (Subtype.ext (Complex.ofReal_injective he))
      obtain ⟨i,hi,hq⟩ := ((hy.eventually hn).and self_mem_nhdsWithin).exists
      have he:0< i:= (zero_lt_one (α:=ℝ≥0)).trans (mem_Ioi.mp hq)
      exact hi (by change S.F (duration i) v-S.E 1 v=0; rw [S.roots_heat he,h,h,sub_self]))
    nth_rw 1 [← h 1]; rw [S.high]; exact (sub_eq_zero.mp (hr (show _ from OS.Semigroup.length.mpr (by norm_num : 0<(1:ℝ≥0))) )).trans (h _)
  intro h t
  have hr : EqOn Ω 0 inside:= hne Ω hp (by
    intro hn
    let f (r:ℝ):ℂ:=duration 1+sideways r
    have hu:Tendsto f (𝓝[≠] 0) (𝓝[≠] (duration 1)):= by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · rw [show duration 1=f 0 from by simp [f]]; exact (by unfold f sideways; fun_prop : Continuous f).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      change ¬f i = _; unfold f sideways; simpa using (show i≠0 from hi)
    obtain ⟨i,a⟩:= (hu.eventually hn).exists
    refine a ?_; change Ω (f i)=0
    unfold Ω f; rw [←S.high]; apply sub_eq_zero.mpr; rw [← ContinuousLinearMap.comp_apply, ← S.eitherE,ContinuousLinearMap.comp_apply,h])
  suffices p:S.E 1 (S.E t v-v)=0 from sub_eq_zero.mp (S.heat_faithful 1 _ p)
  have ht:0<1+t:=by positivity
  have he:S.F (duration (1+t)) v = _:= sub_eq_zero.mp (show Ω (duration (1+t))=0 from hr (dur.mpr ht))
  rw [map_sub, ←ContinuousLinearMap.comp_apply, ←S.time,← S.roots_heat ht,he,sub_self]
end

open OS.Semigroup Complex
local notation "T"=> P.PortionHil j x
local notation "D"=> P.dynamics0 j x
local notation "Z" a:max=> (D).F (-Complex.I*a)
local notation "U" a:max=> (D).edge a
lemma heat_at  : AnalyticOnNhd ℂ (fun z=> Z z) {p:ℂ|0<p.im} := by
  intro v h
  have he: -(Complex.I:ℂ)*v∈ OS.Semigroup.inside:=by change 0< (-Complex.I*v).re; simpa using (show 0<v.im from h)
  exact ((D).localHeat _ he).comp (analyticAt_const.mul analyticAt_id)
-- use `P0.energy` & same **measure** for time heat kernel, GNS. No spectrum forward assertion about p ≠ energy projection.
open Spectral Boundary Probe
noncomputable def energyE (v:P.PortionHil j x): Measure ℝ:= ((P.dynamics0 j x).ℚmeasure.diagonal v).map (fun y:E4=> y j)
instance (v:P.PortionHil j x) : IsFiniteMeasure (P.energyE j x v):=by unfold energyE; infer_instance
lemma energy_pa (v:T) : ∀ᵐ t ∂ (P.energyE j x v), 0 ≤ t := by
  have h:Measurable (fun i:E4=>i j):=by fun_prop
  exact (ae_map_iff h.aemeasurable (measurableSet_le measurable_const measurable_id)).2 ((D).bright v)
lemma energy_char (t:ℝ) (v:T) : inner ℂ v ((P.dynamics0 j x).edge t v) = ∫ r:ℝ, Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I) ∂ (P.energyE j x v):=by
  let m:=(D).ℚmeasure.diagonal v; let e(x:E4):ℝ:=x j
  have he:Measurable e:= by unfold e; fun_prop
  rw [energyE,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I))).aestronglyMeasurable)]
  have ht:=(D).assigned v t 0
  change (D).J 0 v v (t:ℂ)=_ at ht
  -- names conflict linter
  simpa [OS.Semigroup.J,OS.Semigroup.ray,(D).eZero,(D).unit.origin,Probe.plane,e] using ht
lemma paid_edge {a:ℝ≥0} (p:0<a) (t:ℝ) : (P.dynamics0 j x).F (-Complex.I* (((t:ℂ))+((a:ℝ):ℂ)*Complex.I))=(U t).comp (κ a):= by
  have hi: -(Complex.I:ℂ) * ((t:ℂ)+((a:ℝ):ℂ)*Complex.I) = duration a + sideways t := by apply Complex.ext <;> simp [duration,sideways]
  rw [hi,←OS.Semigroup.along (D) (OS.Semigroup.dur.mpr p) t]; rw [OS.Semigroup.roots_heat (D) p]; rfl
lemma energy_read (t:ℂ) (h:0<t.im) (v:T) : inner ℂ v ((P.dynamics0 j x).F (-Complex.I*t) v) = ∫ r:ℝ, Complex.exp ((r:ℂ)*t*Complex.I) ∂ (P.energyE j x v):=by
  let m:=(D).ℚmeasure.diagonal v; let e(x:E4):ℝ:=x j
  have he:Measurable e:= by unfold e; fun_prop
  rw [energyE,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* t*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*t*Complex.I))).aestronglyMeasurable)]
  have ht:=(D).heat 0 v (z:=t) (show t∈_ from h.le)
  rw [OS.Semigroup.J, (D).lift_ray v h] at ht
  simpa [ (D).unit.origin,Probe.plane,e] using ht
lemma grid_member(t:ℝ≥0)(g:Grid j): P.Eucl j t*P.movesOf j g=P.movesOf j g*P.Eucl j t:=Subtype.ext ((ladder_time Y H V (π).circuit j 0 false C₀ g.2.2 t (notch M g.1 g.2.1)).symm)
lemma edge_grid(t:ℝ)(g:Grid j): ((Φ x) (P.movesOf j g)).comp ((P.dynamics0 j x).edge t)= ((P.dynamics0 j x).edge t).comp ((Φ x) (P.movesOf j g)):=by
  refine within_energy (D) (D) _ (fun s=>?_) t
  change (Φ x) (P.movesOf j g) * (Φ x) (P.Eucl j s) = (Φ x) (P.Eucl j s) * (Φ x) (P.movesOf j g); simp_rw [←map_mul,P.grid_member]
lemma vacuum_edge(t:ℝ): (P.dynamics0 j x).edge t (P.emptyV j x)= P.emptyV j x:= (heat_iff_edge j _ _|>.1 (P.at_full j x)) t
lemma vacuum_full(z:T): z∈ rooted (P.portion j x) (P.jointTest j) ↔
    (∀ t:ℝ,(P.dynamics0 j x).edge t z=z) ∧ ∀ g : Grid j,(Φ x) (P.movesOf j g) z=z:=by
  change (Φ x) (P.jointTest j) z=z ↔ _
  rw [←heat_iff_edge]; refine (P.joint_ext j T (Φ x) z).trans ?_
  refine ⟨fun p=> ⟨fun t=>?_,p.2⟩,fun p=>⟨fun s n=>p.1 _,p.2⟩⟩
  apply tendsto_nhds_unique (((D).continuousE z).continuousAt.tendsto.comp (shade M t)); exact tendsto_const_nhds.congr (fun i=>(p.1 i _).symm)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.journey_cont
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.heat_iff_edge
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.vacuum_full
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.energy_read
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.energy_pa
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.energy_char
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.edge_grid
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stateVoxLinear
