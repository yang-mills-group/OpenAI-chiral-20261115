import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme

/-! # The two **raw** factor algebras of the wide even tests

`Gate`: pure scalar of BOTH Pane variables (from local cover), includes even the
non-first-pane symbols needed through the actual refinement. `Mantle`: the
matter letters only, in the same ordinary Fock Exterior-even dictionary as the
reader. Not paths/dressed/pins, and no use of purity after fusion across heights.
This is support-compatible, priced on all normalized heights. No extra test-space
completions; uses the actual `Coeff true`, no a.e. quotient. In particular constancy
in both fields at each Side already characterizes the second pure algebra in Dome
by span of its matter words (`mantle_test`). They remain pure through the gauge action.

Build recipes spelling out that the tensor product predictions on this test class
are well-defined; not just disqualifying a vacuous opponent. We avoid introducing
a new coordinate system for f or taking Mathlib's TensorProduct—give its canonical
evaluation `freezePair`, separating the factors instead. Programs may query
`Exposure.glasses`. This is compatible for different supports (including in joint tests).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
attribute [local instance] opCStarAlgebra

section pure
variable {S : Finset Cover} {f g : PairsC → ℂ}
lemma admits_const (S : Finset Cover) (c : ℂ) : Coeff true S (fun _ : PairsC ↦ c) :=
  ⟨fun q ↦ by contradiction,Girt.rite_c _,fun _ _ _ _ ↦ rfl⟩
lemma admits_zero (S : Finset Cover) : Coeff true S 0 := admits_const S 0
lemma admits_add (h : Coeff true S f) (u : Coeff true S g) : Coeff true S (f+g) :=
  ⟨fun q ↦ by contradiction,Girt.kitE _ _ (· + ·) (by fun_prop) h.env u.env,
   fun _ _ p q ↦ congrArg₂ (· + ·) (h.locus _ _ p q) (u.locus _ _ p q)⟩
lemma admits_scale (c : ℂ) (h : Coeff true S f) : Coeff true S (c • f) :=
  Sound.tone (admits_const S c) h
lemma admits_iterate {I : Type*} (s : Finset I) (f : I → PairsC → ℂ)
    (h : ∀ i∈s, Coeff true S (f i)) : Coeff true S (∑ i∈s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact admits_zero S
  | insert i s hi ih =>
    rw [sum_insert hi]; exact admits_add (h _ (mem_insert_self ..))
      (ih (fun j g ↦ h _ (mem_insert_of_mem g)))

variable (K : Calibration)
def markInk (h : Coeff true S f) : Dome K := ⟨scalar K f,broadCompile K S (InTest.seed h)⟩

lemma ink_const (S : Finset Cover)(c : ℂ) : markInk K (admits_const S c)=c • 1:=rfl
lemma ink_unit (S : Finset Cover) : markInk K (Sound.ice (S:=S))=1:=Subtype.ext Sound.unitLink
lemma ink_zero (S : Finset Cover) : markInk K (admits_zero S)=0 := by
  rw [show markInk K _= (0:ℂ) • 1 from rfl,zero_smul]
lemma ink_add (h : Coeff true S f) (u : Coeff true S g) :
    markInk K (admits_add h u) = markInk K h+markInk K u :=
  Subtype.ext (funext (fun m ↦ funext (fun W ↦ add_smul (f _) (g _) (1:FC _))))
lemma ink_mul (h : Coeff true S f) (u : Coeff true S g) :
    markInk K (Sound.tone h u) = markInk K h*markInk K u := by
  apply Subtype.ext; funext m x; change (f _*g _) • (1:FC _)=(f _ • (1:FC _)) * (g _ • (1:FC (Single (K.c m))))
  rw [mul_smul, Algebra.smul_mul_assoc,one_mul]
lemma ink_scale (h : Coeff true S f) (c : ℂ) :
    markInk K (admits_scale c h)= c • markInk K h :=
  Subtype.ext (funext fun m ↦ funext fun W ↦ mul_smul c (f _) (1:FC _))

-- the pure paid scalar **subalgebra** here with any support
-- Coeff & its own footprint. Nothing about .enclave.
def Gate : Subalgebra ℂ (Dome K) where
  carrier := {f | ∃ S : Finset Cover, ∃ g : PairsC → ℂ, ∃ h : Coeff true S g, f=markInk K h}
  mul_mem' := by
    rintro _ _ ⟨S,x,u,rfl⟩ ⟨T,y,e,rfl⟩
    let p := Sound.tone (u.mono (subset_union_left (s₂:=T))) (e.mono (subset_union_right (s₁:=S)))
    exact ⟨S∪T,x*y,p,(ink_mul K (u.mono (subset_union_left (s₂:=T))) (e.mono (subset_union_right (s₁:=S)))).symm⟩
  add_mem' := by
    rintro _ _ ⟨S,x,u,rfl⟩ ⟨T,y,e,rfl⟩
    let p := admits_add (u.mono (subset_union_left (s₂:=T))) (e.mono (subset_union_right (s₁:=S)))
    exact ⟨S∪T,x+y,p,(ink_add K (u.mono (subset_union_left (s₂:=T))) (e.mono (subset_union_right (s₁:=S)))).symm⟩
  zero_mem' := ⟨∅,0,admits_zero ∅,(ink_zero K ∅).symm⟩
  one_mem' := ⟨∅,1,ice,(ink_unit K ∅).symm⟩
  algebraMap_mem' z := ⟨∅,_,admits_const ∅ z,(Algebra.algebraMap_eq_smul_one z).trans (ink_const K ∅ z).symm⟩

lemma ink_mem (h : Coeff true S f) : markInk K h∈ Gate K:= ⟨S,f,h,rfl⟩
lemma ink_locates (h : Coeff true S f) : markInk K h∈ bay K S true := InTest.seed h

def Mantle : Subalgebra ℂ (Dome K) where
  carrier := {f : Dome K| ∀ (m : Side) (x y : Fields (K.c m)), f.val m x=f.val m y}
  mul_mem' := fun {x y} p q m W V ↦ congrArg₂ (· * ·) (p m W V) (q m W V)
  add_mem' := fun {x y} p q m W V ↦ congrArg₂ (· + ·) (p m W V) (q m W V)
  zero_mem' := fun _ _ _ ↦ rfl
  one_mem' := fun _ _ _ ↦ rfl
  algebraMap_mem' c := by rw [Algebra.algebraMap_eq_smul_one]; exact fun _ _ _ ↦ rfl

lemma mantle_iff {f : Dome K} : f∈ Mantle K ↔
    ∀ (m : Side) (x y : Fields (K.c m)), f.val m x=f.val m y := Iff.rfl

section words
variable (S)

def lineWord (v : Evens S) : Dome K := ⟨sing K (tagWord S v.val),
  broadCompile K S (by simpa only [v.property] using sung K (tagWord S v.val) (w:=true) (Satin.brand S v.val))⟩
lemma word_ink (v : Evens S) : lineWord S K v∈ Mantle K :=
  fun m x y ↦ (spool_sing K m _ x).trans (spool_sing K m _ y).symm
lemma word_locates (v : Evens S) (wide : Bool) : lineWord S K v∈ bay K S wide := by
  apply (locates ..).2; simpa only [v.property,lineWord] using sung K (tagWord S v.val) (w:=wide) (Satin.brand S v.val)

-- "the stencil expansion", ordinary finite sum. in the slot-specific bay.
lemma factors (f : Swatch S) : badge K S f= ∑ i : Evens S,
    markInk K (authentic S (f i))*lineWord S K i := Subtype.ext (by
  rw [domTag, render_eq, AddSubmonoidClass.coe_finsetSum]; rfl)
end words
end pure

variable {K : Calibration}{S T : Finset Cover}{u : PairsC}{f g f' g' : Dome K}

structure Exposure (S : Finset Cover) (p : PairsC) (f g : Dome K) : Prop where
  before : f∈ bay K S true
  pure : g∈ Mantle K
  after : g∈ bay K S true
  glasses (m : Side) (W : Fields (K.c m)) :
    Agrees S (onC (K.c m) W.1) p.1 → Agrees S (onC (K.c m) W.2) p.2 → f.val m W=g.val m W

lemma Exposure.larger (h : Exposure S u f g) (v : S ⊆ T) : Exposure T u f g :=
  ⟨tallerBay K S true v h.before,h.pure,tallerBay K S true v h.after,
   fun m x a b ↦ h.glasses m x (fun i p q ↦ a i (v p) (v q)) (fun i p q ↦ b i (v p) (v q))⟩
lemma Exposure.cost (h : Exposure S u f g) (N : Side) (v : Hosp S (K.c N)) (W : Fields (K.c N)) :
    f.val N (replant S (K.c N) u) = g.val N W :=
  (h.glasses _ _ (tacked S _ v _) (tacked S _ v _)).trans (h.pure _ _ _)
lemma Exposure.unique (h : Exposure S u f g) (q : Exposure T u f g') : g=g' := by
  let t := S∪T
  have hp := h.larger (subset_union_left (s₂:=T))
  have hq := q.larger (subset_union_right (s₁:=S))
  obtain ⟨m,v⟩ := (separates K t).exists
  exact Subtype.ext (looksLike ⟨v⟩ ((locates ..).1 hp.after) ((locates ..).1 hq.after)
    (funext fun W ↦ (hp.cost m ⟨v⟩ W).symm.trans (hq.cost m ⟨v⟩ W)))

lemma Exposure.add (h : Exposure S u f f') (e : Exposure S u g g') : Exposure S u (f+g) (f'+g') :=
  ⟨Subalgebra.add_mem _ h.before e.before, Subalgebra.add_mem _ h.pure e.pure,
   Subalgebra.add_mem _ h.after e.after,
    fun N x p q ↦ congrArg₂ (· + ·) (h.glasses N x p q) (e.glasses N x p q)⟩
lemma Exposure.mul (h : Exposure S u f f') (e : Exposure S u g g') : Exposure S u (f*g) (f'*g') :=
  ⟨Subalgebra.mul_mem _ h.before e.before, Subalgebra.mul_mem _ h.pure e.pure,
   Subalgebra.mul_mem _ h.after e.after,
    fun N x p q ↦ congrArg₂ (· * ·) (h.glasses N x p q) (e.glasses N x p q)⟩
lemma Exposure.smul (h : Exposure S u f g) (c : ℂ) : Exposure S u (c • f) (c • g) :=
  ⟨Subalgebra.smul_mem _ h.before c, Subalgebra.smul_mem _ h.pure c,
   Subalgebra.smul_mem _ h.after c, fun N x p q ↦ congrArg (c • ·) (h.glasses N x p q)⟩
lemma same_exposure (h : f∈ Mantle K) (p : f∈ bay K S true) : Exposure S u f f :=
  ⟨p,h,p,fun _ _ _ _ ↦ rfl⟩
lemma Exposure.sum {I : Type*} (L : Finset I) (f g : I → Dome K) (p : ∀ i∈L, Exposure S u (f i) (g i)) :
    Exposure S u (∑ i∈L, f i) (∑ i∈L, g i) := by
  induction L using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact same_exposure (Subalgebra.zero_mem _) (Subalgebra.zero_mem _)
  | insert i s h ih =>
    rw [sum_insert h,sum_insert h]; exact (p i (mem_insert_self ..)).add
      (ih fun j v ↦ p j (mem_insert_of_mem v))

lemma Exposure.seed {f : PairsC→ℂ} (h : Coeff true S f) : Exposure S u (markInk K h) (f u • 1) := by
  refine ⟨ink_locates K h,(Mantle K).smul_mem (Subalgebra.one_mem _) _,(bay K S true).smul_mem (Subalgebra.one_mem _) _,?_⟩
  intro m W p q; change f _ • (1:FC _) = f u • 1
  rw [h.locus _ _ p q]

lemma Exposure.badged (x : Swatch S) : Exposure S u (badge K S x) (∑ i:Evens S,
    daub S (x i) u • lineWord S K i) := by
  have ht(i : Evens S) := (Exposure.seed (u:=u) (K:=K) (authentic S (x i))).mul
    (same_exposure (word_ink S K i) (word_locates S K i true))
  rw [factors]
  apply Exposure.sum; intro i _; specialize ht i; rwa [Algebra.smul_mul_assoc,one_mul] at ht

lemma exposed_local (h : f∈ bay K S true) (p : PairsC) : ∃ g : Dome K, Exposure S p f g := by
  obtain ⟨x,rfl⟩ := accolade K S f h
  exact ⟨_,Exposure.badged x⟩

section
variable (K u)
private def draft (f : Dome K) : Dome K := (exposed_local (precinct_spec K f) u).choose
private lemma a_draft (h : f∈ bay K S true) : Exposure S u f (draft K u f) := by
  have t := (exposed_local (precinct_spec K f) u).choose_spec
  obtain ⟨g,e⟩ := exposed_local h u
  exact (show g=draft K u f from e.unique t) ▸ e
private lemma read_draft (h : Exposure S u f g) : draft K u f = g := (a_draft K u h.before).unique h

def freezePairₗ : Dome K →ₗ[ℂ] Dome K where
  toFun := draft K u
  map_add' f g := by
    obtain ⟨S,h,g⟩ := coAwake K f g
    exact read_draft K u ((a_draft K u h).add (a_draft K u g))
  map_smul' p f := read_draft K u ((a_draft K u (precinct_spec K f)).smul p)

def freezePair : Dome K →ₐ[ℂ] Dome K := AlgHom.ofLinearMap (freezePairₗ K u)
  (read_draft K u (same_exposure (Mantle K|>.one_mem) (bay K ∅ true|>.one_mem)))
  (fun f g ↦ by obtain ⟨S,h,g⟩ := coAwake K f g; exact read_draft K u ((a_draft K u h).mul (a_draft K u g)))

lemma exposed (h : f∈ bay K S true) : Exposure S u f (freezePair K u f) := a_draft K u h
lemma freezePair_const (f : Dome K) : freezePair K u f∈ Mantle K := (a_draft K u (precinct_spec K f)).pure
lemma freezePair_id (h : f∈ Mantle K) : freezePair K u f=f := read_draft K u (same_exposure h (precinct_spec ..))
lemma freezePair_scalar {f : PairsC→ℂ} (h : Coeff true S f) : freezePair K u (markInk K h)=f u • 1 :=
  read_draft K u (Exposure.seed h)
lemma freezePair_expansion (x : Swatch S) : freezePair K u (badge K S x)=
    ∑ i:Evens S, daub S (x i) u • lineWord S K i := read_draft K u (Exposure.badged x)
end

lemma paid_constant {N : Side} (h : Hosp S (K.c N)) (a : f∈ bay K S true)
    (e : ∀ x y, f.val N x=f.val N y) : f∈ Mantle K := by
  let x : PairsC := (1,1); let g := freezePair K x f
  have hp := exposed K x a
  have he : f=g:= Subtype.ext (looksLike h ((locates ..).mp a) ((locates ..).mp hp.after)
    (funext fun W ↦ (e W _).trans (hp.cost N h W)))
  rw [he]; exact hp.pure

lemma mantle_test (p : f∈ bay K S true) : f∈ Mantle K ↔
    f ∈ Submodule.span ℂ (Set.range (lineWord S K)) := by
  constructor
  · obtain ⟨x,rfl⟩ := accolade K S f p
    intro h; rw [←freezePair_id K (1,1) h,freezePair_expansion]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  intro h; exact (Submodule.span_le.mpr (show Set.range (lineWord S K)⊆(Mantle K).toSubmodule
    from by rintro _ ⟨x,rfl⟩; exact word_ink S K x) : _ ≤ _) h

variable (G : GVertex)

lemma mantleWard (p : f∈ Mantle K) : pennant K G f∈ Mantle K := by
  obtain ⟨S,h⟩ := findsBay K f
  obtain ⟨m,v⟩ := (separates K S).exists
  obtain ⟨g,u⟩ := scoreTrace G (⟨v⟩ : Hosp S (K.c m)); let V := pennant K G f
  apply paid_constant (N:=m) ⟨v⟩ (pennantLocal K S G h)
  intro x y
  exact (twist (quantU (tradew (K.c m) g))).injective (
    ((pennantTrace K S G h m g u x).symm.trans (p m _ _)).trans (pennantTrace K S G h m g u y))

-- copy/calibrateScalar (since doesn't preserve mark representation in type statement)
private lemma gaugeCover_cont : Continuous (fun f:LinksC => Lattice.gauge G f) := by
  apply continuous_pi; intro e; unfold Lattice.gauge; fun_prop
private lemma turn_agrees {x y:LinksC} (h : Agrees S x y) :
    Agrees S (Lattice.gauge G x) (Lattice.gauge G y) := by
  intro i u v; unfold Lattice.gauge; rw [h _ u v]
lemma gateWard (p : f∈ Gate K) : pennant K G f∈ Gate K := by
  obtain ⟨S,x,h,rfl⟩ := p
  let W := fun x:LinksC ↦ Lattice.gauge G x; let f := x ∘ Prod.map W W
  have hf : Coeff true S f := ⟨fun q ↦ by contradiction, Env.along h.env
    ((gaugeCover_cont G).measurable.prodMap (gaugeCover_cont G).measurable),
    fun X Y a b ↦ h.locus _ _ (turn_agrees G a) (turn_agrees G b)⟩
  refine (show pennant K G (markInk K h)= markInk K hf from
    appointed K S G (markInk K h) (markInk K hf) ?_ (ink_locates K hf)) ▸ ?_
  · intro m u t v
    change x _ • (1:FC _)=twist (quantU _) (f _ • 1)
    rw [twist_scalar,map_one]; exact congrArg (fun z : ℂ ↦ z • (1:FC _))
      (h.locus _ _ (gauge_trace G t v.1) (gauge_trace G t v.2))
  exact ink_mem K hf
end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms freezePair
#print axioms mantle_test
#print axioms gateWard
#print axioms mantleWard
end YM.CF.Buffered.Afterglow.Pockets
