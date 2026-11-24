import VerifiedSatinSelectedSectors
import Mathlib.Order.Filter.Germ.Basic

/-!
# A test space for reconstruction, I: single-insertion semantics

Euclidean R4. `the construction notes`. Both the wide even extensions and the physical
(singlet) system. Order of operations matters: BUY a support in physical R4 (units of
level-zero matter lattice) and a height s for each term. Finish any polynomial into
one insertion there; only separated multiplication after this. All finer realizations
in the same regions. No identification of terms with more localized terms via OS-null
vectors. Not a Wightman reconstruction. One should import this development in the
supplied cached project (base `VerifiedSatinSelectedSectors`).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {J : Calibration} {U W : Set RSpace}

/-- Streaming ONE insertion, as a linear morphism, from level s to t when t≥s.
For t<s the dummy value is immaterial (the formula uses 0 steps). -/
noncomputable def spreadTo (s t : ℕ) : Dome (tent Y H) →ₗ[ℂ] Dome (tent Y H) where
  toFun x := ⟨stream Y H G.refine s (t-s) x.val,
    streams_test Y H G.history.circuit s (t-s) ((marque _).mp x.property)⟩
  map_add' x y := Subtype.ext <| woven_add Y H G.history.circuit s (t-s)
    ((marque _).mp x.property) ((marque _).mp y.property)
  map_smul' c x := Subtype.ext <| woven_smul Y H G.history.circuit s (t-s)
    ((marque _).mp x.property) c

local notation "D" => spreadTo Y H G

@[simp] theorem spreadTo_val (s t : ℕ) (x : Dome K) :
    (D s t x).val = stream Y H G.refine s (t-s) x.val := rfl

@[simp] theorem spreadTo_refl (s : ℕ) (x : Dome K) : D s s x = x := by
  apply Subtype.ext
  rw [spreadTo_val,Nat.sub_self]
  rfl

@[simp] theorem spreadTo_one (s t : ℕ) : D s t 1 = 1 :=
  Subtype.ext <| woven_one Y H G.history.circuit s (t-s)

theorem spreadTo_trans {s r t : ℕ} (h : s ≤ r) (h' : r ≤ t) (x : Dome K) :
    D r t (D s r x) = D s t x := by
  apply Subtype.ext
  simp only [spreadTo_val]
  rw [show t-s = (r-s)+(t-r) by omega, joined, show s+(r-s)=r by omega]

/-- Concretely in a physical region. `singlets` asks neutrality (at every Side).
Use `keep` with the unit conversion. `keep`'s wide flag is *different*:
here always true (joint link arguments on the one history). -/
def insideAt (Λ : Preparation) (l : ℕ) (J : Calibration) (singlets : Bool)
    (U : Set RSpace) (s : ℕ) : Subalgebra ℂ (Dome J) :=
  keep Λ l s J true (PhaseChoice.handstamp U) ⊓
    if singlets then enclave J else ⊤

variable {singlets : Bool}

theorem mem_insideAt (x : Dome J) (s : ℕ) :
    x ∈ insideAt Λ l J singlets U s ↔
      (∃ S, InTest J true S false x.val ∧ PhaseChoice.SupportedPhysically Λ l s S U) ∧
        (singlets = true → CovCover J x.val) := by
  cases singlets
  · simp only [insideAt,Bool.false_eq_true,↓reduceIte,inf_top_eq, false_implies, and_true]
    rfl
  simp only [insideAt, ↓reduceIte, forall_const]
  rfl

theorem insideAt_mono {s : ℕ} (p : U ⊆ W) :
    insideAt Λ l J singlets U s ≤ insideAt Λ l J singlets W s :=
  inf_le_inf (rooms _ _ _ _ _ _ (Set.preimage_mono p)) le_rfl

theorem insideAt_loose (s : ℕ) : insideAt Λ l J true U s ≤ insideAt Λ l J false U s := by
  unfold insideAt
  gcongr
  simp

theorem insideAt_univ_loose (s : ℕ) : insideAt Λ l J false Set.univ s = ⊤ := by
  simp only [insideAt,PhaseChoice.handstamp,Set.preimage_univ, Bool.false_eq_true,
    ↓reduceIte,inf_top_eq,fullKeep,vestibuleFull]

theorem insideAt_univ_singlet (s : ℕ) : insideAt Λ l J true Set.univ s = enclave J := by
  simp only [insideAt,PhaseChoice.handstamp,Set.preimage_univ,↓reduceIte,fullKeep,
    vestibuleFull, top_inf_eq]

theorem inside_spread {s t : ℕ} {x : Dome K} (h : x ∈ insideAt Λ l K singlets U s)
    (p : s ≤ t) : D s t x ∈ insideAt Λ l K singlets U t := by
  obtain ⟨⟨S,e,v⟩,h⟩ := (mem_insideAt x s).1 h
  have r : s+(t-s)=t := by omega
  exact (mem_insideAt (D s t x) t).2
    ⟨⟨_,(proceeds Y H G.history.circuit s (t-s) e).1,by simpa only [r] using v.persists (t-s)⟩, fun z =>
      ((obs_in ..).1 (chroma Y H G.history.circuit s (t-s) ((obs_in ..).2 ⟨e,h z⟩))).2⟩

theorem spreadTo_separated {s t : ℕ} {x y : Dome K}
    {q q' : Bool} (h : x ∈ insideAt Λ l K q U s) (p : y ∈ insideAt Λ l K q' W s)
    (e : Disjoint U W) : D s t (x*y) = D s t x * D s t y := by
  obtain ⟨⟨S,a,b⟩,_⟩ := (mem_insideAt x s).1 h
  obtain ⟨⟨T,c,d⟩,_⟩ := (mem_insideAt y s).1 p
  exact Subtype.ext <| woven_product Y H G.history.circuit s (t-s) a c
    (PhaseChoice.separatedPhys b d (Disjoint.preimage _ e))

/-- AMBIENT germs: no assertion they are all usable insertions. -/
abbrev Sky (J : Calibration) := Filter.Germ (atTop : Filter ℕ) (Dome J)

/-- An actual single-insertion stream, for our law. -/
noncomputable def ticket (s : ℕ) : Dome (tent Y H) →ₗ[ℂ] Sky (tent Y H) where
  toFun f := ↑(fun t => spreadTo Y H G s t f)
  map_add' f g := Filter.Germ.coe_eq.mpr <| Eventually.of_forall (fun t => map_add (D s t) f g)
  map_smul' c f := Filter.Germ.coe_eq.mpr <| Eventually.of_forall (fun t => map_smul (D s t) c f)

local notation "Jt" => ticket Y H G

@[simp] theorem ticket_one (s : ℕ) : Jt s 1 = 1 := by
  refine Filter.Germ.coe_eq.mpr ?_
  exact Eventually.of_forall (spreadTo_one Y H G s)

theorem ticket_eq (s t : ℕ) (f f' : Dome K) :
    Jt s f = Jt t f' ↔ ∀ᶠ n in atTop, D s n f = D t n f' := Filter.Germ.coe_eq

theorem ticket_eq_stage (s t : ℕ) (f f' : Dome K) :
    Jt s f = Jt t f' ↔ ∃ n, s ≤ n ∧ t ≤ n ∧ D s n f = D t n f' := by
  rw [ticket_eq]
  constructor
  · intro h
    exact ((eventually_ge_atTop s).and ((eventually_ge_atTop t).and h)).exists
  rintro ⟨n,p,q,h⟩
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [← spreadTo_trans Y H G p hN, ← spreadTo_trans Y H G q hN, h]

@[simp] theorem ticket_spread {s t : ℕ} (p : s ≤ t) (f : Dome K) :
    Jt t (D s t f) = Jt s f :=
  (ticket_eq_stage Y H G t s _ _).2 ⟨t,le_rfl,p,spreadTo_refl ..⟩

theorem ticket_separated {s : ℕ} {x y : Dome K}
    {q q' : Bool} (h : x ∈ insideAt Λ l K q U s) (p : y ∈ insideAt Λ l K q' W s)
    (e : Disjoint U W) : Jt s (x*y) = Jt s x * Jt s y :=
  Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun _ => spreadTo_separated Y H G h p e

/-- One-insertion domain in U. `true` is our gauge invariant domain. -/
def Domain (singlets : Bool) (U : Set RSpace) : Submodule ℂ (Sky (tent Y H)) where
  carrier := { x | ∃ s f, f ∈ insideAt Λ l (tent Y H) singlets U s ∧ x = Jt s f }
  zero_mem' := ⟨0,0, (insideAt Λ l K singlets U 0).zero_mem, (map_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨s,f,p,rfl⟩ ⟨t,g,q,rfl⟩
    let r := max s t
    have a : s ≤ r := le_max_left ..
    have b : t ≤ r := le_max_right ..
    refine ⟨r,_,(insideAt Λ l K singlets U r).add_mem (inside_spread Y H G p a) (inside_spread Y H G q b),?_⟩
    rw [map_add,ticket_spread Y H G a,ticket_spread Y H G b]
  smul_mem' := by
    rintro c _ ⟨s,f,p,rfl⟩
    exact ⟨s,c • f,(insideAt Λ l K singlets U s).toSubmodule.smul_mem c p,(map_smul _ _ _).symm⟩

local notation "𝒟" => Domain Y H G

theorem domain_iff {x : Sky K} :
    x ∈ 𝒟 singlets U ↔ ∃ s f, f ∈ insideAt Λ l K singlets U s ∧ x = Jt s f := Iff.rfl

theorem ticket_mem {s : ℕ} {x : Dome K} (p : x ∈ insideAt Λ l K singlets U s) :
    Jt s x ∈ 𝒟 singlets U := (domain_iff Y H G).2 ⟨_,_,p,rfl⟩

/-- Every request can be brought to ANY sufficiently fine observing height,
without losing its physical support. `Eventually` permits finite (NOT countable)
simultaneous consumption. -/
theorem domain_eventually {x : Sky K} : x ∈ 𝒟 singlets U ↔
    ∀ᶠ s in atTop, ∃ f, f ∈ insideAt Λ l K singlets U s ∧ x = Jt s f := by
  rw [domain_iff]
  constructor
  · rintro ⟨s,f,p,rfl⟩
    exact (eventually_ge_atTop s).mono fun t ht =>
      ⟨D s t f,inside_spread Y H G p ht,(ticket_spread Y H G ht f).symm⟩
  exact fun h => h.exists

theorem domain_mono (p : U ⊆ W) : 𝒟 singlets U ≤ 𝒟 singlets W := by
  rintro _ ⟨s,f,h,rfl⟩
  exact ⟨s,f,insideAt_mono p h,rfl⟩

theorem domain_loose (U : Set RSpace) : 𝒟 true U ≤ 𝒟 false U := by
  rintro _ ⟨s,f,h,rfl⟩
  exact ⟨s,f,insideAt_loose s h,rfl⟩

theorem ticket_loose (s : ℕ) (f : Dome K) : Jt s f ∈ 𝒟 false univ :=
  ⟨s,f,by rw [insideAt_univ_loose]; exact Algebra.mem_top,rfl⟩

@[simp] theorem domain_one (singlets : Bool) (U : Set RSpace) : (1 : Sky K) ∈ 𝒟 singlets U :=
  (ticket_one Y H G 0) ▸ ticket_mem Y H G (insideAt Λ l K singlets U 0 |>.one_mem)

/-- Prefactorization products. NO multiplication on the whole domain asserted! -/
theorem domain_mult {f g : Sky K} (p : f ∈ 𝒟 singlets U) (q : g ∈ 𝒟 singlets W)
    (h : Disjoint U W) : f*g ∈ 𝒟 singlets (U ∪ W) := by
  obtain ⟨s,⟨x,v,rfl⟩,y,t,rfl⟩ := (((domain_eventually Y H G).1 p).and ((domain_eventually Y H G).1 q)).exists
  rw [←ticket_separated Y H G v t h]
  exact ticket_mem Y H G <| Subalgebra.mul_mem _ (insideAt_mono Set.subset_union_left v)
    (insideAt_mono Set.subset_union_right t)

theorem domain_mult_to {A : Set RSpace} {f g : Sky K} (p : f ∈ 𝒟 singlets U)
    (q : g ∈ 𝒟 singlets W) (h : Disjoint U W) (u : U ⊆ A) (v : W ⊆ A) :
    f*g ∈ 𝒟 singlets A := domain_mono Y H G (Set.union_subset u v) (domain_mult Y H G p q h)

section factorization


variable {α : Type*} (R : α → Set RSpace)
variable {A : Set RSpace}

/-- Arbitrary finite products in disjoint supports. Multilinearity, symmetry,
associativity and the role of the unit can be checked in the single ambient
commutative ring (the formula for the operations in the domains is just this product). -/
theorem domain_finset_prod (x : α → Sky (tent Y H)) (s : Finset α)
    (p : ∀ i ∈ s, x i ∈ Domain Y H G singlets (R i))
    (q : (s : Set α).PairwiseDisjoint R) (h : ∀ i ∈ s, R i ⊆ A) :
    (∏ i ∈ s, x i) ∈ 𝒟 singlets A := by
  classical
  induction s using Finset.induction_on generalizing A with
  | empty => rw [Finset.prod_empty (f:=x)]; exact domain_one ..
  | @insert i s hv ih =>
    rw [Finset.prod_insert hv]
    let B := ⋃ b ∈ s, R b
    have hB : B ⊆ A := Set.iUnion₂_subset fun b hb => h b (Finset.mem_insert_of_mem hb)
    have hq : (s : Set α).PairwiseDisjoint R := q.subset (fun _ hb => Finset.mem_insert_of_mem hb)
    exact domain_mult_to Y H G (p i (Finset.mem_insert_self ..))
      (ih (fun b hb => p b (Finset.mem_insert_of_mem hb)) hq
        (fun b hb => Set.subset_iUnion₂_of_subset b hb (Subset.refl (R b)) : ∀ b ∈ s, R b ⊆ B))
      (Set.disjoint_iUnion_right.mpr fun b => Set.disjoint_iUnion_right.mpr fun hb =>
        q (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem hb) (fun e => hv (e.symm ▸ hb)))
      (h i (Finset.mem_insert_self ..)) hB

-- Bilinearity in the ambient space, hence with the specified domain of the product.
theorem sky_smul_mul (c : ℂ) (x y : Sky K) : (c • x) * y = c • (x*y) := by
  induction x using Filter.Germ.inductionOn with | _ x => ?_
  induction y using Filter.Germ.inductionOn with | _ y => ?_
  exact Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i : ℕ => Algebra.smul_mul_assoc c (x i) (y i)

end factorization

section presentations

local notation "D₀" s:max => insideAt Λ l (tent Y H) singlets U s

variable (singlets U) in
/-- Include level s in region U. -/
noncomputable def enclose (s : ℕ) :
    (insideAt Λ l (tent Y H) singlets U s) →ₗ[ℂ] 𝒟 singlets U where
  toFun f := ⟨Jt s f.val,ticket_mem Y H G f.property⟩
  map_add' _ _ := Subtype.ext (map_add ..)
  map_smul' _ _ := Subtype.ext (map_smul ..)

variable (singlets U) in
noncomputable def refineInside (s t : ℕ) (p : s ≤ t) :
    (insideAt Λ l (tent Y H) singlets U s) →ₗ[ℂ] insideAt Λ l (tent Y H) singlets U t where
  toFun f := ⟨spreadTo Y H G s t f.val,inside_spread Y H G f.property p⟩
  map_add' _ _ := Subtype.ext (map_add ..)
  map_smul' _ _ := Subtype.ext (map_smul ..)

@[simp] theorem enclose_val (s) (f : D₀ s) :
    (enclose Y H G U singlets s f).val = Jt s f.val := rfl

@[simp] theorem refineInside_val {s t} (p : s ≤ t) (x : D₀ s) :
    (refineInside Y H G U singlets s t p x).val = D s t x.val := rfl

@[simp] theorem enclose_refine {s t : ℕ} (p : s ≤ t) (x : D₀ s) :
    enclose Y H G U singlets t (refineInside Y H G U singlets s t p x) =
      enclose Y H G U singlets s x := Subtype.ext (ticket_spread Y H G p x.val)

theorem eventually_enclosed (f : 𝒟 singlets U) :
    ∀ᶠ s in atTop, ∃ x, enclose Y H G U singlets s x = f := by
  filter_upwards [(domain_eventually Y H G).1 f.property] with s ⟨g,p,e⟩
  exact ⟨⟨g,p⟩,Subtype.ext e.symm⟩

variable (singlets U)
variable {X : Type*}
variable [AddCommMonoid X] [Module ℂ X]
variable (P : ∀ s : ℕ, (insideAt Λ l (tent Y H) singlets U s) →ₗ[ℂ] X)
variable (π : ∀ s t : ℕ, ∀ (p : s ≤ t) x, P t (refineInside Y H G U singlets s t p x) = P s x)

include π
-- record even universal property. Later presentations may see their own frames & heat.
theorem assemble_linear : ∃ L : Domain Y H G singlets U →ₗ[ℂ] X,
    ∀ (s : ℕ) (x : insideAt Λ l (tent Y H) singlets U s), L (enclose Y H G U singlets s x)= P s x := by
  choose s x hs using fun f => (eventually_enclosed (singlets:=singlets) (U:=U) Y H G f).exists
  let L (z : 𝒟 singlets U) := P (s z) (x z)
  have e (t : ℕ) (f : insideAt Λ l K singlets U t) (z : 𝒟 singlets U)
      (v : enclose Y H G U singlets t f = z) : L z = P t f := by
    obtain ⟨T,a,b,w⟩ := (ticket_eq_stage Y H G (s z) t (x z).val f.val).1
      (congrArg Subtype.val ((hs z).trans v.symm))
    have he : refineInside Y H G U singlets (s z) T a (x z) =
      refineInside Y H G U singlets t T b f := Subtype.ext w
    exact (π _ _ a _).symm.trans ((congrArg (P T) he).trans (π _ _ b f))
  refine ⟨{ toFun := L, map_add' := ?_, map_smul' := ?_ }, fun s x => e s x _ rfl⟩
  · intro x y
    obtain ⟨j,⟨f,rfl⟩,g,rfl⟩ := ((eventually_enclosed Y H G x).and (eventually_enclosed Y H G y)).exists
    rw [← map_add, e j f _ rfl, e j g _ rfl, e j (f+g) _ rfl,map_add]
  intro c x
  obtain ⟨i,f,rfl⟩ := (eventually_enclosed Y H G x).exists
  rw [← map_smul, e i f _ rfl,e i (c • f) _ rfl,map_smul]; rfl

noncomputable def assemble : Domain Y H G singlets U →ₗ[ℂ] X :=
  (assemble_linear Y H G U singlets P π).choose

@[simp] theorem assemble_enclose (s : ℕ) (x : insideAt Λ l (tent Y H) singlets U s) :
    assemble Y H G U singlets P π (enclose Y H G U singlets s x) = P s x :=
  (assemble_linear Y H G U singlets P π).choose_spec s x

theorem assemble_unique (f : Domain Y H G singlets U →ₗ[ℂ] X)
    (h : ∀ s x, f (enclose Y H G U singlets s x)= P s x) : f = assemble Y H G U singlets P π := by
  ext x
  obtain ⟨i,v,rfl⟩ := (eventually_enclosed Y H G x).exists
  rw [h, assemble_enclose]

end presentations

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
