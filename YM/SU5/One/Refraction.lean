import YM.SU5.One.Beacon
/-!
# Lantern constraints and meaning of interaction

The test diagnoses failure of product law on gauge- and matter-only marks
in the original field assignments on the local Euclidean resolution system.
A product law there would already, in particular, require `SingleExposureSplit`
for *loose* evaluations. These evaluations are defined by this same state and
are for elementary probes, not assumed to be in the gauge-invariant part
separately (we are testing an actual factorization proposal for the joint
functional). Both kinds of pure probes are taken from the **narrow** system
(first links, continuous gauge coefficients; local chiral Grassmann words).
The products tested here involve marks on two *separated*, fixed openable
sets. Not a claim of failure of independence BETWEEN the two distant sets! And
NOT a claim of a truncated Wightman function or departure from asymptotic
freeness in some comparison vacuum.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude
open Selected CF.Pannier.Chancel

section acetate
variable {J : Calibration}

/-- tested in the gauge-only class (use with narrow admissibility for
first-field). -/
def glassOnly (f : Family J) := ∀ m : Side,∀ W:Fields (J.c m),∃ z:ℂ,f m W= z • (1:FC (Single (J.c m)))

/-- Raw chiral-matter only (use with InTest). -/
def inkOnly (f : Family J) := ∀ m : Side,∀ U V:Fields (J.c m), f m U=f m V

lemma scalar_glass (v : PairsC → ℂ) : glassOnly (Buffered.scalar J v):=fun _ _=> ⟨_,rfl⟩
variable (j : Axis) (z : ℤ)
lemma mirror_glass {f : Family J} (p : glassOnly f): glassOnly (mirror J j z f):= by
  intro m x; obtain ⟨a,t⟩:=p m (reflFields j z x)
  refine ⟨star a,?_⟩; unfold mirror reflMark; rw [t,theta_smul,theta_one]
lemma mirror_ink {f : Family J} (p : inkOnly f): inkOnly (mirror J j z f):= fun n x y=>congrArg (theta (carR j z _)) (p n (reflFields j z x) (reflFields j z y))
lemma transit_glass (v:List Axis) (y:Cover) {f : Family J} (p : glassOnly f): glassOnly (cad J v y f):= by
 induction v with
 | nil => exact p
 | cons i v ih=> exact mirror_glass i _ (mirror_glass i 0 ih)
lemma transit_ink (v:List Axis) (y:Cover) {f : Family J} (p : inkOnly f): inkOnly (cad J v y f):= by
 induction v with
 | nil => exact p
 | cons i v ih=> exact mirror_ink i _ (mirror_ink i 0 ih)
private lemma ink_span {f g : Family J} (p : inkOnly f) (q:inkOnly g): inkOnly (f+g):=fun m x y=> congrArg₂ (fun v u:FC (Single (J.c m))=>v+u) (p m x y) (q m x y)
private lemma ink_amp (c:ℂ) {f:Family J}(p:inkOnly f): inkOnly (c • f):=fun m x y=> congrArg (fun h:FC (Single (J.c m))=>c • h) (p m x y)
private lemma ink_roll {f g:Family J}(p:inkOnly f)(q:inkOnly g):inkOnly (f*g):=fun m x y=> congrArg₂ (fun v u:FC (Single (J.c m))=>v*u) (p m x y) (q m x y)
lemma ink_row {k:ℕ}{b: Fin k → Cover} {W T L} {f:Family J}(p:CRow J W b T L f): inkOnly f:= by
 induction p with
 | gave=>exact fun _ _ _=> rfl
 | pair i j _ _ _ _ _ _ _ _ _ _ _ _ ih=> exact ink_roll (ink_roll (fun _ _ _=>rfl) (fun _ _ _=>rfl)) ih
 | zip => exact fun _ _ _=>rfl
 | glaze a _ ih=> exact ink_amp a ih
 | fuse _ _ a b=> exact ink_span a b
lemma ink_lode {k:ℕ}{b: Fin k → Cover} {W T} {f:Family J}(p:f∈Lode J W b T): inkOnly f:= by
 refine Submodule.span_induction (p:=fun f _=> inkOnly f) (fun x t=>?_)
           (fun _ _ _=>rfl) (fun x y _ _ a b=> ink_span a b) (fun x y _ p=> ink_amp x p) p
 obtain ⟨l,h,t,w⟩:= t; exact ink_row w
end acetate

/-! Selected smear, polynomial law. Require in particular only the printed
regions of the factors at the two separated spots. Would pay on all those
finite probes. Show ruled out by the very mark surviving. -/
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
variable {i k:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ} {E:ℕ→Family (tent Y H)→ℂ} (V: Universal Y H i k I E)
    (G: GroundExtension (i:=i) (k:=k) (E:=E) Y H) {L:Tapestry.Rack Λ l}{B:Tapestry.Clay Λ l}
    (D: Exhibition Y H i k I E L B)
variable (d : Axis) (S : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "𝔄" j:max=> displayAlgebra Y H V G.history G.clipped j false (S j)
variable (c : displayAlgebra Y H V G.history G.clipped d false (S d) →⋆ₐ[ℂ] ℂ)
local notation "C"=> SameCharacter.resident Y H V G d false (S d) c
local notation "Θ"=> onDrawing Y H V G D d S C
local notation "Mx"=> evaluate Y H V G d S C
local notation "r" j:max=> displacement Y H V G.history G.clipped d false (S d) c j (S j)
local notation "R" j:max t:max=> Selected.response Y H V t G.history G.clipped j false (S j) (r j)
local notation "κ"=> Dome (tent Y H)
local notation "𝒫" s:max=> pinhole (Dome (tent Y H)) s

def SingleExposureSplit (s:ℕ)(U W : Set RSpace) : Prop:=
  ∀ (Φ Ψ φ ψ : Dome (tent Y H)),
    -- bona fide polynomials in the matter-mark (even) local algebra in which
    -- to test the extensions to colored factors.
    (𝒫 s) Φ∈ocular Y H false s U → glassOnly Φ.val →
    (𝒫 s) Ψ∈ocular Y H false s W → glassOnly Ψ.val →
    (𝒫 s) φ∈ocular Y H false s U → inkOnly φ.val →
    (𝒫 s) ψ∈ocular Y H false s W → inkOnly ψ.val →
    Θ (((𝒫 s) Φ*(𝒫 s) Ψ)*((𝒫 s) φ*(𝒫 s) ψ)) = Θ ((𝒫 s) Φ*(𝒫 s) Ψ) * Θ ((𝒫 s) φ*(𝒫 s) ψ)

variable (s:ℕ)(X:Finset Cover)(j:Axis)(p q:Cover)
local notation "Lw" a:max f:max=> relocateWorld Y H true a f
local notation "X₊"=> streetBox K q X
local notation "X₋"=> reflectedBox j 0 (streetBox K p X)
local notation "W"=> cells Λ l s X₊
local notation "U"=> cells Λ l s X₋
local notation "Θw" f:max=> mirrorInMarks Y H j true f
local notation "Θ₀" f:max=> Θw (Lw p f)
variable (f : Marks (tent Y H) true)
local notation "m"=> Θ₀ f
local notation "n"=> Lw q f
local notation "x"=> photograph Y H s m
local notation "y"=> photograph Y H s n
variable {u k₀ : ℕ}{o:Cover}{δ:ℝ}{z:SU.Slot}
local notation "Mk" v:max Q:max=> (show Marks K true from upward Y H G.history true Q s v)

private lemma press_short {f:κ}{P:Finset Cover}(p : InTest K false P false f.val): (𝒫 s) f∈ocular Y H false s (cells Λ l s P):= by
  exact pokes (Set.univ∩Set.Iic s) (fun i=> keep Λ l i K false (handstamp (cells Λ l s P))) (show s∈Set.univ∩Set.Iic s from ⟨Set.mem_univ _, Set.mem_Iic.mpr le_rfl⟩) ((keeps ..).2 ⟨P,(Tapestry.locates ..).2 p,supported_cells Λ l s P⟩)

private lemma impliesSplit (p₁ : SingleExposureSplit Y H V G D d S c s U W)
    {s':ℕ} (v : Fin s' → Cover) (ζ: Window.Family) : RemoteSplit j K p q X v ζ (Mx s) := by
  let P:= remotePair j (tent Y H) p q
  intro F h Y₀ he A A' hx hz
  have H₀:= Lode_test h; have Hy:=Lode_test he
  let φ: Family K := scalar K A; let ψ:=scalar K A'
  have hp : InTest K false X₋ false (mirror K j 0 (cad K ordinate p φ)):= axial K j _ (cadTest p _ (InTest.seed hx))
  have hq := cadTest (J:=tent Y H) q ordinate (show InTest K false X false ψ from InTest.seed hz)
  have hr := axial K j 0 (cadTest p ordinate H₀); have hd:= cadTest q ordinate Hy
  let X':κ:=⟨_,aux_test hp.widen⟩; let Y':κ:=⟨_,aux_test hq.widen⟩
  let Xw:κ:=⟨_, aux_test hr.widen⟩; let Yw:κ:=⟨_,aux_test hd.widen⟩
  have Ht:= p₁ X' Y' Xw Yw (press_short Y H s hp)
        (mirror_glass j _ (transit_glass _ _ (scalar_glass A)))
        (press_short Y H s hq) (transit_glass _ _ (scalar_glass A'))
        (press_short Y H s hr) (mirror_ink j _ (transit_ink _ _ (ink_lode h)))
        (press_short Y H s hd) (transit_ink _ _ (ink_lode he))
  simp_rw [← map_mul (pinhole (Dome (tent Y H)) s), plugged Y H V G D d S C] at Ht
  rw [remotePair_factors j K p q (aux_test H₀.widen) (aux_test (InTest.seed hz|>.widen))]; exact Ht

/-- This is a concrete obstruction: with all the same assignments any such
split forces the reading of the witness polynomial ITSELF to be 0. Therefore
Lantern's bound on this gauge-neutral two-cell polynomial proves failure of
gauge/matter factorization in this specified sense. -/
theorem film (a:Lantern Y H V G D d S c s X j p q f δ o u k₀ z) (t:Injective (booty o k₀ u)) :
    (SingleExposureSplit Y H V G D d S c s U W → Θ (x*y)=0) ∧
    0<δ ∧ (∀ (O P : RSpace)(i:Axis), O∈ U → P∈ W → O i+δ≤P i) ∧
    1/32≤ ‖Θ (x*y)‖ ∧ ¬ SingleExposureSplit Y H V G D d S c s U W:= by
  have hv := a.estimate 0
  have hZ : (SingleExposureSplit Y H V G D d S c s U W → Θ (x*y)=0):= fun v=> by
    rw [←a.tied]
    unfold photograph; rw [plugged]
    change (Mx s) ((m)*(n)).val=0; rw [a.through.shelf.whole_twin]
    -- adapt price to this reader
    let c':= r j; let E':=pigmentReading Y H V s G.history G.clipped j (S j) c'
    have hw : E'=Mx s:= by
       funext u; by_cases h:TestFamily K true u; · exact (reads_color Y H V s G.history G.clipped j (S j) c' (observe h)).trans (spinLoan Y H V G d S c j s (observe h))
       unfold E' pigmentReading evaluate; rw [dif_neg, dif_neg h]; exact fun p=> h p.1
    rw [←hw]
    have hp:= impliesSplit Y H V G D d S c s X j p q v (booty o k₀ u) (Window.family z)
    exact remotePair_price Y H V s G.history G.clipped j (S j) c' p q (detached_disjoint a.through.shelf.structured) t (show RemoteSplit j K p q X _ _ E' from hw.symm ▸ hp) a.sources a.sources
  refine ⟨hZ,(a.through.shelf.span_positions j).1,a.local_support.2.2.2,hv.1,fun b=>?_⟩
  have ht:=hv.1; rw [hZ b,norm_zero] at ht; norm_num at ht

/-- Joint representation of the very pair, including separate stamps and in
the actual geometry. -/
structure Twin (X1 X2 : Finset Cover) (t k' : ℕ) : Prop where
 uses : Tapestry.Pay Y s t k'
 localized : SupportedPhysically Λ l (Y.uv k') X1 U ∧ SupportedPhysically Λ l (Y.uv k') X2 W
 separated : Disjoint (Satin.region X1 (Journey.side Y t (Y.uv k'))) (Satin.region X2 (Journey.side Y t (Y.uv k')))
     ∧ FullDistances (tips (X1∪X2)) (Journey.side Y t (Y.uv k'))
 jointly_read : ∃ E F: Evaluation (Journey.side Y t (Y.uv k')),
   GradeCall Y H x t k' X1 E ∧ GradeCall Y H y t k' X2 F ∧ GradeCall Y H (x*y) t k' (X1∪X2) (E*F)

private lemma enlarge_photograph {s' : Side} {P Q : Finset Cover}{v : Evaluation s'} (h:P⊆Q) (a:v∈localObs s' (diamonds (Satin.region P s')) (sitesIn s' (Satin.region P s'))) :
    v∈localObs s' (diamonds (Satin.region Q s')) (sitesIn s' (Satin.region Q s')):=by
  have hx : Satin.region P s'⊆Satin.region Q s':=Finset.image_subset_image h
  apply localObs_enlarge (fun i (p : i∈ diamonds (Satin.region P s'))=> ?_) (fun i p=> ?_) a
  · obtain ⟨u,t,b⟩:=mem_filter.mp p; exact mem_filter.mpr ⟨u,hx t,hx b⟩
  obtain ⟨u,t⟩:=mem_filter.mp p; exact mem_filter.mpr ⟨u,hx t⟩

private lemma imprint_two {u v : Altitude.Cloud (Dome (tent Y H))}
    (g:u∈ observatory Y H false s U) (h:v∈ observatory Y H false s W)
    (A:ℝ) (s₁: U⊆ cabin A)(t₁: W⊆ cabin A) (d : Disjoint U W)
    (i k:ℕ)(p' : 4*A+2 < (Journey.side Y i 0).val)
    {P Q : Evaluation (Journey.side Y i (Y.uv k))} {I' J':Finset Cover} (e: Pay Y s i k) (b:GradeCall Y H u i k I' P) (q':GradeCall Y H v i k J' Q) :
    GradeCall Y H (u*v) i k (I'∪J') (P*Q) := by
  refine ⟨Subalgebra.mul_mem _ (enlarge_photograph Finset.subset_union_left b.1) (enlarge_photograph Finset.subset_union_right q'.1), ?_⟩
  rw [stencil_mult Y H i k d s₁ t₁ p' e (astro_loose Y H false s U g) (astro_loose Y H false s W h)]
  exact fun v a=> congrArg₂ (· * ·) (b.2 a) (q'.2 a)

private lemma detaches {Λ:Preparation}{l r':ℕ}{S T:Finset Cover}{q k':Set RSpace}(hx:SupportedPhysically Λ l r' S q)
    (Y':SupportedPhysically Λ l r' T k')(v:Disjoint q k') {s':Side} (p: FullDistances (tips (S∪T)) s') :
    Disjoint (Satin.region S s') (Satin.region T s'):= by
  have h:= also_separation (separatedPhys («U»:=handstamp q) hx Y' (Disjoint.preimage _ v)) (distances_mono (fun _ w=> tips_here _ w) p)
  exact Finset.disjoint_left.mpr fun c g a=> by have w:=h c g c a; simp at w

theorem showing (a:Lantern Y H V G D d S c s X j p q f δ o u k₀ z) :
     ∃ X1 X2 : Finset Cover, SupportedPhysically Λ l s X1 U ∧ SupportedPhysically Λ l s X2 W ∧
       ∀ᶠ v:ℕ in atTop, ∀ᶠ b:ℕ in atTop, ∀ t≥ v, (Y.voyage t).kick ≤ b →
         Twin Y H s X j p q f (volumeAround Λ l (Y.uv b-s) X1) (volumeAround Λ l (Y.uv b-s) X2) t b:=by
  obtain ⟨X1,P0,h⟩:= charter Y H a.exposed.1
  obtain ⟨X2,P1,h₁⟩:= charter Y H a.exposed.2.1
  obtain ⟨C1,u,v⟩:= canBound Λ l s X₊; obtain ⟨C2,e,g⟩:= canBound Λ l s X₋
  let C0:=max C1 C2
  have hp : U ⊆ cabin C0 := (supported_iff_cells.mp g).trans (fun a v i=> (v i).trans (le_max_right ..))
  have hq : W ⊆ cabin C0 := (supported_iff_cells.mp v).trans (fun a v i=> (v i).trans (le_max_left ..))
  have hd:= a.local_support.2.2.1
  obtain ⟨t,r₀⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop («R»:=ℝ)).comp (goes Y H 0)|>.eventually (eventually_gt_atTop (4*C0+2)))
  refine ⟨X1,X2,P0,P1,?_⟩
  filter_upwards [eventually_ge_atTop t] with i hi
  filter_upwards [h,h₁] with k P Q t' t₀ ht
  have hk:s+(Y.uv k-s)=Y.uv k:= Nat.add_sub_of_le P.1.le
  have ha:= P0.persists (Y.uv k-s); have hb:= P1.persists (Y.uv k-s); rw [hk] at ha hb
  have hh : 4*C0+2 < (Journey.side Y t' 0).val:=r₀ t' (le_trans hi t₀)
  have he:=no_alias Y t' C0 hh (Y.uv k) _ (supports_union (support_subset ha hp) (support_subset hb hq))
  have He : Pay Y s t' k:= ⟨ht,P.1.le⟩
  obtain ⟨b,p'⟩:= P.2 t' ht; obtain ⟨M,q'⟩:= Q.2 t' ht
  exact ⟨He,⟨ha,hb⟩,⟨detaches ha hb hd he,he⟩,⟨b,M,p',q',imprint_two Y H s X j p q a.exposed.1 a.exposed.2.1 C0 hp hq hd t' k hh He p' q'⟩⟩
end YM.CF.Buffered.Afterglow.Tower.One
