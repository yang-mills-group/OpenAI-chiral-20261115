import YM.SU5.One.Clearance

/-!
# Actual full-depth supported representatives for Euclidean resolution polynomials

Centers/buffers in units of `location`. We prove facts for the physical region
system of the even-mark theory (tested on all loose families so that the
statement includes, also, tests used in diagnosing gauge--matter factorization
by the reader). Works on every paid history in this Course. In particular IDs
here are for arbitrary multi-resolution polynomials, not special formulas for
which following one stencil without contact rules might suffice.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
variable (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
local notation "𝛱"=> Altitude.Cloud (Dome (tent Y H))

/-- localized, height-filtered polynomials; pigments may be wide. Loose also
allows gauge non-neutral operators. We use `observatory` below for the
physical gauge-neutral system. -/
abbrev ocular (wide : Bool) (s : ℕ) (U : Set RSpace) :=
  jetty Λ l (tent Y H) wide (handstamp U) (Set.univ∩Set.Iic s)

abbrev observatory (wide : Bool) (s : ℕ) (U : Set RSpace) :=
  circum Λ l (tent Y H) wide U (Set.univ∩Set.Iic s)

lemma astro_loose (wide : Bool) (s : ℕ) (U : Set RSpace) :
    observatory Y H wide s U ≤ ocular Y H wide s U:=inf_le_left
lemma optic_short (wide : Bool) (s : ℕ) (U : Set RSpace) :
    ocular Y H wide s U ≤ boardedDB (tent Y H) s:=jettyBan ..
lemma optic_wide (wide : Bool) (s : ℕ) (U : Set RSpace) :
    ocular Y H wide s U ≤ ocular Y H true s U:=exposes ..

/-- The actual mark to be paired with the ket of the course at r (UV cutoff
Y.uv k is not necessarily r). -/
abbrev imprint (r i k : ℕ) (x : Altitude.Cloud (Dome (tent Y H))) :=
   attire (breathing Y H r i k x)
local notation "𝒑" r:max=> imprint Y H r

lemma imprint_add (s i k : ℕ) (x y : 𝛱) :
    (𝒑 s) i k (x+y)=(𝒑 s) i k x + (𝒑 s) i k y:=by unfold imprint; rw [map_add,attire_add]
lemma imprint_scale (s i k : ℕ) (x : 𝛱) (c : ℂ) :
    (𝒑 s) i k (c • x)= c • (𝒑 s) i k x:=by unfold imprint; rw [map_smul,attire_scale]

lemma imprint_step {s : ℕ} (i k : ℕ) {f : Altitude.Cloud (Dome (tent Y H))} (p : f∈ boardedDB K s) :
    imprint Y H (s+1) i k f = ascender Y s i k (imprint Y H s i k f) := by
  unfold imprint breathing
  rw [Decking.joins _ _ _ _ p]
  exact flowing Y s i k _

private lemma imprint_origin {s : ℕ} {x : Altitude.Cloud (Dome (tent Y H))}
    {U : Set RSpace} (t : x∈ ocular Y H true s U) :
    ∃ S : Finset Cover, SupportedPhysically Λ l s S U ∧ ∀ i k, Tapestry.Pay Y s i k →
        AtSupport false (Satin.region S (Journey.side Y i s)) ((𝒑 s) i k x) := by
  apply boarded (P:={f|Officer (Set.univ∩Set.Iic s) (fun i=>keep Λ l i K true (handstamp U)) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ t
  · intro f (p : Officer _ _ f)
    choose W h H₁ using (fun i=> (keeps ..).1 (p.observes i))
    obtain ⟨z,e⟩:= motif_represents K W f h
    refine ⟨frameBudget W Λ l s,frame_lines W s Λ l (fun i _=> H₁ i),fun i k v=>?_⟩
    have hx: Clocked («K»:=K) W s z:=by unfold Clocked; rw [e]; exact p.visible _ _ Set.inter_subset_right
    rw [←e]
    exact wearH Y H i k s W z v hx
  · refine ⟨∅,fun _ h=> (Finset.notMem_empty _ h).elim,fun i k _=>?_⟩
    unfold imprint; rw [map_zero,attire_none]; exact AtSupport.zeroM
  · rintro x y _ _ ⟨S,u,v⟩ ⟨T,q,w⟩
    refine ⟨S∪T, supports_union u q, fun i k t=>?_⟩
    rw [imprint_add]
    exact ((v i k t).mono (Finset.image_subset_image Finset.subset_union_left)).addM
          ((w i k t).mono (Finset.image_subset_image Finset.subset_union_right))
  rintro a x _ ⟨S,u,v⟩
  refine ⟨S,u,fun i k t=>?_⟩
  rw [imprint_scale]; exact (v i k t).smulM _

lemma imprint_advances {s : ℕ} {i k : ℕ} (n : ℕ) {f : Altitude.Cloud (Dome (tent Y H))}
    (e : f∈ boardedDB K s) {S : Finset Cover}
    (q : AtSupport false (Satin.region S (Journey.side Y i s)) (imprint Y H s i k f))
    (p : Tapestry.Pay Y (s+n) i k) :
    AtSupport false (Satin.region (volumeAround Λ l n S) (Journey.side Y i (s+n)))
      (imprint Y H (s+n) i k f) := by
  induction n with
  | zero=> exact q
  | succ n ih=>
    let g:=ih ⟨p.1, le_trans (by omega) p.2⟩
    change AtSupport false _ (imprint Y H ((s+n)+1) i k f)
    rw [imprint_step Y H i k (Altitude.climbs (Dome K) (n:=s) (m:=s+n) (by omega) e)]
    exact ascendSupport Y (s+n) i k _ p g

/-- Simultaneous, fixed observing box, all refinements up through the true
cutoff. -/
theorem carried_support {s : ℕ} {x : Altitude.Cloud (Dome (tent Y H))} {wide : Bool}
    {U : Set RSpace} (t : x∈ ocular Y H wide s U) :
    ∃ S : Finset Cover, SupportedPhysically Λ l s S U ∧
      ∀ (i k n : ℕ), Tapestry.Pay Y (s+n) i k →
        AtSupport false (Satin.region (volumeAround Λ l n S) (Journey.side Y i (s+n)))
          (imprint Y H (s+n) i k x) := by
  obtain ⟨S,h,w⟩:= imprint_origin Y H (optic_wide Y H wide s U t)
  exact ⟨S,h,fun i k n P=> imprint_advances Y H n (optic_short Y H wide s U t)
                 (w _ _ ⟨P.1, (Nat.le_add_right s n).trans P.2⟩) P⟩

-- finite product factorization. Compare `Apart.lean`: there for vistaFinish,
-- on disjoint physical slots. Here through *all* those steps up to the
-- cutoff, one volume bound. Use actual ascender, keep all labels ordered.
variable (i : ℕ) {k : ℕ}

section aperture
variable {A : ℝ} (room : 4*A+2 < (Journey.side Y i 0).val)
variable {U V : Set RSpace} (sep : Disjoint U V) (hU : U ⊆ cabin A) (hV : V ⊆ cabin A)
include room sep hU hV
private lemma mates {P Q : Finset Cover} {s : ℕ}
    (p : SupportedPhysically Λ l s P U) (q : SupportedPhysically Λ l s Q V)
    (b : Tapestry.Pay Y (s+1) i k) {x y : Ward (Journey.side Y i s)}
    (hx : AtSupport false (Satin.region P (Journey.side Y i s)) (attire x))
    (hy : AtSupport false (Satin.region Q (Journey.side Y i s)) (attire y)) :
    (tidalDressing Y H i k).surge s (x*y)=
      (tidalDressing Y H i k).surge s x * (tidalDressing Y H i k).surge s y:= by
  have hp : Tower.Detached Λ l P Q:= separatedPhys (V:=handstamp V) p q (Disjoint.preimage _ sep)
  let h := no_alias Y i A room _ (P∪Q) (supports_union (support_subset p hU) (support_subset q hV))
  have w := also_separation hp (distances_mono (fun _ v=> tips_here (P∪Q) v) h)
  apply attireL_inj
  change attire (rhythm Y _ _ _ (x*y)) = attire (rhythm Y s i _ x * rhythm Y s i _ y)
  rw [attire_mul,flowing, flowing, flowing, attire_mul]
  exact ascendSep Y _ _ _ b hx hy w

omit room sep hU hV
private lemma offered {s : ℕ} (b : Tapestry.Pay Y s i k) (x : ℕ→Dome (tent Y H))
    {V : Set RSpace} (p : ∀ j, x j ∈ keep Λ l j K true (handstamp V)) :
    ∃ W : Finset Cover, SupportedPhysically Λ l s W V ∧
       AtSupport false (Satin.region W (Journey.side Y i s))
           (attire ((tidalDressing Y H i k).finish s x)):= by
  choose W h hw using (fun i=> (keeps ..).1 (p i))
  obtain ⟨t,e⟩:= motif_represents K W x h
  refine ⟨frameBudget W Λ l s,frame_lines W s Λ l (fun i _=> hw i),?_⟩
  rw [←e]; exact wearSupport Y H i k s W t b
include room sep hU hV
private lemma paired_film {s : ℕ} (q : Tapestry.Pay Y s i k) (x y : ℕ → Dome (tent Y H))
    (a : ∀ j,x j ∈ keep Λ l j K true (handstamp U)) (b : ∀ j,y j ∈ keep Λ l j K true (handstamp V)) :
    Decking.finish (tidalDressing Y H i k) s (x*y) = Decking.finish (tidalDressing Y H i k) s x * Decking.finish (tidalDressing Y H i k) s y := by
  induction s with
  | zero=> exact map_mul ((tidalDressing Y H i k).perceive 0) ..
  | succ s ih=>
     have h₀:Tapestry.Pay Y s i k:= ⟨q.1,le_of_lt q.2⟩
     obtain ⟨P,hx,ex⟩:= offered Y H i h₀ x a
     obtain ⟨Q,hy,ey⟩:= offered Y H i h₀ y b
     rw [Decking.finish,Decking.finish,Decking.finish,ih h₀,
       mates Y H i room sep hU hV hx hy q ex ey,Pi.mul_apply,map_mul]; ac_rfl

/-- Pair multiplication commutes with imprint on geometrically separate
observables; does not change the expectation into a product state. -/
theorem imprint_pair {s : ℕ} (q:Tapestry.Pay Y s i k) {x y : Altitude.Cloud (Dome (tent Y H))}
    {u v : Bool} (p:x∈ ocular Y H u s U) (t:y∈ ocular Y H v s V) :
    imprint Y H s i k (x*y) = imprint Y H s i k x * imprint Y H s i k y := by
  apply congrArg attire (a₁:=_) _ |>.trans (attire_mul ..)
  let M:= Set.univ∩ Set.Iic s; let X:= fun i=> keep Λ l i K true (handstamp U); let W:=fun i=>keep Λ l i K true (handstamp V); let Z:=breathing Y H s i k
  change Z _ = _
  apply boarded (P:={f| Officer M X f}) (M:=fun f=> Z (f*y)= Z f *Z y) ?_ ?_ ?_ ?_ (optic_wide Y H u s U p)
  · intro f (e : Officer M _ f)
    apply boarded (P:={f| Officer M W f}) (M:=fun g=> Z (PiTensorProduct.tprod ℂ f * g)= Z (PiTensorProduct.tprod ℂ f)*Z g) ?_ ?_ ?_ ?_ (optic_wide Y H v s V t)
    · intro g (h : Officer M _ g)
      change Z ((PiTensorProduct.tprod ℂ f)*(PiTensorProduct.tprod ℂ g))=_
      have hx: Enough s f:= e.visible _ _ Set.inter_subset_right
      have hy: Enough s g:= h.visible _ _ Set.inter_subset_right
      unfold Z breathing; rw [PiTensorProduct.tprod_mul_tprod,
       Decking.reckon_paid _ _ _ hx, Decking.reckon_paid _ _ _ hy,
       Decking.reckon_paid _ _ _ (hx.together hy)]; exact paired_film Y H i room sep hU hV q f g e.observes h.observes
    · simp
    · intro a b _ _ h H'; rw [mul_add,map_add,map_add,h,H',mul_add]
    intro a b _ h
    change Z ((pureShot (tent Y H) f)* (a • b))= Z (pureShot (tent Y H) f) * Z (a • b)
    change Z ((pureShot (tent Y H) f)*b)=Z (pureShot (tent Y H) f)*Z b at h
    rw [Algebra.mul_smul_comm,map_smul,map_smul,h,Algebra.mul_smul_comm]
  · simp
  · intro a b _ _ h H'; rw [add_mul,map_add,map_add,h,H',add_mul]
  intro a b _ h; rw [Algebra.smul_mul_assoc,map_smul,map_smul,h,Algebra.smul_mul_assoc]
end aperture

end YM.CF.Buffered.Afterglow.Tower.One
