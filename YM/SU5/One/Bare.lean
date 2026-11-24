import YM.SU5.One.Imprint

/-!
# One physical (first link field) cutoff realization

This is an *exact* identity with the actual normalized histories. It works
with yet BOREL tests on the top torus. Even for polynomials from the wide
system we get physical meaning as a push to chiral marks on the first links,
with support control from `Imprint`. Don't infer a density of a restricted
algebra on the limit from this: testing at the UV cutoff using a family of
marks representing our fixed-resolution observable is not the same as keeping
a mark supported in a shrinking cell. Nor is Eχ pretended to be the Y-limit
without selection.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
variable (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
local notation "𝛱"=> Altitude.Cloud (Dome (tent Y H))
variable (i k : ℕ)
local notation "Y₀"=> Y.voyage i
local notation "N"=> Y.uv k
local notation "r"=> mesh (Y.ir i) Λ.R.L N
local notation "M"=> Journey.side Y i N
local notation "R"=> ((Y₀).X N).gram N
local notation "Q"=> (Y₀).CapeT N
local notation "T"=> Y.meter.a N
local notation "Z"=> partitionZ (R) Λ.U (Q)
local notation "β"=> (R).beta

/-- No replacement by a non-chiral ket or independent sea -/
abbrev bareCore := Vale.capP («K»:=Λ.K) (m:=mesh (Y.ir i) Λ.R.L (Y.uv k)) Λ.U
   (((Y.voyage i).X (Y.uv k)).gram (Y.uv k)).beta (Y.meter.a (Y.uv k))

abbrev bareStencil (f : Altitude.Cloud (Dome (tent Y H))) : Evaluation (Journey.side Y i (Y.uv k)):=
  Heat.both (imprint Y H (Y.uv k) i k f)
local notation "B"=> bareStencil Y H i k
local notation "X"=> bareCore Y i k

def clearStage (s : ℕ) {O : Side} : Set (Pane O) := {x| flags (Y.meter.a s).threshold x=∅}
def bareField (n : Side) (a : Phys n) := inner ℂ (Dial.mateK n) a
local notation "V'"=> fun U : Pane (Journey.side Y i (Y.uv k))=>bareField M (X U)

theorem obstruction {x : Pane M} (h : x∉ clearStage Y N) : X x=0 := Set.indicator_of_notMem h _
theorem allowedField {x : Pane M} (h : x∈ clearStage Y N) : X x=
    Complex.exp (-((β * basicP Λ.K.top.clip x:ℝ):ℂ)) • changeM (m:=r) Λ.U x babyM:=
  Set.indicator_of_mem h _

lemma integrand_stencil (f : 𝛱) (w : Skye.Orbit M) :
    inner ℂ (Dial.mateK M) (acts ((imprint Y H N i k f) (drawn Q w)) (denZ R Λ.U Q w))=
      bareField M (acts (B f w.1) (X w.1)):= by
  rw [Y.whole]
  unfold bareField
  by_cases h : w.1∈clearStage Y N
  · have he: (Q) w=w.1:=funext fun j=> (Papal.roofage Y i N).lamp w.1 w.2 j (by simp [growFlags Y i k h])
    change inner ℂ (Dial.mateK M) (acts ((imprint Y H N i k f) (w.1,Q w)) (X w.1))=_
    rw [he]; rfl
  change inner ℂ _ (acts _ (X w.1))=inner ℂ _ (acts _ (X w.1)); rw [obstruction Y i k h,map_zero,map_zero]

lemma erase_tags (g : Pane M → ℂ) (p : Integrable (fun x:Skye.Orbit M=> g x.1) (city M)) :
    Integrable g (prior SU.group (More M)) ∧
      (∫ x:Skye.Orbit M,g x.1∂city M)=(∫ x,g x∂prior SU.group (More M)):= by
  refine ⟨?_,?_⟩
  · simpa using p.integral_prod_left
  change (∫ v : Pane M×_, g v.1∂ (prior SU.group (More M)).prod (depot M))=_
  rw [MeasureTheory.integral_fun_fst]; simp

theorem bare_vacuum (p:(Y₀).kick ≤ k) : Integrable V' (prior SU.group (More M)) ∧
    Z=(∫ x:Pane M,bareField M (X x)∂prior SU.group (More M)) ∧ Z≠0:= by
  let m(v:Skye.Orbit M):= (inner ℂ (Dial.mateK M) (denZ R Λ.U Q v))
  have hm : Integrable m (city M):=by
    let h:Pay Y N i k :=⟨p,le_rfl⟩
    have hx:= (funds Y N i k (f:=1) (AtSupport.oneM univ).env p (Nat.le_refl N)).1
    change Integrable (fun v : Skye.Orbit M=> inner ℂ (Dial.mateK M) (acts (1:FC (Single M)) (denZ R Λ.U Q v))) (city M) at hx
    simp only [act_one] at hx
    exact hx
  have ht : m= fun v=> bareField M (X v.1):=by funext v; unfold m bareField; rw [Y.whole]
  have he : Z ≠ 0 := (Y.each_level i k N p (le_refl _)).valid
  change Integrable _ _ ∧ (∫ v,m v∂city M)=_∧Z≠0
  rw [ht]; rw [ht] at hm
  obtain ⟨hp,hf⟩:=erase_tags Y i k V' hm
  exact ⟨hp,hf,he⟩

section stamping
variable (f : Altitude.Cloud (Dome (tent Y H)))

/-- Formula after earthing BOTH link fields. -/
abbrev inspectedBare (U : Pane M) := bareField M (acts ((bareStencil Y H i k f) U) ((bareCore Y i k) U))
local notation "F"=> inspectedBare Y H i k f

theorem pay_bare {s : ℕ} (p : f∈ boardedDB K s) (b : Tapestry.Pay Y s i k) :
    Integrable F (prior SU.group (More M)) ∧
      (∫ U:Pane M,bareField M (X U)∂prior SU.group (More M)) ≠ 0 ∧
      taking Y H i k f = (∫ U,F U∂prior SU.group (More M)) /
          (∫ U:Pane M,bareField M (X U)∂prior SU.group (More M)) := by
  have ht := taking_formula Y H N i k f (show Pay Y N i k from ⟨b.1,le_rfl⟩) (Altitude.climbs _ b.2 p)
  change Integrable (fun w:Skye.Orbit M=> inner ℂ _ (acts (imprint Y H N i k f (drawn Q w)) _)) _ ∧ _∧ taking _ _ _ _ _=_ at ht
  obtain ⟨hi,he,h⟩:= ht
  simp_rw [integrand_stencil] at hi
  change _=(∫ w: Skye.Orbit M,inner ℂ _ (acts (imprint Y H N i k f (drawn Q w)) _) ∂city M)/Z at h -- specify measure
  simp_rw [integrand_stencil] at h
  let H₀:=erase_tags Y i k F hi
  let v:= bare_vacuum Y i k b.1
  rw [← v.2.1]
  exact ⟨H₀.1,v.2.2,h.trans (congrArg (· / Z) H₀.2)⟩

/-- Thus the aperture keeps exactly one gauge field at the bare level. -/
theorem truly_neutral {s : ℕ} (p : Pay Y s i k) {U : Set RSpace} {wide : Bool} (h:f∈observatory Y H wide s U) :
    covariant (toMark (B f)):= by
  have a:=paid_coherence Y H i k N (show Pay Y N i k from ⟨p.1,le_rfl⟩) f h
    (Altitude.climbs _ p.2 (optic_short Y H wide s U (astro_loose Y H wide s U h)))
  intro g v
  exact a g (v.1,v.1)
end stamping

lemma local_first {n : Side} {T' : Finset Cover} {b : Bool} {F : Mark n}
    (h : AtSupport b (Satin.region T' n) F) : AtSupport b (Satin.region T' n) (toMark (Heat.both F)):=
  AtSupport.fromEval _ (Env.along (g:=fun x:Pane n=>(x,x)) h.env (by fun_prop))
        (fun U V t=> h.dep _ _ t t) (fun x=> h.allV (x,x))

/-- Support doesn't depend on which period we are taking. Keep even the
assignment of chiral signs via `AtSupport`. -/
theorem stencil_stays {s : ℕ} {f : Altitude.Cloud (Dome (tent Y H))} {wide : Bool} {U : Set RSpace}
    (t : f∈ ocular Y H wide s U) : ∃ S : Finset Cover, SupportedPhysically Λ l s S U ∧
      ∀ i k, Tapestry.Pay Y s i k → let n:=Y.uv k; let s':= volumeAround Λ l (n-s) S
                                    AtSupport false (Satin.region s' (Journey.side Y i n)) (toMark (bareStencil Y H i k f)) ∧
                                    SupportedPhysically Λ l n s' U := by
  obtain ⟨S,q,v⟩:= carried_support Y H t
  refine ⟨S,q,?_⟩
  intro i k p n W
  have he:s+(Y.uv k-s)= Y.uv k:= by have h:=p.2; omega
  have hp:=q.persists (Y.uv k-s); rw [he] at hp
  specialize v i k (Y.uv k-s); rw [he] at v
  exact ⟨local_first (v ⟨p.1,le_rfl⟩),hp⟩

lemma optic_grows {wide : Bool} {U : Set RSpace} {s t:ℕ}(h:s ≤ t) : ocular Y H wide s U ≤ ocular Y H wide t U:=
  admits Λ l _ wide _ _ _ _ (fun _ p=> ⟨p.1,le_trans p.2 h⟩) Set.Subset.rfl

lemma stencil_mult {A : ℝ} {x y : Altitude.Cloud (Dome (tent Y H))} {u v : Bool}
    {U V : Set RSpace} (sep : Disjoint U V) (hU : U⊆ cabin A) (hV : V⊆ cabin A)
    (room : 4*A+2 < (Journey.side Y i 0).val)
    {s : ℕ} (h : Tapestry.Pay Y s i k) (p : x∈ ocular Y H u s U) (t : y∈ ocular Y H v s V) :
    B (x*y)= (B x) * (B y):=by
  have hp : Pay Y N i k:= ⟨h.1,le_rfl⟩
  exact congrArg Heat.both (imprint_pair Y H i room sep hU hV hp (optic_grows Y H h.2 p) (optic_grows Y H h.2 t))
end YM.CF.Buffered.Afterglow.Tower.One
