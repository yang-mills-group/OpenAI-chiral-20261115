import SU5SatinProgressNovember7B
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
-- §LP shift Ward (one real oriented edge and disjoint patches)
namespace PureForce
variable (N : Side)
local notation "μ" => prior SU.group (More N)

-- more memory needed? set from header.
/-- Product Haar left and right (so also covers negative-oriented move, multiplying
at the right endpoint) and untouched extra Ids. -/
abbrev gaugeLink (N : Side) := Edge (Site (More N))
variable {N}

def switch (l r : gaugeLink N → SU.E) : Pane N → Pane N := fun U i=> l i * U i * r i

def switchOrbit (l r : gaugeLink N → SU.E) : Orbit N → Orbit N := Prod.map (switch l r) id

lemma switch_pres (l r : gaugeLink N → SU.E) : MeasurePreserving (switch l r) (μ) (μ) := by
  apply measurePreserving_pi (f:=fun (i : gaugeLink N) u => l i * u * r i) (fun _=> SU.group.probHaar) (fun _=>SU.group.probHaar)
  exact fun i=>SU.group.preserve_two_sided (l i) (r i)
lemma switch_emb (l r : gaugeLink N → SU.E) : MeasurableEmbedding (switch l r) :=
  ((Homeomorph.mulLeft (l : Pane N)).trans (Homeomorph.mulRight (r : Pane N))).toMeasurableEquiv.measurableEmbedding
lemma switchOrbit_pres (l r : gaugeLink N → SU.E) :
    MeasurePreserving (switchOrbit l r) (Scree.city N) (Scree.city N) :=
  (switch_pres l r).prod (MeasurePreserving.id _)
lemma switchOrbit_emb (l r : gaugeLink N → SU.E) : MeasurableEmbedding (switchOrbit l r) :=
  (switch_emb l r).prodMap MeasurableEmbedding.id

-- Positive oriented e. For many moves use disjoint anchors.
def atomAt (e : gaugeLink N) (a : SU.E) : gaugeLink N → SU.E := Pi.mulSingle e a
lemma atom_off {i e : gaugeLink N} (a : SU.E) (h : i ≠ e) : atomAt e a i=1 := by
  unfold atomAt
  exact Pi.mulSingle_eq_of_ne (M:=fun _=>SU.E) h a

variable {Q : Type*}
/-- All anchored links of a menu, transformed simultaneously by chosen SU
elements. L & R orientation parameters; may choose R=1 e.g. for positive Lie step.
Indices in `qs` pairwise distinct. -/
def offerSide (qs : List Q) (E : Q → gaugeLink N) (a : Q → SU.E) : gaugeLink N → SU.E :=
  fun i=> (qs.map fun q=> atomAt (E q) (a q) i).prod
def offer (qs : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) : Pane N → Pane N :=
  switch (offerSide qs E a) (offerSide qs E b)
def oneOffer (e : gaugeLink N) (a b : SU.E) : Pane N → Pane N := switch (atomAt e a) (atomAt e b)
def offerOrbit (qs : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) : Orbit N → Orbit N :=
  switchOrbit (offerSide qs E a) (offerSide qs E b)
lemma offer_pres (qs : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) :
    MeasurePreserving (offerOrbit qs E a b) (Scree.city N) (Scree.city N) := switchOrbit_pres _ _
lemma offer_emb (qs : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) :
    MeasurableEmbedding (offerOrbit qs E a b) := switchOrbit_emb _ _

variable (S : Q → Finset (Skye.Seat N))
lemma offerSide_far (qs : List Q) (E : Q → gaugeLink N) (a : Q → SU.E) {i : gaugeLink N}
    (h : ∀ j ∈ qs,i ≠ E j) : offerSide qs E a i=1 := by
  apply List.prod_eq_one
  rintro x hx
  obtain ⟨q,k,rfl⟩ := List.mem_map.mp hx
  exact atom_off _ (h _ k)
lemma offerSide_here (qs : List Q) (E : Q → gaugeLink N) (a : Q → SU.E) {q:Q}
    (hq:q∈qs) (n:qs.Nodup) {i:gaugeLink N}(h:∀ j∈qs,j ≠ q → i≠E j) :
    offerSide qs E a i= atomAt (E q) (a q) i := by
  induction qs with
  | nil=> simp at hq
  | cons p qs ih=>
    rw [List.nodup_cons] at n
    rcases List.mem_cons.mp hq with v|v
    · subst p
      change atomAt _ _ _*offerSide qs E a i=_
      rw [offerSide_far qs E a (fun j hj=> h j (List.mem_cons_of_mem _ hj) (fun hl=> n.1 (hl ▸ hj))),mul_one]
    · change atomAt _ _ i*offerSide qs E a i=_
      rw [atom_off _ (h _ List.mem_cons_self (fun hl=> n.1 (hl.symm ▸ v))), one_mul, ih v n.2 (fun j hj=>h j (List.mem_cons_of_mem _ hj))]

-- only need one endpoint inclusion. Agrees in both panes not available to shifts in general.
lemma anchor_avoid (m : Pairwise (Disjoint on S)) {q j:Q}(h:j≠q) {e i:gaugeLink N}
    (v:i.1∈S q) (w:e.1∈S j) : i≠ e := by
  rintro rfl
  exact Finset.disjoint_left.mp (m h) w v
lemma offer_undriven (qs:List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (U:Pane N)
    (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S)) {q:Q}(h:q∉qs) :
    Agrees (S q) (offer qs E a b U) U := by
  intro i v _
  have he(j)(hj:j∈qs):i≠E j:= anchor_avoid S m (fun y:j=q=>h (y ▸ hj)) v (t j)
  unfold offer switch; rw [offerSide_far _ _ _ he,offerSide_far _ _ _ he,one_mul,mul_one]
lemma offer_driven (qs:List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (U:Pane N)
    (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S)) {q:Q}(h:q∈qs)(n:qs.Nodup) :
    Agrees (S q) (offer qs E a b U) (oneOffer (E q) (a q) (b q) U) := by
  intro i v _
  have he(j)(_ : j∈qs)(y:j≠q):i≠E j:= anchor_avoid S m y v (t j)
  unfold offer oneOffer switch; rw [offerSide_here _ _ _ h n he,offerSide_here _ _ _ h n he]
private lemma envProd {X T M : Type*} [MeasurableSpace X] [NormedRing M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (f : T → X → M)
    (h:∀ t,Envelope (f t)) (l:List T):
    Envelope fun x=> (l.map fun t=> f t x).prod := by
  induction l with
  | nil => exact ⟨measurable_const,‖(1:M)‖,fun x=>le_refl _⟩
  | cons y l ih=>
    let g(x:X):=(l.map fun t=> f t x).prod
    obtain ⟨hx,c,hc⟩:= h y; obtain ⟨hy,d,hd⟩:=ih
    change Measurable g at hy
    exact ⟨hx.mul hy,c*d,fun x=> (norm_mul_le (f y x) (g x)).trans
      (mul_le_mul (hc x) (hd x) (norm_nonneg _) ((norm_nonneg _).trans (hc x)))⟩

/-- Kept operands. Ordered, no commuting across overlapping footprints.
Patch covariance/eligible target theorem separate. -/
def keptMarks (keeps : List Q) (F : Q → Evaluation N) : Evaluation N := fun U=> (keeps.map fun q=> F q U).prod

/-- Exposure coefficient, computed at EACH INDIVIDUALLY shifted argument. In
LP can take this to include `-gamma` with cutoff on that patch at U_z. -/
def prize (qs : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (γ: Q → Pane N → ℂ) (U :Pane N) :ℂ :=
  (qs.map fun q=> γ q (oneOffer (E q) (a q) (b q) U)).prod
/-- Same exposure computed after pulling U by all the shifts. -/
def together (qs : List Q) (γ : Q → Pane N → ℂ) (U :Pane N):ℂ:=(qs.map fun q=> γ q U).prod

/-- Price of one shifted checker choice (density ψ always on that same Orbit,
so in particular computes denZ and hence new Loom value on *new* Orbit, for actual application). -/
def changed (qs keep : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (γ:Q→Pane N→ℂ)
    (F:Q→Evaluation N) (ψ: Orbit N → Scree.Phys N) (x : Orbit N) : ℂ:=
  prize qs E a b γ x.1 *
    inner ℂ (Dial.mateK N) (acts (keptMarks keep F x.1) (ψ (offerOrbit qs E a b x)))

def startPrice (keep : List Q)(F:Q→Evaluation N)(ψ:Orbit N→ Scree.Phys N)(x:Orbit N):ℂ:=
  inner ℂ (Dial.mateK N) (acts (keptMarks keep F x.1) (ψ x))

def PatchOnly {α : Type*} (C:Finset (Skye.Seat N))(f:Pane N → α):Prop:=
  ∀ U V, Agrees C U V → f U = f V

private lemma pull_all (qs keep : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (γ:Q→Pane N→ℂ)
    (F:Q→Evaluation N) (ψ: Orbit N → Scree.Phys N) (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))
    (d:∀ q ∈ keep,q∉qs) (n:qs.Nodup) (h:∀ q,PatchOnly (S q) (F q)) (v:∀ q,PatchOnly (S q) (γ q)) :
    changed qs keep E a b γ F ψ = (fun x:Orbit N=> together qs γ x.1 * startPrice keep F ψ x) ∘ offerOrbit qs E a b := by
  funext x; unfold changed startPrice Function.comp
  change _ = together qs γ (offer qs E a b x.1) * ⟪_,acts (keptMarks keep F (offer qs E a b x.1)) (ψ _)⟫_ℂ
  congr 1
  · exact congrArg List.prod <| List.map_congr_left fun q hq=> (v q _ _ (offer_driven S qs E a b _ t m hq n)).symm
  rw [show keptMarks keep F (offer qs E a b x.1) = keptMarks keep F x.1 from ?_]
  exact congrArg List.prod <| List.map_congr_left fun q hq=> h q _ _ (offer_undriven S qs E a b _ t m (d q hq))

lemma pay_pull (qs keep : List Q) (E : Q → gaugeLink N) (a b : Q → SU.E) (γ:Q→Pane N→ℂ)
    (F:Q→Evaluation N) (ψ: Orbit N → Scree.Phys N) (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))
    (d:∀ q∈keep,q∉qs) (n:qs.Nodup) (h:∀ q,PatchOnly (S q) (F q)) (v:∀ q,PatchOnly (S q) (γ q))
    (hv:∀ q,Envelope (γ q)) (p:Integrable (startPrice keep F ψ) (Scree.city N)) :
    Integrable (changed qs keep E a b γ F ψ) (Scree.city N) ∧
    ∫ x,changed qs keep E a b γ F ψ x∂(Scree.city N) =∫ x,together qs γ x.1 * startPrice keep F ψ x∂(Scree.city N):= by -- parentheses
  have ht:= pull_all S qs keep E a b γ F ψ t m d n h v
  rw [ht]
  refine ⟨(MeasurePreserving.integrable_comp_emb (offer_pres ..) (offer_emb ..)).mpr ?_, MeasurePreserving.integral_comp (offer_pres qs E a b) (offer_emb ..) (fun x:Orbit N=> together qs γ x.1 * startPrice keep F ψ x)⟩
  have hu :Envelope (fun x:Orbit N=> together qs γ x.1):= Env.along (envProd γ hv qs) measurable_fst
  obtain ⟨l,c,w⟩:=hu
  exact p.bdd_mul l.aestronglyMeasurable (ae_of_all _ w)

set_option maxHeartbeats 60000
variable {J:Type*} [Fintype Q] [DecidableEq Q] [Fintype J] -- fixed angular radial option indices, sum zero

def optionΓ (w : Q → J → ℂ) (X : Q → Pane N → ℂ) (u:Q→J) : Q→Pane N→ℂ:= fun q x=>w q (u q)*X q x

def assayShift (qs keep:List Q)(E:Q → gaugeLink N)(L R:Q→J→SU.E)
    (w:Q→J→ℂ)(X:Q→Pane N→ℂ)(F:Q→Evaluation N)(ψ:Orbit N→Scree.Phys N)(u:Q→J):Orbit N→ℂ:=
  changed qs keep E (fun q=>L q (u q)) (fun q=>R q (u q)) (optionΓ w X u) F ψ

omit [Fintype Q] [DecidableEq Q] [Fintype J] in
private lemma envOption (w : Q → J → ℂ)(X : Q → Pane N → ℂ)(h:∀ q,Envelope (X q))(u:Q→J)(q:Q):
    Envelope (optionΓ w X u q):= by
  obtain ⟨v,C,t⟩:=h q
  exact ⟨measurable_const.mul v,‖w q (u q)‖*C,fun x=> (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (t x) (norm_nonneg _))⟩

private lemma cancel_weights (w : Q → J → ℂ)(qs : List Q)(q:Q)(e:q∈qs)(n:qs.Nodup)(h:∀ q,∑ i,w q i=0) :
    ∑ u:Q→J, (qs.map fun q=> w q (u q)).prod=0:= by
  let g(q:Q)(v:J):ℂ:= if q∈qs then w q v else 1
  simp_rw [←List.prod_toFinset _ n]
  have he(u:Q→J): (∏ i∈qs.toFinset,w i (u i)) = ∏ i,g i (u i):= by
    refine Eq.trans (Finset.prod_congr rfl ?_) (Finset.prod_subset (Finset.subset_univ _) ?_)
    · intro i t; simp [g, List.mem_toFinset.mp t]
    intro i _ v; simp [g, show i∉qs from fun h=> v (List.mem_toFinset.mpr h)]
  simp_rw [he, ←Fintype.prod_sum g]
  exact Finset.prod_eq_zero (i:=q) (Finset.mem_univ _) (by change ∑ i,g q i=0; simp [g,e,h q])

/-- §LP p.100, for each fixed choice of link and direction (including if chosen
in a moved frame) per omitted root. Includes integrability and the signed equality
on that same Orbit space. ψ integrability required only against the unshifted kept
operand (even when masks/γ supported off the typical set).
-/
theorem cancelOffer (qs keep:List Q)(E:Q → gaugeLink N)(L R:Q→J→SU.E)
    (w:Q→J→ℂ)(X:Q→Pane N→ℂ)(F:Q→Evaluation N)(ψ:Orbit N→Scree.Phys N)
    (q:Q)(e:q∈qs)(n:qs.Nodup)(hy:∀ q,∑ i,w q i=0)
    (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))(d:∀ p∈keep,p∉qs)
    (h:∀ q,PatchOnly (S q) (F q)) (v:∀ q,PatchOnly (S q) (X q) ∧ Envelope (X q))
    (p:Integrable (startPrice keep F ψ) (Scree.city N)) :
    (∀ u:Q→J,Integrable (assayShift qs keep E L R w X F ψ u) (Scree.city N)) ∧
    ∑ u:Q→J, (∫ x, assayShift qs keep E L R w X F ψ u x∂(Scree.city N))=0 := by
  let A(u:Q→J):= (qs.map fun q=> w q (u q)).prod
  let W(x:Orbit N):= together qs X x.1 * startPrice keep F ψ x
  have he(u:Q→J): Integrable (assayShift qs keep E L R w X F ψ u) (Scree.city N) ∧
      ∫ x, assayShift qs keep E L R w X F ψ u x∂(Scree.city N) = A u* ∫ x,W x∂(Scree.city N) := by
    obtain ⟨B,hb⟩:= pay_pull S qs keep E (fun j=>L j (u j)) (fun j=>R j (u j)) (optionΓ w X u) F ψ t m d n h
      (fun j C D he=> congrArg (fun x=>w j (u j)*x) ((v j).1 _ _ he)) (envOption w X (fun i=>(v i).2) u) p
    refine ⟨B,hb.trans ?_⟩
    rw [← integral_const_mul]; apply integral_congr_ae; refine ae_of_all _ fun x=>?_ ; dsimp [W,together,optionΓ,A]; rw [List.prod_map_mul, mul_assoc]
  refine ⟨fun u=>(he u).1,?_⟩
  simp_rw [(he _).2, ←Finset.sum_mul, show ∑ u,A u=0 from cancel_weights w qs q e n hy,zero_mul]
-- For Preserving F only need AtSupport on smaller than patch, toMark.
omit [Fintype Q] [DecidableEq Q] in
lemma atSupport_supplies {p : Q} {F : Evaluation N} (h : AtSupport false (S p) (toMark F)) :
    PatchOnly (S p) F ∧ Envelope F := by
  refine ⟨fun U V t=>h.dep (U,U) (V,V) t t,Env.along h.env (measurable_id.prodMk measurable_id)⟩

-- Exact integrated price at *interior* s. Remove offset (same amount on both);
-- preserve the normalized ratio. Needs funds (from kick and s≤v, actual Π/R law).
variable (P : Spine)(i k s:ℕ)(u : Tapestry.Pay P.run s i k)
set_option quotPrecheck false
local notation "nA" => side P.run i s
local notation "gA" => ((P.run.voyage i).X (P.run.uv k)).gram s
local notation "LA" => (P.run.voyage i).CapeT s
local notation "μA" => Scree.city (side P.run i s)

abbrev Psi (x:Orbit (side P.run i s)) := Complex.exp (-(gA).v) • denZ (gA) P.par.U (LA) x
abbrev denom := Complex.exp (-(gA).v) * partitionZ (gA) P.par.U (LA)
include u
omit [Fintype Q] [DecidableEq Q] in
lemma actualBill (qs:List Q)(F:Q→Evaluation (side P.run i s))(h:∀ q,Envelope (F q)) :
    Integrable (startPrice qs F (Psi P i k s)) (μA) ∧ denom P i k s ≠ 0 ∧
    Journey.compass P.run i k s (toMark (keptMarks qs F))=
    (∫ x,startPrice qs F (Psi P i k s) x∂(μA))/denom P i k s := by
  have hl:Envelope (toMark (keptMarks qs F)):= Env.along (envProd F h qs) measurable_fst
  obtain ⟨a,v,w⟩:= Tapestry.funds (Y:=P.run) (s:=s) (i:=i) (k:=k) hl u.1 u.2
  let f := fun x : Orbit (side P.run i s) => inner ℂ (Dial.mateK (nA)) (acts (keptMarks qs F x.1) (denZ (gA) P.par.U (LA) x))
  let d:=Complex.exp (-(gA).v); have ht:d≠0:=Complex.exp_ne_zero _
  have he: startPrice qs F (Psi P i k s) = fun x=>d * f x:=by
    funext x; exact Eq.trans (congrArg (inner ℂ _) (map_smul _ _ _)) (inner_smul_right ..)
  rw [he,integral_const_mul]
  refine ⟨Integrable.const_mul (show Integrable f _ from a) d, mul_ne_zero ht v,?_⟩
  exact w.trans (by change (∫ x,f x∂_) / _ = (d * ∫ x,f x∂_) / (d * _); rw [mul_div_mul_left _ _ ht])

/-- On P's actual R_s, full Loom: the nonempty shift summand in §LP2 checker
has value zero. Also with L.2 compensation, same physical price for the original
unshifted collection. P and Y-law *arbitrary* Spin appointments with Pay, no
attachment from a separate echo/spectator trajectory. -/
theorem actualCancelOffer (layout keep qs:List Q)(E:Q → gaugeLink (nA))(L R:Q→J→SU.E)
    (w:Q→J→ℂ)(X:Q→Pane (nA)→ℂ)(F:Q→Evaluation (nA))(C:Q→Finset (Skye.Seat (nA)))
    (q:Q)(e:q∈qs)(hn:qs.Nodup)(hy:∀ q,∑ i,w q i=0)
    (t:∀ j,(E j).1∈ C j) (m: Pairwise (Disjoint on C))(d:∀ p∈keep,p∉qs)
    (h:∀ q,AtSupport false (C q) (toMark (F q))) (v:∀ q,PatchOnly (C q) (X q) ∧ Envelope (X q)) :
    let ψ:=Psi P i k s
    (∀ y:Q→J, Integrable (assayShift qs keep E L R w X F ψ y) (μA)) ∧
    Integrable (startPrice layout F ψ) (μA) ∧ denom P i k s ≠ 0 ∧
    Journey.compass P.run i k s (toMark (keptMarks layout F)) =
      ((∫ x,startPrice layout F ψ x∂(μA)) + ∫ x,∑ y:Q→J,assayShift qs keep E L R w X F ψ y x∂(μA)) / denom P i k s := by
  intro ψ
  have he(q):Envelope (F q):= (atSupport_supplies C (h q)).2
  obtain ⟨A,b⟩ := cancelOffer C qs keep E L R w X F ψ q e hn hy t m d (fun q=> (atSupport_supplies C (h q)).1) v
    (actualBill P i k s u keep F he).1
  obtain ⟨ht,hk,hp⟩:= actualBill P i k s u layout F he
  refine ⟨A,ht,hk,hp.trans ?_⟩
  rw [integral_finsetSum _ (fun l _=>A l),b,add_zero]
omit u
variable {Θ:Type*} [MeasurableSpace Θ] (ν: Measure Θ) [IsProbabilityMeasure ν]
    (qs keep : List Q) (E : Q → gaugeLink N) (a b : Θ → Q → SU.E)

set_option linter.unusedSectionVars false in
private lemma offerSideM (ha:∀ j,Measurable fun θ=> a θ j)(e:gaugeLink N) :
    Measurable fun θ=> offerSide qs E (a θ) e := by
  induction qs with
  | nil=> exact measurable_const
  | cons j qs h=>
    change Measurable ((fun θ=> atomAt (E j) (a θ j) e)*(fun θ=>offerSide qs E (a θ) e))
    refine Measurable.mul ?_ h
    by_cases t:e=E j
    · subst e; simp only [atomAt, Pi.mulSingle_eq_same]; exact ha _
    simp_rw [atom_off _ t]; exact measurable_const

private lemma skew_meas (ha:∀ j,Measurable fun θ=>a θ j)(hb:∀ j,Measurable fun θ=>b θ j) :
    Measurable fun x:Θ×Orbit N=>offerOrbit qs E (a x.1) (b x.1) x.2 := by
  let A(x:Θ×Orbit N):Pane N:= offer qs E (a x.1) (b x.1) x.2.1
  refine Measurable.prodMk (show Measurable A from ?_) (measurable_snd.comp measurable_snd)
  apply measurable_pi_lambda
  intro i
  change Measurable ((fun x:Θ×Orbit N=> offerSide qs E (a x.1) i * x.2.1 i) * fun x=> offerSide qs E (b x.1) i)
  exact (( (offerSideM qs E a ha i).comp measurable_fst).mul ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).mul ((offerSideM qs E b hb i).comp measurable_fst)

/-- So one can charge and interchange the angular (independent color-sphere
product etc.) integrals in this proof. We get away with only L¹ on the
kept bra reading with actual Ψ on City (no *uniform* or separately purchased
phase/measurability hypothesis on Ψ with arbitrary Pane parameters). -/
theorem inside_shift (γ: Q→ Θ× Pane N → ℂ) (F:Q→Evaluation N) (ψ:Orbit N→ Scree.Phys N)(t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))(d:∀ q∈keep,q∉qs)(n:qs.Nodup)
    (h:∀ q,PatchOnly (S q) (F q)) (v:∀ q θ,PatchOnly (S q) (fun U=>γ q (θ,U)))
    (hv:∀ q,Envelope (γ q))(ha:∀ j,Measurable fun θ=>a θ j)(hb:∀ j,Measurable fun θ=>b θ j)
    (p: Integrable (startPrice keep F ψ) (Scree.city N)) :
    Integrable (fun x:Θ×Orbit N=>changed qs keep E (a x.1) (b x.1) (fun q U=>γ q (x.1,U)) F ψ x.2) (ν.prod (Scree.city N)) := by
  let f (x:Θ×Orbit N) := together qs (fun q U=>γ q (x.1,U)) x.2.1 * startPrice keep F ψ x.2
  let g (x:Θ×Orbit N): Θ×Orbit N:=(x.1,offerOrbit qs E (a x.1) (b x.1) x.2)
  have hg : MeasurePreserving g (ν.prod (Scree.city N)) (ν.prod (Scree.city N)):= MeasurePreserving.skew_product (g:=fun θ U=>offerOrbit qs E (a θ) (b θ) U) (MeasurePreserving.id ν) (skew_meas qs E a b ha hb) (ae_of_all _ fun θ=>(offer_pres ..).map_eq)
  have he:(fun x:Θ×Orbit N=>changed qs keep E (a x.1) (b x.1) (fun q U=>γ q (x.1,U)) F ψ x.2)= f ∘ g := by
    funext x; rw [pull_all S qs keep E _ _ _ _ ψ t m d n h (fun j=>v j _)]; rfl
  rw [he]; apply hg.integrable_comp_of_integrable
  let wl (q : Q) (x:Θ×Orbit N) := γ q (x.1,x.2.1)
  have hl(q:Q) : Envelope (wl q):= Env.along (hv q) (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  obtain ⟨v,c,hc⟩:=envProd wl hl qs
  have hs: Integrable (startPrice keep F ψ ∘ Prod.snd) (ν.prod (Scree.city N)):= measurePreserving_snd.integrable_comp_of_integrable p
  exact hs.bdd_mul (v.aestronglyMeasurable) (ae_of_all _ hc)
-- Take all Ward shift option prices with ν integrated in each summand first.
variable (L R:Θ→Q→J→SU.E)
lemma angular_cancel (w:Q→J→ℂ)(X:Q→Θ × Pane N → ℂ)(F:Q→Evaluation N)(ψ:Orbit N→Scree.Phys N)
    (q:Q)(e:q∈qs)(hn:qs.Nodup)(hy:∀ q,∑ i,w q i=0)
    (t:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))(d:∀ p∈keep,p∉qs)(h:∀ q,PatchOnly (S q) (F q))
    (v:∀ q θ,PatchOnly (S q) (fun U=>X q (θ,U))) (hv:∀ q,Envelope (X q))
    (ha:∀ q j,Measurable fun θ=>L θ q j)(hb:∀ q j,Measurable fun θ=>R θ q j)
    (p: Integrable (startPrice keep F ψ) (Scree.city N)) :
    let Z:= fun y:Q→J=> Function.uncurry (fun θ=> assayShift qs keep E (L θ) (R θ) w (fun j U=>X j (θ,U)) F ψ y)
    (∀ y,Integrable (Z y) (ν.prod (Scree.city N))) ∧
    (∫ x, (∑ y:Q→J, ∫ θ,Z y (θ,x)∂ν) ∂(Scree.city N))=0 := by
  intro Z
  have hh(y):Integrable (Z y) (ν.prod (Scree.city N)):=by
    let γ(q)(x:Θ × Pane N):= w q (y q)* X q x
    apply inside_shift S ν qs keep E (fun θ q=>L θ q (y q)) (fun θ q=>R θ q (y q)) γ F ψ t m d hn h _ _ (fun q=>ha q _) (fun q=>hb q _) p
    · intro j θ U V h
      exact congrArg (fun x=> w j (y j)*x) (v j θ _ _ h)
    intro j; obtain ⟨l,c,d⟩:=hv j
    exact ⟨measurable_const.mul l, ‖w j (y j)‖*c,fun U=> (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (d _) (norm_nonneg _))⟩
  refine ⟨hh,?_⟩
  rw [integral_finsetSum _ (fun l _=> (hh l).integral_prod_right)]
  have he(θ:Θ):∑ y:Q→J, ∫ x,Z y (θ,x) ∂ (Scree.city N)=0:=
    cancelOffer S qs keep E (L θ) (R θ) w (fun j U=>X j (θ,U)) F ψ q e hn hy t m d h
      (fun j=>⟨v j θ,Env.along (hv j) (measurable_const.prodMk measurable_id)⟩) p|>.2
  simp_rw [show ∀ l, (∫ x, ∫ θ,Z l (θ,x)∂ν ∂(Scree.city N))=(∫ θ, (∫ x,Z l (θ,x)∂(Scree.city N)) ∂ν) from
    fun l=> Eq.symm (integral_integral_swap (f:=fun θ x=> Z l (θ,x)) (hh l)), ← integral_finsetSum _ (fun l _=> (hh l).integral_prod_left), he, integral_zero]

end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
