import YM.SU5.Selected.Vacuum
/-!
# Linearity and gauge invariance survive compression on the `Parcel`-asking labels
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
namespace Spine
variable (P : Spine) (j : Axis)

variable (s : ℕ)
local notation "ω" => P.groundZero j
local notation "K" => P.calibration
local notation "κ" => P.compressed j s
local notation "Γ" f:max => P.preRead j (s,f)
@[simp] lemma preRead_val (f : ℕ × P.Test) :
    ((P.preRead j f).val) = P.compressed j f.1 f.2 := rfl
lemma equal_reads (x y : P.Ensemble j) (e : x.val ω=y.val ω) : x=y :=
  sub_eq_zero.mp (P.separating j (x-y) (by change x.val ω-y.val ω=0; exact sub_eq_zero.mpr e))
lemma preRead_unit : P.preRead j (s,1) = 1 := by
  apply P.equal_reads j; let U:=unity P.run P.large j 0 false s
  change κ (1:P.Test) ω=ω
  rw [show (1:P.Test)=P.voxTest j s U from rfl, P.seed]
  unfold piece U piZero
  rw [← vacua P.run P.large P.law P.history.circuit j 0 false (P.room j)]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (P.groundZero j)
lemma preRead_star (x : P.Test) : star (P.preRead j (s,x))=P.preRead j (s,P.reflectTest j x) :=
  Subtype.ext (P.reflected j s x)
lemma seed_pairing (x y : P.Vox j s) :
    inner ℂ (P.piece j s x) (P.piece j s y) = P.E s (mirror K j 0 x.val * y.val) := by
  have h:= stems P.run P.large P.law P.history.circuit j 0 false (P.room j) s x y
  rwa [area0] at h
lemma piece_linear (x y : P.Vox j s) (c : ℂ) : P.piece j s (c • x+y) =
    c • P.piece j s x + P.piece j s y := by
  let T:=arrows P.run P.large P.law P.history.circuit j 0 false (P.room j) s
  change T _=c • T x+T y
  rw [map_add,map_smul]

/-- Same discrete translations as used to generate the compressed operators. -/
def shiftsₗ (x : ℤ) : P.Test →ₗ[ℂ] P.Test where
  toFun f:= ⟨relocate K j x f.val, (marque ..).mpr (move_ok K j x ((marque ..).mp f.property))⟩
  map_add' _ _:=Subtype.ext (chime_plus ..)
  map_smul' _ _:=Subtype.ext (chime_scale ..)
def shifts (x : ℤ) : P.Test →ₐ[ℂ] P.Test := AlgHom.ofLinearMap (P.shiftsₗ j x)
    (Subtype.ext (relocate_unit K j x)) (fun _ _=>Subtype.ext (relocate_mul K j x))
lemma shifted (a : ℤ) (x : P.Test) : (P.shifts j a x).val = relocate K j a x.val := rfl
lemma shifts_sum (x : P.Test) (a b : ℤ) : P.shifts j a (P.shifts j b x)=P.shifts j (a+b) x:=
  Subtype.ext (relocate_sums K j a b ((marque K).mp x.property))
lemma shifts_zero (x : P.Test) : P.shifts j 0 x=x :=
  Subtype.ext (relocate_zero K j ((marque K).mp x.property))
lemma shifts_support (x : ℤ) (S : Finset Cover) {f : P.Test} {wide : Bool} (p : f∈bay K S wide) :
    P.shifts j x f∈ bay K (plow K j x S) wide := flow_port K j _ ((Tapestry.locates ..).mp p)

lemma shifted_read (x : ℤ) (f : P.Test) : P.preRead j (s,P.shifts j x f)= P.preRead j (s,f) := by
  let W (y : P.Test) := Veranda P.run P.large s j false (P.obs y)
  let T : W (P.shifts j x f) := Classical.choice (anyporch P.run P.large s j false (P.obs (P.shifts j x f)))
  let U : W f := ⟨T.rise+x,T.span,T.pos,T.fwd,T.yes.trans (congrArg (fun z : P.Test=> z.val) (P.shifts_sum j f T.rise x))⟩
  exact Subtype.ext ((onAny P.run P.large P.law s P.history P.projection.clipped j false (P.room j) T).trans
                     (onAny P.run P.large P.law s P.history P.projection.clipped j false (P.room j) U).symm)
lemma supports_future (S : Finset Cover) : ∀ᶠ x : ℕ in atTop, Tower.region j 0 (K).ℓ (plow K j x S) := by
  have hv (i : Cover) : ∀ᶠ x : ℕ in atTop, ((K).ℓ:ℤ) ≤ i j+ruler (K).B*x := by
    filter_upwards [eventually_ge_atTop ((K).ℓ+(i j).natAbs)] with x e
    have h : (x:ℤ) ≤ ruler (K).B*x := le_mul_of_one_le_left (by positivity) (ruler_gene (K).B)
    omega
  filter_upwards [(S.eventually_all).mpr (fun i _=> hv i)] with x p i h
  obtain ⟨y,u,rfl⟩:=plow_stays K j x S h
  rw [moves,if_pos rfl,zero_add]; exact p y u
def positiveVox (S : Finset Cover) (f : P.Test) (u : f∈bay K S true) (p : Tower.region j 0 (K).ℓ S) : P.Vox j s:=
  ⟨f.val,(purpose_ok ..).2 ⟨(show _ from ⟨S,(Tapestry.locates ..).mp u,by rw [area0]; exact p⟩),by simp⟩⟩

lemma preRead_linear (x y : P.Test) (c : ℂ) : P.preRead j (s,c • x+y) = c • P.preRead j (s,x)+P.preRead j (s,y):=by
  obtain ⟨S,h,g⟩:=coAwake K x y
  obtain ⟨p,t⟩:=(P.supports_future j S).exists
  let T:=P.shifts j (p:ℤ)
  let f:=P.positiveVox j s _ _ (P.shifts_support j p S h) t; let b:=P.positiveVox j s _ _ (P.shifts_support j p S g) t
  rw [← P.shifted_read j s p x, ← P.shifted_read j s p y, ← P.shifted_read j s p (c • x+y), map_add,map_smul]
  apply P.equal_reads
  change κ (c • T x+ T y) ω= c • (κ (T x) ω)+ κ (T y) ω
  rw [show (c • T x+ T y)= P.voxTest j s (c • f+b) from rfl]
  change κ _ ω= c • (κ (P.voxTest j s f) ω)+ κ (P.voxTest j s b) ω
  rw [P.seed,P.seed,P.seed,P.piece_linear,map_add,map_smul]
lemma preRead_zero : P.preRead j (s,0)=0 := by
  have h:= P.preRead_linear j s 0 0 1
  simpa using h
noncomputable def reading : P.Test →ₗ[ℂ] P.Ensemble j where
  toFun x := P.preRead j (s,x)
  map_add' x y:=by simpa using P.preRead_linear j s x y 1
  map_smul' c x:=by simpa [P.preRead_zero] using P.preRead_linear j s x 0 c

@[simp] lemma reading_unit : P.reading j s 1=1 := P.preRead_unit j s
lemma reading_star (f : P.Test) : star (P.reading j s f)= P.reading j s (P.reflectTest j f):=
  P.preRead_star j s f
lemma at_label (x : P.Test) : (P.reading j s x).val=κ x := rfl

-- The following conditioning result is for SINGLE-observable reads. This will
-- imply an **operator** test involving products of the compressed marks in Parcel.
-- No use of a gauged probability measure for the Euclidean labels.
local notation "ϱ" => pennant K
lemma local_recolor (S : Finset Cover) {x : P.Test} (h : x∈bay K S true) (rho tau : Cover→SU.E) (p : ∀ i∈S,rho i=tau i) :
    (ϱ rho) x=ϱ tau x := by
  refine appointed K S rho _ _ (fun n g e i=>?_) (pennantLocal K S tau h)
  exact pennantTrace K S tau h n g (fun i h=>(e i h).trans (p i h)) i
lemma survives_disjoint (S T : Finset Cover) (d : Disjoint T S) {f g x : Family K}
    (a : InTest K true S false f) (b : InTest K true S false g) (u : InTest K true T false x)
    (t : Cover→SU.E) (v : Circular S t f g) : P.E s (x*f)=P.E s (x*g):=by
  let z i := if i∈S then t i else 1
  let X : P.Test:= ⟨x,aux_test u⟩
  have ht : X∈bay K T true:= u
  have hx : ϱ z X=X:= (P.local_recolor T ht z 1 (fun i h=> if_neg (Finset.disjoint_left.mp d h))).trans (pennantId ..)
  have hw : Circular T z x x := by simpa only [hx] using (pennantTrace K T z ht)
  have he : Circular S z f g:= fun n u e=> v n u (fun i h=> (e i h).trans (if_pos h))
  let pT:= Finset.subset_union_left (s₁:=T) (s₂:=S)
  let pS : S ⊆ T∪S:= Finset.subset_union_right
  refine (Papal.ledgerRule P.run P.large P.law (T∪S) s).gauge z _ _ ((u.mono pT).mul (a.mono pS))
    ((u.mono pT).mul (b.mono pS)) ((largerGauge pT hw).mul z (T∪S) (largerGauge pS he))
lemma erases_at_seam (a b : P.Vox j s) (S : Finset Cover) (h : InTest K true S false a.val)
    (p : InTest K true S false b.val) (v : Tower.region j 0 (K).ℓ S)
    (R : Cover → SU.E) (u : Circular S R a.val b.val) : P.piece j s a = P.piece j s b := by
  -- Equality already measured by the single-rung Gram norm; avoid any gauge generator at the OS seam
  let T:= reflectedBox j 0 S
  have ht := mirror_detached P.par P.width v v
  have hz : Disjoint T S:=Finset.disjoint_left.mpr (fun i h t=> ht i h i t (by rw [sub_self]; exact Lattice.center_box _))
  let a':= P.piece j s a; let b':=P.piece j s b
  have h₁ : inner ℂ a' a'=inner ℂ a' b':=by
    unfold a' b'; rw [P.seed_pairing,P.seed_pairing]
    exact P.survives_disjoint s S T hz h p (axial K j 0 h) R u
  have h₂ : inner ℂ b' a'=inner ℂ b' b':=by
    unfold a' b'; rw [P.seed_pairing,P.seed_pairing]; exact P.survives_disjoint s S T hz h p (axial K j 0 p) R u
  apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  change inner ℂ (a'-b') (a'-b')=0; rw [inner_sub_right,inner_sub_left,inner_sub_left,h₁,h₂,sub_self]

lemma erases_future (a b : P.Vox j s) (S : Finset Cover) (h : InTest K true S false a.val)
    (p : InTest K true S false b.val) (v : Tower.region j 0 (K).ℓ S)
    (R : Cover → SU.E) (u : Circular S R a.val b.val) : P.reading j s (P.voxTest j s a)=P.reading j s (P.voxTest j s b) := by
  apply P.equal_reads
  rw [at_label,at_label,P.seed,P.seed,P.erases_at_seam j s a b S h p v R u]

lemma gauges_of_mirror (a : ℤ) (r : GVertex) : reflectGauge j a (reflectGauge j a r) = r := by
  funext i; unfold reflectGauge; simp only [comp_apply]; congr 1; ext v; rw [fling_move,fling_move]; split <;> ring
lemma spins_shift (t : ℤ) (r : GVertex) (x : P.Test) : ∃ u : GVertex, ϱ u (P.shifts j t x) = P.shifts j t (ϱ r x) := by
  let a:=gaugeT K t; refine ⟨reflectGauge j a (reflectGauge j 0 r),?_⟩
  change ϱ _ (aureole K j a (aureole K j 0 x)) = aureole K j a (aureole K j 0 (ϱ r x))
  rw [pennantReflect,gauges_of_mirror,pennantReflect,gauges_of_mirror]
/-- Cap remembers the gauge-invariance of E at EACH observing rung. -/
lemma reading_gauge (r : GVertex) (f : P.Test) : P.reading j s (pennant K r f)=P.reading j s f := by
  obtain ⟨S,h⟩:=findsBay K f; obtain ⟨v,u⟩:=(P.supports_future j S).exists
  obtain ⟨m,e⟩:= P.spins_shift j v r f
  suffices he : P.reading j s (P.shifts j v (ϱ r f))= P.reading j s (P.shifts j v f) by
    change Γ (P.shifts j (v:ℤ) (pennant K r f))= Γ (P.shifts j (v:ℤ) f) at he
    change Γ (pennant K r f)= Γ f
    rwa [P.shifted_read,P.shifted_read] at he
  rw [←e]; symm; let x:= P.shifts j (v:ℤ) f; have hx:= P.shifts_support j v S h
  let T:=plow K j v S
  let a:=P.positiveVox j s T x hx u; let b:=P.positiveVox j s T _ (pennantLocal K T m hx) u
  exact P.erases_future j s a b T ((Tapestry.locates ..).mp hx)
    ((Tapestry.locates ..).mp (pennantLocal K T m hx)) u m (pennantTrace K T m hx)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.preRead_unit
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reading
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reading_gauge
