import YM.SU5.MacroSix.Exposure

/-! # A single normalized sign test on gauge & chiral-matter together, or its raw product.

`Prices`, `Split` & `PureWard`: no class assumptions about volumes or signals,
not even positivity: read separately in each factor but pay the same normalization.
Variant arbitrary two normal marginals, with different candidate law allowed from
rung to rung. The actual marginal prices will be used as (non-empty) example. On
the raw heights of mixed mark consultations, using these **same stencils**, split
has a simple expression and is support-independent.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
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

/-- Full wide even `Dome`; factorization is at the height of this
reading. No claim of positivity, consistency across heights, or normalization
by a probability/determinantal nonnegative weight. -/
abbrev Prices (K : Calibration) := Dome K →ₗ[ℂ] ℂ
variable {K : Calibration} {S : Finset Cover} {f g : Dome K}

structure Split (M : Prices K) : Prop where
  unital : M 1=1
  pixel : ∀ a∈Gate K, ∀ b∈Mantle K, M (a*b)=M a*M b
section construction
variable (A B : Prices K)

-- Use convenient presentation with linear extensions (one can have arbitrary separate
-- assignments on those actual raw subalgebras; proofs below verify independence of those outside choices).
def provision (f : Dome K) (W : PairsC) := B (freezePair K W f)
lemma provision_envelope (a : f∈ bay K S true) : Coeff true S (provision B f) := by
  obtain ⟨x,rfl⟩ := accolade K S f a
  let v (i : Evens S) := B (lineWord S K i)
  rw [show provision B (badge K S x)= ∑ i, v i • daub S (x i) from ?_]
  · exact admits_iterate univ (fun i ↦ v i • daub S (x i)) (fun i _ ↦ admits_scale _ (authentic S _))
  funext W; unfold provision
  rw [freezePair_expansion,map_sum, Finset.sum_apply]; exact sum_congr rfl (fun i _ ↦
    (map_smul B _ _).trans (mul_comm _ _))

def ticketProvision (f : Dome K) : Dome K:= markInk K (provision_envelope B (precinct_spec K f))
lemma ticket_seed (x : Dome K) : ticketProvision B x ∈ Gate K := ink_mem K _
lemma ticket_spec (h : f∈ bay K S true) : ticketProvision B f = markInk K (provision_envelope B h) := rfl

lemma ticket_factor {q : PairsC→ℂ}(h : Coeff true S q) (p : g∈ Mantle K) :
    ticketProvision B (markInk K h*g)= B g • markInk K h := by
  have he (W : PairsC) : provision B (markInk K h*g) W=B g*q W:=by
    unfold provision; rw [map_mul, freezePair_scalar,freezePair_id K W p,Algebra.smul_mul_assoc,one_mul,map_smul,smul_eq_mul,mul_comm]
  apply Subtype.ext; funext N W
  change provision B (markInk K h*g) _ • (1:FC _) = B g • q _ • (1:FC (Single (K.c N)))
  rw [he,mul_smul]

def splitMap : Prices K where
  toFun f := A (ticketProvision B f)
  map_add' f g := by
    have hp : ticketProvision B (f+g)=ticketProvision B f+ticketProvision B g:= by
      apply Subtype.ext; funext N W
      change provision B (f+g) _ • (1:FC _) = provision B f _ • (1:FC _) + provision B g _ • (1:FC (Single (K.c N)))
      rw [provision,map_add,map_add,add_smul]; rfl
    rw [hp,map_add]
  map_smul' c f := by
    have hp : ticketProvision B (c • f)=c • ticketProvision B f:= by
      apply Subtype.ext; funext N W
      change provision B (c • f) _ • (1:FC _) = c • provision B f _ • (1:FC (Single (K.c N)))
      rw [provision,map_smul,map_smul,smul_smul,provision]; rfl
    rw [hp,map_smul]; rfl

lemma split_pay (h : f∈ Gate K) (g' : g∈ Mantle K) :
    splitMap A B (f*g)=A f*B g := by
  obtain ⟨S,a,t,rfl⟩ := h
  change A (ticketProvision B _)=_
  rw [ticket_factor B t g', map_smul]; exact mul_comm _ _
lemma split_gate (p : B 1=1) (h : f∈ Gate K) : splitMap A B f=A f := by
  simpa [p] using split_pay A B h (Mantle K|>.one_mem)
lemma split_mantle (p : A 1=1) (h : f∈ Mantle K) : splitMap A B f=B f := by
  simpa [p] using split_pay A B (Gate K|>.one_mem) h
lemma buildSplit (p : A 1=1) (q : B 1=1) : Split (splitMap A B) :=
  ⟨(split_gate A B q (Gate K|>.one_mem)).trans p,fun a h b g ↦ (split_pay A B h g).trans
    (congrArg₂ (· * ·) (split_gate A B q h).symm (split_mantle A B p g).symm)⟩

-- no ambiguity
lemma uniquelySplit (M : Prices K)(h : Split M)
    (e : ∀ f∈Gate K,A f=M f) (v : ∀ g∈Mantle K,B g=M g) : M=splitMap A B := by
  apply LinearMap.ext; intro x
  obtain ⟨S,p⟩:= findsBay K x
  obtain ⟨f,rfl⟩ := accolade K S x p
  rw [Pockets.factors,map_sum,map_sum]; refine sum_congr rfl fun i _ ↦ ?_
  rw [split_pay A B (ink_mem K (authentic S (f i))) (word_ink S K i),h.pixel _ (ink_mem K (authentic S (f i))) _ (word_ink S K i),
    e _ (ink_mem K (authentic S (f i))),v _ (word_ink S K i)]
end construction

/-- Can do it for SUBALGEBRA maps alone (and arbitrary assignments outside);
i.e. no implication that normalization means extension by positivity. Both pure
marginal hypotheses can be tested via Split. -/
theorem alwaysASplit (A : Gate K →ₗ[ℂ] ℂ) (B : Mantle K →ₗ[ℂ] ℂ)
    (p : A 1=1) (q : B 1=1) :
    ∃ M : Prices K, Split M ∧ (∀ a:Gate K,M a=A a) ∧ (∀ b:Mantle K,M b=B b) := by
  obtain ⟨U,h⟩ := (Gate K).toSubmodule.exists_isCompl
  obtain ⟨V,v⟩ := (Mantle K).toSubmodule.exists_isCompl
  let a : Prices K:= A.comp ((Gate K).toSubmodule.projectionOnto U h)
  let b : Prices K:= B.comp ((Mantle K).toSubmodule.projectionOnto V v)
  have ha (x : Gate K): a x.val=A x:=congrArg A (Submodule.projectionOnto_apply_left h x)
  have hb (x : Mantle K): b x.val=B x:=congrArg B (Submodule.projectionOnto_apply_left v x)
  have hx : a 1=1 := (ha 1).trans p; have hy : b 1=1 := (hb 1).trans q
  exact ⟨splitMap a b,buildSplit a b hx hy,fun x ↦ (split_gate a b hy x.property).trans (ha x),
    fun y ↦ (split_mantle a b hx y.property).trans (hb y)⟩

/-- Ward on ONE raw marginal suffices. On every localized gauge incl 
constant values on the pockets; no need for ward jointly on all products. -/
def GatesPrice (M : Prices K) (p : GVertex) := ∀ f ∈ Gate K, M (pennant K p f)=M f
def MantlesPrice (M : Prices K) (p : GVertex) := ∀ f∈ Mantle K, M (pennant K p f)=M f

def PureWard (M : Prices K) : Prop:= (∀ p, GatesPrice M p) ∨ (∀ p, MantlesPrice M p)

def Comparison (M : Prices K) : Prop := Split M ∧ PureWard M

theorem split_gate_ward {A B : Prices K} {p : GVertex} (q : B 1=1) (h : GatesPrice A p) :
    GatesPrice (splitMap A B) p := fun f v ↦ (split_gate _ _ q (gateWard p v)).trans
      ((h f v).trans (split_gate _ _ q v).symm)
theorem split_mantle_ward {A B : Prices K} {p : GVertex} (q : A 1=1) (h : MantlesPrice B p) :
    MantlesPrice (splitMap A B) p := fun f v ↦ (split_mantle _ _ q (mantleWard p v)).trans
      ((h f v).trans (split_mantle _ _ q v).symm)

end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms alwaysASplit
#print axioms uniquelySplit
#print axioms split_gate_ward
#print axioms split_mantle_ward
end YM.CF.Buffered.Afterglow.Pockets
