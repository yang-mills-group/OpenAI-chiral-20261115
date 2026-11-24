import YM.SU5.MacroSix.Letters
import YM.SU5.FiniteGaugeData.Tapestry.Concord
import YM.SU5.FiniteGaugeData.Tapestry.Neutral

/-! # Cost on both panes for the course: manuscript endpoint-pocket calculation

Step 1. Every supported finite-test recipe in these cover pockets is priced
on a (single-roomy suffices) calibration family call, via the `torRibbon`
criterion and lifting from the call into exactly the claimed `Family`
support. Use the basis procedure (compare `SU5/Selected/Cor/Diamond:Reach.extensionA`),
but **wide**, and for these bare charges. Step 2. On the very same price as
used for the coherence across the election, check that the Mark sent to the next
level is in that grammar. With all stamps & neighborhoods of the movement
already payable this way (specify Spanned). This works for two pockets in an
arbitrary orientation.
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

/-- Coefficient pieces: the whole `Coeff true` of the pair constitutive height.
`S` will include `U,V`. -/
def ribbon (K : Calibration) (S : Finset Cover) (b : Bool) (U V : Finset Cover) :
    Submodule ℂ (Family K) := Submodule.span ℂ {f|∃ v∈ stamp K b U V,
      ∃ q : PairsC → ℂ, Coeff true S q ∧ f=scalar K q * v}

variable {K : Calibration}{S U V : Finset Cover}{b : Bool}{f : Family K}

lemma mixed_ribbon (h : f∈ stamp K b U V) {g : PairsC → ℂ} (p : Coeff true S g) :
    scalar K g*f∈ ribbon K S b U V := Submodule.subset_span (show _ ∈ _ from ⟨f,h,g,p,rfl⟩)
lemma ribbon_test (h : f∈ ribbon K S b U V) (p : U ⊆ S) (q : V ⊆ S) : InTest K true S false f :=
  Submodule.span_induction (p:=fun f _ ↦ InTest K true S false f)
    (by rintro x ⟨v,h,q',u,rfl⟩; exact InTest.mul (.seed u) (stamp_test h p q))
    .zero (fun _ _ _ _ a b ↦ .add a b) (fun z _ _ a ↦ .smul z a) h

variable (N : Side)
local notation "n" => K.c N

lemma ribbon_view (h : f∈ ribbon K S b U V) (W : Fields (K.c N)) :
    f N W∈ torRibbon b (region U n) (region V n) := by
  let D := torRibbon b (region U n) (region V n)
  refine Submodule.span_induction (p:=fun f _ ↦ f N W∈ D) ?_ D.zero_mem
    (fun _ _ _ _ p q ↦ D.add_mem p q) (fun a _ _ p ↦ D.smul_mem _ p) h
  rintro v ⟨z,p,g,q,rfl⟩; obtain ⟨A,l,H⟩ := stamp_paid N p; change (g _ • (1:FC (Single n)))*z N W∈ D
  rw [Algebra.smul_mul_assoc,one_mul,H]; exact D.smul_mem _ l

lemma through_glasses (e : Roomy S (K.c N)) (p : U ⊆ S) (q : V ⊆ S)
    (hf : InTest K true S false f) (h : ∀ W, f N W∈ torRibbon b (region U (K.c N)) (region V (K.c N))) :
    f∈ ribbon K S b U V := by
  let L := ribbon K S b U V
  let D := torRibbon b (region U n) (region V n)
  have hu := hf.support N
  obtain ⟨W,g⟩ := D.exists_isCompl
  let B := Module.finBasis ℂ D
  let I := Fin (Module.finrank ℂ D); let T := D.projectionOnto W g
  let P (i : I) := (B.coord i).comp T
  choose Z t r using (fun i : I ↦ adopted_tor K N (show (B i).val ∈ D from (B i).property))
  let A (i : I) (x : PairsC) : ℂ := P i (f N (replant S n x))
  have ht (i : I) : Coeff true S (A i) :=
    ⟨fun h ↦ by contradiction,pole_w _ ((P i):FC (Single n) → ℂ) (P i).continuous_of_finiteDimensional
        (Env.along (g:=replant S n) hu.env (replant_b S n)), fun x y p q ↦
        congrArg (P i) (hu.dep _ _ (tack S n e x.1 y.1 p) (tack S n e x.2 y.2 q))⟩
  let v : Family K := ∑ i, scalar K (A i)* Z i
  have hv : v∈ L:= L.sum_mem (fun i _ ↦ mixed_ribbon (t i) (ht i))
  suffices f=v by rwa [this]
  apply looksLike (m:=N) (Roomy.seats e) hf (ribbon_test hv p q)
  funext j; let k : D := ⟨f N j,h j⟩
  have he : T (f N j)=k:= Submodule.projectionOnto_apply_left g k
  have hx (i : I) : (scalar K (A i)*Z i) N j = B.coord i k • (B i).val := by
    rw [Pi.mul_apply,Pi.mul_apply,r i j]; change (P i (f N (replant S n (Prod.map (onC n) (onC n) j))) • (1:FC (Single n)))*_ = _
    have hp : f N (replant S n (Prod.map (onC n) (onC n) j))= f N j :=
      hu.dep _ _ (untack S n (Roomy.seats e) j.1) (untack S n (Roomy.seats e) j.2)
    rw [hp,Algebra.smul_mul_assoc,one_mul]; change B.coord i (T (f N j)) • _=_; rw [he]
  unfold v; simp_rw [Finset.sum_apply,hx]
  have ht : k = ∑ i, B.coord i k • B i:= (B.sum_repr k).symm
  change k.val= _
  conv_lhs => rw [ht]
  rw [Submodule.coe_sum]; try rfl

section receipt
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ : Preparation}{l : ℕ}(Y : Course Λ (VolumeCape.Dream.Nimbus l))(H : Real.exp 1 ≤ Λ.x)
variable (s i k : ℕ)
local notation "Up" S:max => followBox (Λ:=Λ) (l:=l) S
local notation "m" => side Y i s
local notation "m'" => side Y i (s+1)
local notation "K₀" => tent Y H

variable (Λ l) in
lemma follow_subset (p : U⊆ S) : (followBox (Λ:=Λ) (l:=l) U)⊆ followBox (Λ:=Λ) (l:=l) S :=
  by
    intro a h; obtain ⟨z,t,w⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨z,Finset.image_subset_image p t,w⟩

private lemma ribbon_padding (U : Finset Cover) :
    let G:=apt (Y.ir i) Λ.block Λ.R.L s
    padded G (region U m) (clothRadius G.count (aliasLaw Λ)) ⊆ region (Up U) m' := by
  intro G
  let Z := aliasLaw Λ; let S := region U m
  let L := G.count.val
  let D := distanceLaw l; let B := L * gross Z D Λ.R.J
  have h : padded G S (L*beforePad Z) ⊆ padded G S B := Corona.halo_mono
    (Nat.mul_le_mul_left _ (by unfold gross; omega)) (Subset.refl _)
  apply Finset.Subset.trans (s₂:=padded G S B) ((halo_subset _ _).trans ((before_zone G S Z).trans h))
  exact Satin.next_contains U B m G

-- indeed no hypothesis of multiplicativity of `D` there. Takes just the argument
-- by admissible ascender, no period comparison needed here.
lemma ribbon_ascends {f : Mark (side Y i s)} (h : ∀ W, f W∈ torRibbon b (region U m) (region V m))
    (x : Fields (side Y i (s+1))) : ascender Y s i k f x∈ torRibbon b
      (region (Up U) (side Y i (s+1))) (region (Up V) (side Y i (s+1))) := by
  refine torRibbon_mono (ribbon_padding Y s i U) (ribbon_padding Y s i V) ?_
  let G:=apt (Y.ir i) Λ.block Λ.R.L s
  let Z:=((Y.voyage i).X (Y.uv k)).gram (s+1)
  exact push_ribbon G Λ.K.j (Journey.legal Λ) Λ.R.odd_side Z.J.M (patternQ Y s i k)
    (patternA Y s i k) Chi.canonical Λ.J.d Z.beta ((Y.voyage i).CapeT s) h x

private lemma ribbon_cast {b : Bool} {U V : Finset Cover}{N : Side} (F : Mark N)
    {M : Side} (h : N=M) :
    (∀ W, F W∈ torRibbon b (region U N) (region V N)) ↔
      (∀ W, arrange N M h F W∈ torRibbon b (region U M) (region V M)) := by subst M; rfl

lemma ribbon_coupon (hp : U ⊆ S) (hv : V ⊆ S) (t : Spanned Y S s i k)
    (f : Swatch S) (h : render S K₀ f∈ ribbon K₀ S b U V) :
    render (Up S) K₀ (coupon Y H S s i k f)∈ ribbon K₀ (Up S) b (Up U) (Up V) := by
  let M := momentm Y i s; let M' := momentm Y i (s+1); let S' := Up S
  let P := coupon Y H S s i k f
  have e₁ : (K₀).c M=side Y i s:= terrain Y H (Y.ir i) s
  have e₂ : (K₀).c M'=side Y i (s+1):= terrain Y H (Y.ir i) (s+1)
  have he : Roomy (Up S) (side Y i (s+1)):=t.2.2
  apply through_glasses M' (e₂.symm ▸ he) (follow_subset Λ l hp) (follow_subset Λ l hv) (texture ..)
  have hx : ∀ W, present Y H s i S f W ∈ torRibbon b (region U (side Y i s)) (region V (side Y i s)) :=
    (ribbon_cast _ e₁).mp (ribbon_view M h)
  refine (ribbon_cast _ e₂).mpr ?_
  change ∀ W, present Y H (s+1) i (Up S) P W ∈ _
  rw [show present Y H (s+1) i (Up S) P=_ from onSpanned Y H S s i k t f]
  exact ribbon_ascends Y s i k hx
end receipt
end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms through_glasses
#print axioms ribbon_coupon
end YM.CF.Buffered.Afterglow.Pockets
