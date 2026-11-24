import SatinStress.U2.Chain
import SatinStress.U1.ClassLine
/-!
# Transfer input from the *free polynomial class calculations*

Direct sum (incl *one* matter & one mixed copy for each of two species).
Everything still in polynomial-test payment. The two species here are **copies**
because this calculation is on flavor-invariant tensors after the reduction.
No claim that the 5 and 10 representation/test factors have been identified with
their physical prices here, have the same normalization or are interchangeable as
operators.
-/
namespace SatinStress.U2.Shape
open SatinStress.U1 Derivative Class Sequence ChainData
open Chart (s t)
open Module (finrank)

variable (K : Type*) [Field K] [Algebra K ℂ] [CharZero K]
noncomputable section

section
variable {a b pol : Type} [Fintype a] [Fintype b] (C : Class pol a) (H : Class pol b)
    (f : Freq) (e : Lands K C H f)
/-- (94) on each of the individual U1 types. -/
def fromBlock : ChainData K (C.image TT K) (H.image V K) (H.image W K) (Grid (DR pol)) where
  grad := (up K C f).codRestrict _ (fun i => e.vw ⟨i,rfl⟩)
  divg := (D K C f).codRestrict _ (fun i => e.ww ⟨i,rfl⟩)
  obstruction := difference K H f
omit [CharZero K] in
theorem ker_divg_fromBlock : (fromBlock K C H f e).supply = (D K C f).ker := by
  ext x
  change _∈(LinearMap.ker (_)) ↔ _; rw [LinearMap.mem_ker,LinearMap.mem_ker]; exact Subtype.ext_iff
omit [CharZero K] in
theorem rank_divg_fromBlock : finrank K (fromBlock K C H f e).divg.range = finrank K (D K C f).range := by
  have h := LinearMap.finrank_range_add_finrank_ker (fromBlock K C H f e).divg
  have z := LinearMap.finrank_range_add_finrank_ker (D K C f)
  rw [show (fromBlock K C H f e).divg.ker = _ from ker_divg_fromBlock K C H f e] at h
  exact add_right_cancel (h.trans z.symm)
omit [CharZero K] in
lemma fromBlock_full' {q w r u o p} (h : RowRanks K C H f q w r u o p) (hn : (f 0).den ≠ 0) :
    (fromBlock K C H f h.stays).Full :=
  ⟨fun _ _ e => Subtype.ext (monoT K f hn pol (congr_arg Subtype.val e)),h.exact94⟩
end

abbrev TT0 := (gaugeStress K) × ((flavorStress K) × (mixedStress K)) × ((flavorStress K) × (mixedStress K))
/-- Middle and right space of (divg) both use the five-total copies. -/
abbrev Both {o : Type} (O : Schedule o) := (ph5.image O K) × (mixed.image O K)
abbrev Total {o : Type} (O : Schedule o) := (ge5.image O K) × Both K O × Both K O
abbrev VV := Total K V
abbrev WW := Total K W
-- last `Z`: even for K=ℝ, these tests use complex polynomials.
abbrev EndCost := Grid (DR GPol) × (Grid (DR FPol) × Grid (DR XPol)) × (Grid (DR FPol) × Grid (DR XPol))

def g := fromBlock K ge4 ge5 s (table9394 K).1.stays
def f := fromBlock K ph4 ph5 s (table9394 K).2.1.stays
def x := fromBlock K mixed4 mixed t (table9394 K).2.2.stays
def chain : ChainData K (TT0 K) (VV K) (WW K) EndCost := (g K).prod (((f K).prod (x K)).prod ((f K).prod (x K)))
lemma full : (chain K).Full := by
  have hf : (f K).Full := fromBlock_full' K _ _ _ (table9394 K).2.1 (nonzero_s _)
  have hx : (x K).Full := fromBlock_full' K _ _ _ (table9394 K).2.2 (nonzero_t _)
  exact (fromBlock_full' K _ _ _ (table9394 K).1 (nonzero_s _)).prod ((hf.prod hx).prod (hf.prod hx))

-- Aid possible synthesis costs ([FiniteDimensional K] from product). expose all.
lemma dim_T : finrank K (TT0 K)=7 := by
  obtain ⟨a,b,c⟩ := table9394 K
  simp only [TT0,Module.finrank_prod,gaugeStress,mixedStress,flavorStress,a.rankT,b.rankT,c.rankT]
lemma dim_W : finrank K (WW K)=6 := by
  obtain ⟨a,b,c⟩ := table9394 K
  simp only [WW,Total,Both,Module.finrank_prod,a.rankW,b.rankW,c.rankW]
lemma dim_V : finrank K (VV K)=60 := by
  obtain ⟨a,b,c⟩ := table9394 K
  simp only [VV,Total,Both,Module.finrank_prod,a.rankV,b.rankV,c.rankV]
lemma rankD : finrank K (chain K).divg.range = 4 := by
  obtain ⟨a,b,c⟩ := table9394 K
  rw [chain, prod_rank_div (g K) _, prod_rank_div ((f K).prod (x K)) _]
  rw [prod_rank_div (f K) (x K)]
  unfold g f x
  rw [rank_divg_fromBlock, rank_divg_fromBlock K ph4, rank_divg_fromBlock K mixed4, a.divergence,b.divergence,c.divergence]
lemma rank_obs : finrank K (chain K).obstruction.range = 59 := by
  have h := (full K).count; rw [dim_T, dim_V, dim_W] at h; omega
lemma dim_supply : finrank K (chain K).supply = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (chain K).divg; rw [rankD, dim_T] at h
  unfold supply; omega

-- Coordinate isomorphism for the 3-dimensional conservation space. (Product on it in U3
-- with these free *normalizations* still calls for calculating the charges on free Wick,
-- not just the above kernel-rank computations.)
def sectorLift : (Fin 3 → K) →ₗ[K] (TT0 K) where
  toFun z := (z 0 • Line.Jg K, (z 1 • Line.Jf K,0), (z 2 • Line.Jf K,0))
  map_add' _ _ := Prod.ext (by simp [add_smul]) (by ext1 <;> ext1 <;> simp [add_smul])
  map_smul' c z := Prod.ext (by simp [mul_smul]) (by ext1 <;> ext1 <;> simp [mul_smul])

lemma lift_mem (z : Fin 3 → K) : sectorLift K z ∈ (chain K).supply := by
  obtain ⟨h,h'⟩ := Line.supplies K
  have he : LinearMap.ker (g K).divg = Submodule.span K {Line.Jg K} := (ker_divg_fromBlock ..).trans h
  have he' : LinearMap.ker (f K).divg = Submodule.span K {Line.Jf K} := (ker_divg_fromBlock ..).trans h'
  have hv : (g K).divg (Line.Jg K)=0 := LinearMap.mem_ker.mp (by rw [he]; exact Submodule.mem_span_singleton_self _)
  have hv' : (f K).divg (Line.Jf K)=0 := LinearMap.mem_ker.mp (by rw [he']; exact Submodule.mem_span_singleton_self _)
  apply LinearMap.mem_ker.mpr
  rw [chain]; simp only [prod_divg,sectorLift,LinearMap.coe_mk, AddHom.coe_mk,map_smul,hv,hv', smul_zero,map_zero]; rfl

def entering := (sectorLift K).codRestrict (chain K).supply (lift_mem K)
lemma independent : Function.Injective (entering K) := by
  intro x y eq
  let z := x - y
  suffices z = 0 from sub_eq_zero.mp this
  have h : entering K z = 0 := by simp [z,eq]
  have hh := congr_arg Subtype.val h
  have e0 : z 0 • Line.Jg K = 0 := congr_arg Prod.fst hh
  have e1 : z 1 • Line.Jf K = 0 := congr_arg (Prod.fst ∘ Prod.fst ∘ Prod.snd) hh
  have e2 : z 2 • Line.Jf K = 0 := congr_arg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hh
  ext i; fin_cases i
  · exact (smul_eq_zero_iff_left (Line.Jg_ne K)).mp e0
  · exact (smul_eq_zero_iff_left (Line.Jf_ne K)).mp e1
  exact (smul_eq_zero_iff_left (Line.Jf_ne K)).mp e2

def normalized : (Fin 3 → K) ≃ₗ[K] (chain K).supply :=
  LinearEquiv.ofBijective (entering K)
    ⟨independent K,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K:=K) (V:=Fin 3 → K) (V₂:=↥(chain K).supply) (f:=entering K)
      (show finrank K (Fin 3 → K) = finrank K (chain K).supply by rw [dim_supply]; simp)).mp (independent K)⟩
@[simp] lemma normalized_price (v : Fin 3 → K) : (normalized K v).val = sectorLift K v := rfl
end
end SatinStress.U2.Shape
