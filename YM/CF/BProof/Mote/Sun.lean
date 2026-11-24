import YM.CF.Scroll.Kent
/- Exact finite Laurent expansion needed for mode-lift. Keep inverse absent! Averaging over centered block lengths is performed in `rail`, and its (power j convoluted) finite stencil is recognised by keeping all these sums in the subalgebra of finite Fourier series. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir.BasisRim
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame Rush Scroll
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
abbrev noteD := Momentum→ℂ
abbrev modeT (v:Cover):noteD :=fun p=>mode p v
inductive Sheet : noteD→Prop where
| mode (x:Cover): Sheet (modeT x)
| zero: Sheet 0
| plus {f g}: Sheet f → Sheet g→ Sheet (f+g)
| scale {f}: Sheet f → ∀ z:ℂ,Sheet (z • f)
namespace Sheet
variable {f g:noteD}
lemma shiftL {x:Cover}(p:Sheet f): Sheet (modeT x*f):=by
 induction p with
 | mode y=> rw [show modeT x*modeT y=modeT (x+y) from (funext fun p=> (mode_shift p x y).symm)]; apply Sheet.mode
 | zero=> rw [mul_zero]; exact Sheet.zero
 | plus _ _ i j=> rw [mul_add]; exact i.plus j
 | scale _ c i=> rw [Algebra.mul_smul_comm]; exact i.scale c
lemma times (p:Sheet f) (u:Sheet g):Sheet (f*g) :=by
  induction p with
  | mode i=> exact shiftL u
  | zero=> rw [zero_mul]; exact Sheet.zero
  | plus _ _ i j=> rw [add_mul]; exact i.plus j
  | scale _ s i=> rw [Algebra.smul_mul_assoc]; exact i.scale _
lemma unit : Sheet 1:=by rw [← show modeT 0=(1:noteD) from funext fun p=>mode_zero _]; apply Sheet.mode
lemma cash (x:ℂ): Sheet fun _=>x :=by rw [show (fun _:Momentum=>x)=x•(1:noteD) from funext fun p=>(mul_one x).symm]; exact unit.scale x
lemma sum_h {α:Type*}(S:Finset α)(F:α→ noteD)(h:∀ i∈S,Sheet (F i)):Sheet (fun p=>∑ i∈S,F i p):=by
 induction S using Finset.induction_on with| empty=>simp only [Finset.sum_empty]; exact Sheet.zero | insert i s g t=> simp only [Finset.sum_insert g]; exact (h i (mem_insert_self ..)).plus (t fun j u=> h j (mem_insert_of_mem u))
lemma prod_h {α:Type*}(S:Finset α)(F:α→noteD)(h:∀ i∈S,Sheet (F i)): Sheet (fun p=>∏ i∈S,F i p) :=by
 induction S using Finset.induction_on with| empty=> simp only [Finset.prod_empty]; exact unit | insert i s g t=> simp only [Finset.prod_insert g]; exact times (h i (mem_insert_self ..)) (t fun j u=>h j (mem_insert_of_mem u))
lemma pows (p:Sheet f)(n:ℕ): Sheet (fun i=> f i ^ n):=by induction n with| zero=> simp only [pow_zero]; exact unit| succ n h=> simp only [pow_succ]; exact h.times p
/-- λ-harmonics alias sum, calculated with exact centered alias convention. -/
def harmony (L:Side)(F:noteD): noteD:=fun p=> ∑ l:Site L,F (aliasAt p l)
lemma sings_h (L:Side)(p:Sheet f):Sheet (harmony L f):=by
 induction p with
 | mode v=>
    by_cases h:wrap L v=0
    · obtain ⟨z,y⟩:= cover_of_eq (0:Cover) v ((map_zero (wrap L)).trans h.symm); have ht:harmony L (modeT v)= (Fintype.card (Site L):ℂ) • modeT z:=by funext p; unfold harmony modeT; rw [zero_add] at y; simp_rw [y,←mode_scale,alias_scale,mode_phase,mode_periodic,mul_one]; rw [Finset.sum_const,card_univ,←Nat.cast_smul_eq_nsmul ℂ]; rfl
      rw [ht]; exact (Sheet.mode z).scale _
    rw [show harmony L (modeT v)=0 from ?_]; exact Sheet.zero
    funext p; unfold harmony modeT aliasAt; simp_rw [mode_phase,← cell_wrap,show ∀ l:Site L,cell l (wrap L v)=cell (wrap L v) l from fun _=>cell_duality ..,← mul_sum]; rw [sum_cell h,mul_zero]; rfl
 | zero=> unfold harmony; simp only [Pi.zero_apply,sum_const_zero]; exact Sheet.zero
 | plus _ _ i j=> unfold harmony; simp only [Pi.add_apply,sum_add_distrib]; exact i.plus j
 | scale _ c i=> unfold harmony; simp only [Pi.smul_apply,←Finset.smul_sum]; exact i.scale c
-- monomial algebra; frequencies λ t- lift selected. geometry bound captured by extraction
lemma swirl (i:Axis)(x:ℤ): Sheet fun p=> twirl (p i) x:=by
 let z:Cover:=Pi.single i x; refine (?_ : (fun p=> twirl (p i) x)=modeT z) ▸ Sheet.mode z; funext p; unfold twirl modeT Laurent.mode; rw [Finset.sum_eq_single i]; simp [z]; ring_nf -- tune
 intro j _ h; simp [z,h]
 simp
lemma stanch (L:Side)(i:Axis): Sheet fun p=> Next.Free.plank L (p i):=by
 simp_rw [plank_centers]; exact times (cash (L.val:ℂ)⁻¹) (sum_h (range L.val) _ (fun (x:ℕ) _=> swirl i (x-mid L))) -- ℤ subtraction correction
lemma main (L:Side)(j:ℕ): Sheet (muff j L):= (prod_h (Finset.univ:Finset Axis) (fun i (p:Momentum)=> plank L (p i)) (fun i _=> stanch L i)).pows j
end Sheet
end YM.CF.Fir.BasisRim
