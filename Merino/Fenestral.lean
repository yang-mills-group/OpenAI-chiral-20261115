import Merino.Glass
import Zephyr.Bed
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

lemma millTrace (z:Cover)(M:Op (Single n)):
    (M * millQ (wrap n z)).trace=∑ i:IS,M (tag n z i) (tag n z i):=by
  let w:=wrap n z
  have h: millQ w=Matrix.diagonal fun s=> if s.1.1=w then 1 else 0:=by
    ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,c⟩
    by_cases hx:x=w <;> by_cases hy:y=w <;> by_cases hu:i=j <;> by_cases hv:b=c <;>
      simp [millQ, panel,Matrix.sum_apply,Matrix.diagonal_apply,Matrix.one_apply,
        *, Ne.symm,ite_and]
  rw [h]
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  rw [←Equiv.sum_comp (Equiv.prodAssoc (Site n) SpinIdx SU.Slot).symm,Fintype.sum_prod_type]
  rw [sum_eq_single w]
  · apply sum_congr rfl; rintro ⟨i,j⟩ _
    change M (tag n z _) (tag n z _) * (if w=w then 1 else 0) = _
    rw [if_pos rfl,mul_one]
  · intro b _ hb; exact sum_eq_zero fun i _=> by simp only [Equiv.prodAssoc_symm_apply,if_neg hb,mul_zero]
  · simp


/-- Exact stripped reading through Loom, i.e. evaluated on argument *to* it. -/
def stripFee(m:ℕ)(z:Cover)(L:List Axis)(P:Spine)(s i k:ℕ): ℝ→ℂ:=
  let n:=age P.run i s
  glaze (stream n) (fun U=> ((funde P.par.K.j (blood P.run i k s) n U)-Dial.tickA n)*
    squareSum millQ m L (wrap n z))

def farther (i:Axis) (m r:ℕ)(z:Cover): Cover:= (z-m • step i)+(r+1) • step i

lemma strip_nil (P:Spine)(z:Cover)(m s i k:ℕ):
    ∃ c:ℂ,stripFee m z [] P s i k=
      sparSite (N:=age P.run i s) P.par.K.j (blood P.run i k s) z + Function.const ℝ c:=by
  let n:=age P.run i s
  refine ⟨ -(Dial.tickA n*millQ (wrap n z)).trace,?_⟩
  funext t; unfold stripFee glaze squareSum
  dsimp only
  rw [sub_mul,Matrix.trace_sub, sub_eq_add_neg,millTrace]
  rfl

lemma strip_cons (P:Spine)(z:Cover)(m s i k:ℕ)(a:Axis)(L:List Axis):
    stripFee m z (a::L) P s i k =
      fun t=>∑ d∈range (2*m), stripFee m (farther a m d z) L P s i k t:=by
    funext; unfold stripFee glaze
    simp_rw [squareSum,stripSum, Finset.mul_sum, Matrix.trace_sum, farther, moveSite,
      map_add,map_sub,map_nsmul,wrap_step]

lemma strip_fee {P:Spine}(h:SprigFee P){m:ℕ}(hm:0 < m) (L:List Axis):
    ∀ z,∃ δ:ℝ,0<δ∧∀ᶠ s in atTop,∀ i k, Bud (stripFee m z L P s i k) ∧
      δ < (bud (stripFee m z L P s i k) 2).re:=by
  induction L with
  | nil=>
    intro z
    obtain ⟨δ,p,r⟩:=h.actual z
    refine ⟨δ,p,?_⟩
    filter_upwards [r] with s g i k
    obtain ⟨c,hc⟩:=strip_nil P z m s i k
    rw [hc]; exact g i k c
  | cons a l ih=>
    intro z
    choose c p q using fun d=>ih (farther a m d z)
    let r:=range (2*m)
    have hr:r.Nonempty:=⟨0,mem_range.mpr (by omega)⟩
    refine ⟨∑ d∈r,c d,sum_pos (fun d _=>p d) hr,?_⟩
    filter_upwards [(eventually_all_finite (r.finite_toSet)).mpr
      (fun d _=>q d)] with s g i k
    let f d := stripFee m (farther a m d z) l P s i k
    have hB: Bloom (fun t=>∑ d∈r,f d t) (∑ d∈r,bud (f d)):=
      Bloom.sum r fun d hd=>(g d hd i k).1.bloom
    rw [strip_cons,hB.bud_eq]
    refine ⟨hB.1,?_⟩
    rw [Finset.sum_apply,Complex.re_sum]
    exact sum_lt_sum_of_nonempty hr fun d hd=>(g d hd i k).2

end YM.CF.Merino
