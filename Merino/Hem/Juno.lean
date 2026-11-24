import Merino.Hem.Slip
import Merino.Fenestral
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Hem
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
variable (P:Spine)


open Sour Spire Scroll
lemma ech_sums {I:Type*}(l:Finset I)(s:Sweep n)(F:I→Op (Single n)): ech s (∑ i∈l,F i)=∑ i∈l,ech s (F i):=by simp [ech,win_sum]

variable (σ:Signed)
def juno(m:ℕ)(z:Cover)(L:List Axis)(P:Spine)(s i k:ℕ): ℝ→ℂ:=
  let n:=age P.run i s
  glaze (stream n) (fun U=> ((funde P.par.K.j (blood P.run i k s) n U)-Dial.tickA n)*
    (ech (rim n σ)⁻¹ (squareSum millQ m L (wrap n z))))


lemma rover_nil (P:Spine)(z:Cover)(m s i k:ℕ):
    ∃ c:ℂ,juno σ m z [] P s i k=
      sparSite (N:=age P.run i s) P.par.K.j (blood P.run i k s) (offing σ z) + Function.const ℝ c:=by
  let n:=age P.run i s
  refine ⟨ -(Dial.tickA n*millQ (wrap n (offing σ z))).trace,?_⟩
  funext t; unfold juno glaze squareSum
  dsimp only
  rw [sub_mul,Matrix.trace_sub, sub_eq_add_neg,mill_back,millTrace]
  rfl

lemma rover_cons (P:Spine)(z:Cover)(m s i k:ℕ)(a:Axis)(L:List Axis):
    juno σ m z (a::L) P s i k =
      fun t=>∑ d∈range (2*m), juno σ m (farther a m d z) L P s i k t:=by
    funext; unfold juno glaze
    simp_rw [squareSum,stripSum, ech_sums, Finset.mul_sum, Matrix.trace_sum, farther, moveSite,
      map_add,map_sub,map_nsmul,wrap_step]

lemma rover_fee {P:Spine}(h:SprigFee P){m:ℕ}(hm:0 < m) (L:List Axis):
    ∀ z,∃ δ:ℝ,0<δ∧∀ᶠ s in atTop,∀ i k, Bud (juno σ m z L P s i k) ∧
      δ < (bud (juno σ m z L P s i k) 2).re:=by
  induction L with
  | nil=>
    intro z
    obtain ⟨δ,p,r⟩:=h.actual (offing σ z)
    refine ⟨δ,p,?_⟩
    filter_upwards [r] with s g i k
    obtain ⟨c,hc⟩:=rover_nil σ P z m s i k
    rw [hc]; exact g i k c
  | cons a l ih=>
    intro z
    choose c p q using fun d=>ih (farther a m d z)
    let r:=range (2*m)
    have hr:r.Nonempty:=⟨0,mem_range.mpr (by omega)⟩
    refine ⟨∑ d∈r,c d,sum_pos (fun d _=>p d) hr,?_⟩
    filter_upwards [(eventually_all_finite (r.finite_toSet)).mpr
      (fun d _=>q d)] with s g i k
    let f d := juno σ m (farther a m d z) l P s i k
    have hB: Bloom (fun t=>∑ d∈r,f d t) (∑ d∈r,bud (f d)):=
      Bloom.sum r fun d hd=>(g d hd i k).1.bloom
    rw [rover_cons,hB.bud_eq]
    refine ⟨hB.1,?_⟩
    rw [Finset.sum_apply,Complex.re_sum]
    exact sum_lt_sum_of_nonempty hr fun d hd=>(g d hd i k).2


def cuirass (P:Spine)(m:ℕ)(z:Cover)(s i k:ℕ):Oil (age P.run i s):=
  let n:=age P.run i s
  fun U=>(funde P.par.K.j (blood P.run i k s) n U-Dial.tickA n)*windmill (wrap n z) m
def forint (σ:Signed)(P:Spine)(m:ℕ)(z:Cover)(s i k:ℕ):ℝ→ℂ:=
 let n:=age P.run i s
 glaze (stream n) (julStep (rim n σ) (cuirass P m z s i k))

lemma uncle {P:Spine}(h:SprigFee P){m:ℕ}(hm:0 < m)(z:Cover)(hp:1≤P.par.K.j):
    ∃ δ:ℝ,0<δ∧∃ q:ℕ,∀ᶠ s:ℕ in atTop,∀ i k:ℕ,q≤(age P.run i s).val→
      δ < slash σ * (bud (forint σ P m z s i k) 2).re:=by
 obtain ⟨e,u,q,H⟩:=radiance P.par.K.j hp
 let l:=List.ofFn (id:Axis→Axis)
 obtain ⟨v,w,g⟩:=rover_fee σ h hm l z
 refine ⟨v,w,q,?_⟩
 filter_upwards [g] with s f i k hk
 let n:=age P.run i s
 let c:=bud (juno σ m z l P s i k)
 obtain ⟨a,b⟩:=f i k
 have ht:Bloom (forint σ P m z s i k) ((slash σ:ℂ) • c):=by
   apply (a.bloom.scale (slash σ:ℂ)).congr
   filter_upwards [petals_safe (stream n) u] with t hw
   change (julStep (rim n σ) (fun U=>(funde _ _ _ U-_)*windmill _ m)
     (profile (petals (stream n) t))).trace=_
   rw [full_slide _ _ _ _ _ hp e (H n hk) hw, Matrix.trace_smul]
   rfl
 rw [ht.bud_eq, Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul,←mul_assoc,
    ←pow_two, ←sq_abs, slash_abs, one_pow,one_mul]
 exact b

-- for stream Temper
lemma box_off (σ:Signed)(n:Side)(z:Cover): boxA (rim n σ) (node (wrap n z))=
     node (wrap n (offing σ z)):=by
   change (castX (rim n σ)).anon _ _=_
   rw [rim_cast,←Shape.nodex,Shape.mill,offing]
