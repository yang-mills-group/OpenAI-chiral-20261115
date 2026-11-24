import YM.CF.BPress.Contour.Opals
import YM.CF.BPress.Contour.Fold
/-! concise B-contour for our hypotheses. Finite expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Push.SectorMeasure Env Finset MeasureTheory Function Palmer Ledger Grid Branch Bands Locale Lattice
open scoped Classical Topology BigOperators
variable {Y I:Type}{Φ:Y→ Type*}[DecidableEq I][Fintype I][Fintype Y][DecidableEq Y][∀ i,MeasurableSpace (Φ i)][∀ i,Nonempty (Φ i)][Nonempty Y]
variable (Z:Y→ Finset Y)(T:I→Finset Y) (A:(Seal Y)→ I→ (∀ i,Φ i)→ℂ)(G:Seal Y→(∀ i,Φ i)→ℂ)
variable (μ ν:∀ i, Measure (Φ i))[∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)] {q:ℝ}{a:I→ℝ}
abbrev sheetD (E:Seal Y)(i:I) (x:∀ i,Φ i):= Complex.exp (A E i x)-1
def sumE (E:Seal Y)(v : ∀ i,Φ i):= buoy G (Parts Z E) v * Complex.exp (∑ i,A E i v)
def glob : ℂ:= ∑ E:Seal Y, ∫ v,sumE Z A G E v ∂century μ ν E
variable {Z A G T}
lemma line_eq (P:Cabin Z T (sheetD A) G) : ∑ S:Finset (Seal Y⊕ I), line Z (sheetD A) G μ ν S= glob Z A G μ ν:=by
 let D:=sheetD A; unfold line; rw [←sum_filter]; unfold glob; have he : ∀ E:Seal Y, ∫ v,sumE Z A G E v ∂century μ ν E=∑ J:Finset I, channel D G μ ν (Parts Z E) J:=by
   intro E; let S:=Parts Z E; let V(v) i:=Complex.exp (A E i v)-1; have ht : floor S=E:=reconstruct ..; have hp(v:∀ i,Φ i):sumE Z A G E v=∑ J:Finset I,lance D G S J v:=by
      unfold sumE; rw [Complex.exp_sum]; unfold lance; rw [←mul_sum,ht,Finset.prod_congr rfl (show ∀ i∈ _,Complex.exp (A E i v)=1+D E i v from fun i _=> by unfold D sheetD; ring),prod_one_add,powerset_univ] -- tune
   unfold channel; change _=∑ J:Finset I, ∫ v,_∂century μ ν (floor S); simp_rw [ht,hp]; rw [integral_finsetSum]; intro i _; exact integrableX (P.sailsC (gathering ..) _) _
 simp_rw [he]; rw [← sum_product']; apply sum_bij (fun i _=> (floor i.toLeft,i.toRight)); · intros; simp
 · intro i b j v e; obtain ⟨p,q⟩:= Prod.mk.inj e; have hj:i.toLeft=j.toLeft:=((mem_filter.mp b).2.stays).symm.trans ((congrArg (Parts Z) p).trans ((mem_filter.mp v).2.stays)); exact i.toLeft_disjSum_toRight.symm.trans ((congrArg₂ disjSum hj q).trans j.toLeft_disjSum_toRight)
 · rintro ⟨E,M⟩ t; refine ⟨(Parts Z E).disjSum M,mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩; · rw [toLeft_disjSum]; exact gathering Z E
   rw [toLeft_disjSum,toRight_disjSum,floor,reconstruct Z E] -- tune floor
 intro i v; dsimp only; exact congrArg (fun x=>channel D G μ ν x i.toRight) ((mem_filter.mp v).2.stays).symm
structure Reaches (a:I→ℝ) (A:(Seal Y)→ I→ (∀ i,Φ i)→ℂ) : Prop where
 meas(E i): Measurable (A E i)
 sees (i E S) : Visible Z (T i) E=Visible Z (T i) S → A E i=A S i
 pane(E i): ScopedB (A E i) (watches Z (T i) E)
 tax(E i v):‖A E i v‖ ≤ a i -- `Z` implicit, T` Lean binder modifies!
structure Holds (Z:Y→ Finset Y)(T:I→Finset Y)(A:(Seal Y)→ I→ (∀ i,Φ i)→ℂ)(G:Seal Y→(∀ i,Φ i)→ℂ)(μ ν:∀ i,Measure (Φ i))(a:I→ℝ)(q:ℝ):Prop where
 env(Q)(p:Core Z Q):Envelope (G Q)
 sees(Q)(p:Core Z Q):ScopedB (G Q) (station Z Q)
 paid(Q)(p:Core Z Q): ∫ i,‖G Q i‖∂century μ ν Q ≤ q^Q.card
 owns : Reaches (Z:=Z) (T:=T) a A
variable {μ ν}
lemma Holds.sum (C:Holds Z T A G μ ν a q)(hq:0≤q)(u:∀ i,a i≤1): SumP Z T (sheetD A) G μ ν q (fun i=>2*a i):=by
 have ht(E i v):‖sheetD A E i v‖≤2*a i:= (Complex.norm_exp_sub_one_le ((C.owns.tax E i v).trans (u i))).trans (mul_le_mul_of_nonneg_left (C.owns.tax E i v) (by norm_num)); refine {bill:=C.env,extent:=C.sees,meter:=fun E i=> ⟨(Complex.continuous_exp.measurable.comp (C.owns.meas E i)).sub measurable_const, _, ht E i⟩,boost:=hq,fromSea:= fun E h=> ((C.paid E h).trans_eq (if_pos h|>.symm)), fromEarth:=ht, cond:= fun i E S h=>congrArg (fun f=> fun v=> Complex.exp (f v)-1) (C.owns.sees i E S h), when:= fun E i x y v=> congrArg (fun k=> Complex.exp k-1) (C.owns.pane E i x y v)} -- tune refine structure field separators
set_option linter.unusedSectionVars false in
lemma modulus {m:Side} {F:Branch.Field Y}{u γ C:ℝ}(h: SumP Z T (sheetD A) G μ ν q a)(p:∀ i,i∈ Z i)(c:Stakes m (u+u) γ)(b: Stakes m u C)(ht:till_cost m γ≤ C)(f:till_cost m C≤1)(L:Sole F m)(e:evenT F Z)(t: evenT F T)(w:Cash (chart Z T) (beads Z q a) ((u+u)+(u+u)) γ) : Real.exp (-(Fintype.card Y:ℝ))≤ ‖glob Z A G μ ν‖:=by
 let W:= chart Z T; obtain ⟨a,v,V,y⟩:= algorithm (h.toCabin.ship μ ν p) L b c ht (chart_g Z T e t) w (fun i=> h.pile p _); let g:=sheetD A; rw [←line_eq μ ν h.toCabin,a,Complex.norm_exp]; apply Real.exp_le_exp.mpr; have H:= (V.total b.he.le (by rintro i (h : id _ = _); by_contra! w; exact (inhabited_grove (y i w)).ne_empty h)).2.2; rw [tsum_fintype] at H; apply le_trans _ ((abs_le.mp (Complex.abs_re_le_norm _)).1); refine neg_le_neg ((norm_sum_le _ _ ).trans ((sum_le_sum (fun i _=> v i)).trans (H.trans ((mul_le_mul_of_nonneg_left f (Nat.cast_nonneg _)).trans_eq (mul_one _))))) -- tune
end YM.CF.BPress.Contour
