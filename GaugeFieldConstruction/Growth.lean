import GaugeFieldConstruction.Sommar
import GaugeFieldConstruction.Gisborne
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots.Connect
open Function Filter Metric MeasureTheory Finset Mew
open Py.Rate.Pitching.Focus.CoeffArc
open scoped Topology ContDiff BigOperators Matrix Classical Mew
variable {I J K X Y E F:Type}[LinearOrder I][LinearOrder J][LinearOrder K][Fintype I][Fintype J][Fintype K][DecidableEq X][DecidableEq Y][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable (σ:I→X)(t:J→X)(C:J→ Key I)(ρ:K→Y)(τ:J→Y)(A:J→Key K)
abbrev Ivec (J:Type)[DecidableEq J]:J→ Key J:=fun i j=> if i=j then 1 else 0
lemma I_t : Tours t t (Ivec J):=fun j i p=> if_neg (show ¬j=i from fun e=>p (mem_filter.mpr ⟨mem_univ i,congrArg t e.symm⟩)) -- e ▸ rfl
lemma I_spot (z:Key J) : SpotQ (Ivec J) z=z:=by ext i:1; unfold SpotQ Ivec; rw [Finset.sum_apply]; simp
lemma I_Pica (F':Key J→E)(l:List J) : Pica t t (Ivec J) F' l=tipI F' l:=by
 suffices he:∀ K:List J→E,Jetd t t (Ivec J) K l= K l from he _
 intro K; induction l generalizing K with
 | nil=> simp [Jetd,Jetd.aux]
 | cons i l ih=>
    rw [Jetd,Jetd.aux,sum_eq_single_of_mem i (show i∈Entry t (t i) from mem_filter.mpr ⟨mem_univ _,rfl⟩)]; · rw [show Ivec J i i=1 from if_pos rfl, one_smul]; exact ih _
    intro b _ w; rw [show Ivec J i b=0 from if_neg (Ne.symm w),zero_smul]
lemma hatchΦ (F: Finset I→E): Hatch σ E (univ.image σ) (Fluid σ F):= Hatch.sum σ _ _ (fun i z=> pine i z • F i) fun i q=> Hatch.mon _ ⟨(mem_filter.mp q).2,fun i _=> mem_image_of_mem σ (mem_univ i)⟩ _
lemma Stem_P(C:I→ I→ℂ)(F:Key I→ E): Fluid σ (streamArc F σ C)=palm_R F σ ∘ toV_C σ C:=by
 let D(i j:I):ℂ:= if σ i=σ j then C j i else 0
 have hx: Tours σ σ D:=fun i j p=> if_neg (fun q=>p (mem_filter.mpr ⟨mem_univ _,q.symm⟩))
 have he:toV_C σ C=SpotQ D:=by
    funext z i; unfold toV_C SpotQ pipe_ζ; rw [sum_filter, Finset.sum_apply]; apply sum_congr rfl; intro j _; change _=z j*(if σ j=σ i then _ else _); split <;> simp [*,mul_comm]
 have ht:= Hatch.cost σ _ (Hatch_comp σ σ _ hx (hatchΦ σ (gemI F))); rw [show Fluid σ (streamArc F σ C)=palm_R ((palm_R F σ) ∘ toV_C σ C) σ from ?_,he]; · exact ht.symm
 funext z; unfold Fluid streamArc palm_R seedΞ; exact Finset.sum_congr rfl (fun i x=>by rw [if_pos x])
-- polymorphic `Darboux`
variable {f:Key I→E}{g:Key K→ F}
variable (p:River f)(q:River g)(u:Tours σ t C)(v:Tours ρ τ A)
lemma Jet_wax (l:List J){F G: List I→E}(h:∀ L,L.map σ=l.map t→ F L=G L): Jetd σ t C F l=Jetd σ t C G l:=by
 induction l generalizing F G with
 | nil=> simp_rw [Jetd,Jetd.aux]; exact h _ rfl
 | cons i l ih=>
    unfold Jetd; rw [Jetd.aux,Jetd.aux]; refine sum_congr rfl fun k w=>?_; apply congrArg; exact ih fun x e=>h (k::x) (by rw [List.map_cons,List.map_cons,e,(mem_filter.mp w).2]) -- tune
variable [NormedSpace ℝ E][NormedSpace ℝ F][IsScalarTower ℝ ℂ E][IsScalarTower ℝ ℂ F]
include p u
lemma Hatch_part (l:List J)(z: ψS t l): let V:=fun y=>palm_R f σ (SpotQ C y); Hatch t E (univ.image σ) V∧ tipI V l=Pica σ t C f l:=by
 intro V; have hp:Hatch t E (univ.image σ) V:= Hatch_comp σ t C u (hatchΦ σ (gemI f)); have he:= Darboux σ t C t t (Ivec J) ((hatchΦ σ (gemI f)).rivers ..) (hp.rivers ..) (ContinuousLinearMap.id ℝ E) u (I_t t) z z (Eventually.of_forall (fun x _=>by rw [LegQ,I_spot]; rfl)) -- tune p
 refine ⟨hp,?_⟩; rw [←I_Pica t _ l]; exact he.trans (Jet_wax σ t C l (fun L v=> spark_U σ p (by unfold ψS; rw [v]; exact z)))
-- $Y group$. use iff equal.T.All
abbrev SameGrade(t:J→X)(u:J→Y):Prop:= ∀ i j,t i=t j ↔ u i=u j
variable (G:SameGrade t τ)(M:E→L[ℝ] F)(Q:ℂ →+* ℂ)(H:∀ a x,M (a • x)=Q a • M x)
include q v G H
lemma Assembly (e:∀ᶠ x:J→ℝ in 𝓝 0,g (LegQ A x)=M (f (LegQ C x)))(z:Key J) : palm_R g ρ (SpotQ A (Q ∘ z))=M (palm_R f σ (SpotQ C z)):=by
 let W(y):= palm_R f σ (SpotQ C y); let T (y):=palm_R g ρ (SpotQ A y); change T _=M (W z)
 have hW:Hatch t E (univ.image σ) W:=Hatch_comp σ t C u (hatchΦ σ (gemI f)); have hT: Hatch τ F (univ.image ρ) T:= Hatch_comp ρ τ A v (hatchΦ ρ (gemI g))
 have hu:realm_C t= realm_C τ:=by
    ext i; unfold realm_C; rw [mem_filter,mem_filter]; refine ⟨fun ⟨x,h⟩=>⟨x,fun a ha b hb k=>h ha hb ((G a b).mpr k)⟩,fun ⟨x,h⟩=>⟨x,fun a ha b hb k=>h ha hb ((G a b).mp k)⟩⟩
 have he:∀ i∈realm_C t,gemI T i=M (gemI W i):=by
    intro i x; have h:=Ūm t x; have h':=Ūm τ (hu ▸ x); unfold gemI; unfold W T; rw [(Hatch_part σ t C p u _ h).2,(Hatch_part ρ τ A q v _ h').2]; exact Darboux σ t C ρ τ A p q M u v h h' (e.mono fun _ x _=> x)
 let z':Key J:=Q ∘ z
 rw [show T (Q ∘ z)= _ from congrFun (hT.cost ..) z',show W z=_ from congrFun (hW.cost ..) z]; unfold palm_R seedΞ; rw [map_sum,←hu]; exact sum_congr rfl fun i x=>by rw [H,he _ x,show pine i z'= Q (pine i z) from (map_prod Q _ _).symm]
variable (B_I:I→ I→ℂ)(B_K:K→ K→ℂ)
variable (C0:J→Key I)(A0:J→Key K)
omit p u q v G H in
lemma by_column(C:K→K→ℂ) (D:J→Key K)(W:J→Key K)(r:∀ i,toV_C ρ C (D i)=W i)(z:Key J): toV_C ρ C (SpotQ D z)=SpotQ W z:=by
 funext i; unfold toV_C SpotQ; simp_rw [Finset.sum_apply, Pi.smul_apply,smul_eq_mul,mul_sum]; rw [sum_comm]; refine sum_congr rfl fun j p=>?_ ; rw [←r j,toV_C,mul_sum]; exact sum_congr rfl fun x _=>mul_left_comm ..
lemma Voyage (e:∀ᶠ x:J→ℝ in 𝓝 0,g (LegQ A x)=M (f (LegQ C x))) (pV:∀ i,toV_C σ B_I (C0 i)=C i)(pW:∀ i,toV_C ρ B_K (A0 i)= A i)(z:Key J): Fluid ρ (streamArc g ρ B_K) (SpotQ A0 (Q ∘ z)) = M (Fluid σ (streamArc f σ B_I) (SpotQ C0 z)):=by
 rw [Stem_P,Stem_P,Function.comp_apply,Function.comp_apply, by_column _ _ _ _ pW, by_column _ _ _ _ pV]; exact Assembly σ t C ρ τ A p q u v G M Q H e z -- tune columns. omit params in by_column
#print axioms Voyage
end YM.CF.Roots.Connect
end
