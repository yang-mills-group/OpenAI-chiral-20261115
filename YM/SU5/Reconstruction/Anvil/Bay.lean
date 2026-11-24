import YM.SU5.Reconstruction.Anvil.Overture
/-! # Contour into Mink spacelike locality budget censorship. Uses angularly changing availability of actual axis budgets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Metric Filter Finset
open scoped Topology BigOperators
variable {ι κ:Type*} [Fintype ι][DecidableEq ι] [Fintype κ][DecidableEq κ]
lemma compensates (e:ι≃κ)(i:ι)(f:κ→ℝ): ∑ k∈Finset.univ.erase i,f (e k) = ∑ k∈ Finset.univ.erase (e i),f k:= Finset.sum_equiv e (by simp) (fun _ _=>rfl)
private lemma loosen {x y a b:ℝ}(h:x^2=y^2+b)(v:0≤x)(e:0<a)(t:ℝ)(p:|t|≤1): (t*y)^2+b<(x+a)^2:= by
 calc
   _ ≤ y^2+b:= by rw [mul_pow]; gcongr; have u:t^2 ≤1:=( sq_le_one_iff_abs_le_one t).mpr p; nlinarith [sq_nonneg y] -- tune
   _ < _ := by rw [←h]; nlinarith
-- φ includes minus i in phase/time origin. Cost ℝ, preserves polarity for both signs.
structure Festum (x:ι→ℝ) (t:ℝ) where
  φ : ℂ→ℂ
  g : ι→ℂ→ℂ
  atBase : φ 0= -(t:ℂ)*Complex.I
  at_place (i:ι): g i 0=x i
  enters {z:ℂ}(u:z∈Pane): ContinuousAt φ z ∧ ∀ i,ContinuousAt (g i) z
  hol {z:ℂ}(u:z∈Well): DifferentiableAt ℂ φ z ∧ ∀ i,DifferentiableAt ℂ (g i) z
  relies (z:ℂ)(p:z∈Rim):∃ i, 0 < (g i z).re ∧ (φ z).im^2+ ∑ j∈ Finset.univ.erase i, (g j z).im^2<(g i z).re^2
private lemma verse {n:ℕ}[Nontrivial (Spin n)] (x:Spin n→ℝ)(T:ℝ)(p:T^2<∑ i,x i^2)(u:∀ i,0<x i): Nonempty (Festum x T) := by
 let t:= Real.sqrt (∑ i,x i^2); have ht:0<t:= Real.sqrt_pos.mpr ((sq_nonneg T).trans_lt p); have hq:(∑ i,x i^2)=t^2:= (Real.sq_sqrt ((sq_nonneg T).trans p.le)).symm; have e:|T|<t:= lt_of_pow_lt_pow_left₀ _ ht.le (by rwa [sq_abs,←hq]) -- implicit
 let R:=(t+|T|)/2; have hp:|T|<R:=by unfold R; linarith; -- newline
 have hv:0<R:=(abs_nonneg T).trans_lt hp
 let A(i:Spin n):=x i/t; have s (i):0<A i:=div_pos (u i) ht
 have hS: ∑ i,A i^2=1:=by simp only [A,div_pow,← Finset.sum_div,hq]; rw [div_self (by positivity)]
 let d(i:Spin n):= x i-R*A i; have hd i:0<d i:= by
     unfold d; have H:R<t:=by unfold R; linarith; --
     have hx:x i=t*A i:=by unfold A; field_simp
     nlinarith only [H,s i,hx]
 obtain ⟨f,rho,g,b,r⟩:= archPrice (fun i=> A i^2) (fun i=> pow_pos (s _) _); let C: Score n:= ⟨f,fun i=>(r i).1,b⟩
 obtain ⟨U,v,g⟩:= mistress C.post C.post_rim C.distinct_post
 let G:=C.glisten U A R; let F:= C.siesta U R; let k:= -T/R; let φ (z:ℂ) := (k:ℂ)*F z*Complex.I; have hk: |k|≤1:= by unfold k; rw [abs_div,abs_neg, abs_of_pos hv]; exact (div_le_one hv|>.mpr hp.le)
 refine ⟨φ,fun i z=> G i z+(d i:ℂ), by unfold φ k F; rw [C.siesta_zero]; push_cast; have ht:(R:ℂ)≠0:= Complex.ofReal_ne_zero.mpr hv.ne'; field_simp, fun i=>by unfold G d; rw [C.glisten_zero]; push_cast; ring, fun {z} c=> ?_,fun {z} c=> ?_,?_⟩
 · exact ⟨(continuousAt_const.mul (C.siesta_cont U v R c)).mul continuousAt_const,fun i=> (C.glisten_cont U v A R i c).add continuousAt_const⟩
 · exact ⟨((differentiableAt_const _).mul (C.siesta_hol U v R c)).mul (differentiableAt_const _),fun i=> (C.glisten_hol U v A R i c).add (differentiableAt_const _)⟩
 intro z c; obtain ⟨i,h,h'⟩:= C.bountiful U v A R rho (fun i=> (r i).2) hS s hv (fun z zA=>g z (sphere_subset_closedBall zA)) c
 refine ⟨i,?_,?_⟩; · simp only [Complex.add_re,Complex.ofReal_re]; exact add_pos_of_nonneg_of_pos h (hd _)
 simp only [φ,Complex.mul_I_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,Complex.add_re,add_zero,zero_mul,sub_zero]; exact loosen h' h (hd i) k hk

def Festum.move {x: κ→ℝ} {t:ℝ} (C:Festum x t)(e:ι≃κ) : Festum (x∘e) t where
  φ:= C.φ
  g:= fun i=> C.g (e i)
  atBase:=C.atBase
  at_place(i):= C.at_place (e i)
  enters {z} v := ⟨(C.enters v).1,fun i=> (C.enters v).2 _⟩
  hol {z} v:= ⟨(C.hol v).1,fun i=> (C.hol v).2 _⟩
  relies z v:= by
    obtain ⟨i,v,h⟩ := C.relies z v; refine ⟨e.symm i,by simpa using v,?_⟩; rw [compensates e _ (fun j=> (C.g j z).im^2),e.apply_symm_apply]; exact h

lemma put_in_place (x:ι→ℝ)(t:ℝ)(p:t^2< ∑ i,x i^2)(u:∀ i,0<x i): Nonempty (Festum x t):= by
  cases isEmpty_or_nonempty ι with
  | inl y=> have g:t^2<0:= (by simpa using p); exact False.elim (lt_irrefl 0 ((sq_nonneg t).trans_lt g))
  | inr y=>
   cases subsingleton_or_nontrivial ι with
   | inl h=>
     inhabit ι
     refine ⟨fun _=> -(t:ℂ)*Complex.I,fun i _=> x i,rfl,fun _=>rfl,fun {z} h=> ⟨continuousAt_const,fun _=>continuousAt_const⟩,fun {z} h=> ⟨differentiableAt_const _,fun _=> differentiableAt_const _⟩,fun z h=>?_⟩
     refine ⟨default,u _,?_⟩; have v:t^2<x default^2:= Finset.sum_eq_single (f:=fun i=> x i^2) (s:= Finset.univ) default (fun b _ h=> False.elim (h (Subsingleton.elim ..))) (by simp) ▸ p
     simpa
   | inr h=>
     obtain ⟨n,g⟩:∃ n:ℕ,Fintype.card ι=n+1:=by have h':= Fintype.card_pos (α:=ι); exact ⟨Fintype.card ι -1, Eq.symm (Nat.sub_add_cancel h')⟩
     let e:= (Fintype.equivFin ι).trans (finCongr g); letI:= Function.Injective.nontrivial e.injective -- wrong: injective yields
     obtain ⟨T⟩:= verse (x∘⇑e.symm) t (by simp only [Function.comp_apply]; rw [Equiv.sum_comp e.symm (fun i=> x i^2)]; exact p) (fun i=> u _)
     rw [show x=(x∘⇑e.symm)∘⇑e from funext fun i=> by simp]; exact ⟨T.move e⟩
end YM.Anvil
