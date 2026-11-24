import Merino.JadeEye.Dup
import Merino.Cuff.Kerf

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
open AnalyticBridge.Merino Cuff
variable {d b a C r : ℝ} {o:Seat n}
local notation "A"=>Openc (More n) d
local notation "M"=> (↥(Openc (More n) d))
abbrev filer(d:ℝ)(F:SOp n) : Openc (More n) d → ℂ:=fun t=>(F t.val).trace

lemma aging {F:SOp n}(h:Soak o F a b d): Looks A (filer d F):=by
 obtain ⟨R,W,p,t,u,v⟩:=h
 intro V hv γ dγ
 change DifferentiableOn ℂ (fun z=>(F (γ z).val).trace) V
 simp_rw [v,Matrix.trace_sum]
 rw [←Finset.sum_fn (g:=fun i z=>(R i (γ z)).trace)]
 apply DifferentiableOn.sum
 intro S _
 change DifferentiableOn ℂ (fun z=>∑ i, R S (γ z) i i) V
 rw [← Finset.sum_fn (g:=fun i z=>R S (γ z) i i)]
 exact DifferentiableOn.sum fun i _=>(p S).fuel i i _ hv _ dγ


lemma age {F:SOp n}(h:Soak o F a b d)(T:Room d r C)(p:0≤a){x:Duo n}(v:‖x‖≤r):
   Jet.Allows 6 (glint (filer d F)) x (b*C):=
 T.pay _ _ (aging h) (soak_cont h).matrix_trace (fun t=>soak_trace h t p) v

/- General result for a globally gauge invariant function. -/
lemma pace (J:Pane n→ℂ)(p:∀ g U,J (gauge g U)=J U)
   (q:ContDiffAt ℝ 2 (J ∘ dyeB n) 0): fderiv ℝ (J ∘ dyeB n) 0=0:= by
 have l (L:ℂ→L[ℝ]ℝ): fderiv ℝ (L ∘ (J ∘ dyeB n)) 0=0:=
   flat_critical Thera.yet_one (f:=L ∘ J) ⟨fun g U=> congrArg L (p g U), L.contDiff.contDiffAt.comp 0 q⟩
 have h(L)(v): (L:ℂ→L[ℝ]ℝ) (fderiv ℝ (J ∘ dyeB n) 0 v)=0:=by
   have e:=l L
   rw [fderiv_comp _ L.differentiableAt (q.differentiableAt (by norm_num)),L.fderiv] at e
   exact congr($e v)
 exact ContinuousLinearMap.ext fun v=>Complex.ext (h Complex.reCLM v) (h Complex.imCLM v)


lemma duo_pace (J:Pane n→ℂ)(p:∀ g U,J (gauge g U)=J U)
   (q:ContDiffAt ℝ 2 (J ∘ du n) 0): fderiv ℝ (J ∘ du n) 0=0:=by
 let I:=ContinuousLinearMap.inl ℝ (Bows n) (Bows n)
 let A':=ContinuousLinearMap.inr ℝ (Bows n) (Bows n)
 have r:(J ∘ du n) ∘ I=J ∘ dyeB n:=by
    funext x; change J (increment _ 0)=_; rw [at_zero];rfl
 have s:(J ∘ du n) ∘ A'=J ∘ dyeB n:=by
    funext x; change J (increment (increment 1 0) x)=_; rw [at_zero];rfl
 have u:ContDiffAt ℝ 2 (J ∘ dyeB n) 0:=by
    rw [← r];exact ((I.map_zero.symm ▸ q).comp _ I.contDiff.contDiffAt)
 have h (L:Bows n→L[ℝ]Duo n)(v)(k:(J ∘ du n) ∘ L=J ∘ dyeB n):
      fderiv ℝ (J ∘ du n) 0 (L v)=0:=by
    have e:=pace J p u
    rw [← k, fderiv_comp _ (by rw [map_zero]; exact q.differentiableAt (by norm_num)) L.differentiableAt,
      L.map_zero,L.fderiv] at e
    exact congr($e v)
 exact ContinuousLinearMap.ext fun ⟨x,y⟩=>by
    have f:(x,y)=I x+A' y:=by simp [I,A']
    rw [f,map_add,h I x r,h A' y s,zero_add]
    rfl


lemma young {F:SOp n}(h:Soak o F a b d)(T:Room d r C)(p:0≤a):
 fderiv ℝ (glint (filer d F)) 0 = 0:=by
 let J:Pane n→ℂ:=fun U=>Jet.equalizer (filer d F) (profile U)
 have g:Jet.Allows 6 (J ∘ du n) 0 (b*C):=
    age h T p (by rw [norm_zero]; exact T.haveR.le)
 apply duo_pace J _ (g.smooth.of_le (by norm_num))
 intro v U
 by_cases hx:profile U∈A
 · unfold J
   rw [equalizer,dif_pos (open_frame hx v),equalizer,dif_pos hx]
   unfold filer
   let t:M:=⟨_,hx⟩
   change (F (profile (gauge v U))).trace=_

   rw [profile_g v U]
   change (F (rayG n d v t).val).trace=_
   rw [soak_frame h t v,trace_twist]
 have hy:profile (gauge v U)∉A:=by
     intro ht; apply hx; have hm:= open_frame ht v⁻¹
     have hf:gauge v⁻¹ (gauge v U)=U:=by
        funext e; simp [Lattice.gauge,mul_assoc]
     rwa [hf] at hm
 unfold J
 rw [equalizer,dif_neg hy,equalizer,dif_neg hx]

