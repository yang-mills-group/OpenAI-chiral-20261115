import GaugeFieldConstruction.VialP
import GaugeFieldConstruction.Verdant
import GaugeFieldConstruction.Ventana
import GaugeFieldConstruction.Viridian
import GaugeFieldConstruction.Valle
import GaugeFieldConstruction.Canone
import GaugeFieldConstruction.Tropic
import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open Fock
variable (P:Spine)
open MeasureTheory
open Afterglow -- tune
local notation "Ω"=>P.floorVec
-- Alternative Porch gives linear itself for all tests fit BEntry.B.Q. Thus prove for any p.H3 and shift stamp.
variable {P}
open Papal Papal.FrameP
open CF.XGarden CF.XGarden.MastTin ArtCart
open RG Fock CF.Rush Vale Branch Fock.Flux Tapestry
open YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open RG CF.Skye
open CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open scoped YM.CF.Mew
open CF.TableF TableF.Lenten TableF.Lenten.Layout Py
variable {P:Spine}{S:Finset Cover}{f:P.Test}{F:ℕ→Buffered.Family P.calibration}

open Py.Rate Py.Rate.LocalLimit.Papal Fock.Flux Zpress
open Violets BluffV BluffV.Lave
namespace Heritor
variable (R:P.Heritor)
-- Phys budget for scaled patterns. sequences on Cover.Actors varying roots/times. finite integer.A. margin

open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick
open YM.GaugeFieldConstruction.Cauchy -- tune
open YM.GaugeFieldConstruction -- tune
open SpaΘ
-- Use absolute plenum version; R3 may use after translating poses about tile grid.
open YM.GaugeFieldConstruction.Calibration
variable (Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u: TintDemand)(H: LicensedHeight (tagged_B Q) t u P.par)
private structure heel (c d:ℝ)(z w:ℂ):Prop where
  value : ‖w‖≤c
  gap : ‖z-w‖≤d
private lemma heel.product {a b c d:ℝ}{X Y Z T:ℂ}(h:heel a b X Y)(p:heel c d Z T): heel (a*c) (b*c+(a+b)*d) (X*Z) (Y*T):=by
 have hv:0≤a:=(norm_nonneg Y).trans h.1
 have ht: ‖X‖≤a+b:= (norm_le_norm_add_norm_sub' ..).trans (add_le_add h.1 h.2) -- tune order
 constructor; · rw [norm_mul]; exact mul_le_mul h.1 p.1 (norm_nonneg _) hv
 rw [show X*Z-Y*T=(X-Y)*T+X*(Z-T) by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul h.2 p.1 (norm_nonneg _) ((norm_nonneg _).trans h.2)) (mul_le_mul ht p.2 (norm_nonneg _) ((norm_nonneg _).trans ht))
private lemma heel.sub {a b c d:ℝ}{X Y Z T:ℂ}(h:heel a b X Y)(p:heel c d Z T) : heel (a+c) (b+d) (X-Z) (Y-T):=by
 refine ⟨(norm_sub_le ..).trans (add_le_add h.1 p.1),?_⟩; rw [sub_sub_sub_comm]; apply (norm_sub_le ..).trans (add_le_add h.2 p.2)
private lemma heel.add {a b c d:ℝ}{X Y Z T:ℂ}(h:heel a b X Y)(p:heel c d Z T): heel (a+c) (b+d) (X+Z) (Y+T):=by
 refine ⟨(norm_add_le ..).trans (add_le_add h.1 p.1),?_⟩; rw [add_sub_add_comm]; apply (norm_add_le ..).trans (add_le_add h.2 p.2)
private lemma heel.double {a b:ℝ}{X Y:ℂ}(h:heel a b X Y):heel (a+a) (b+b) (2*X) (2*Y):=by rw [two_mul,two_mul]; exact h.add h

variable {T:ℝ→ℝ}{p f:ℝ}{s:ℕ→ℕ}{v:ℕ→ℝ}
private lemma cutErr(x:ℕ→ℂ)(C D:ℝ→ℝ) {e:ℝ}(p0: RunRate e f C)(pe:e<0)(w:RunRate 0 p D)(hs:Tendsto s atTop atTop)(h:∀ᶠ i:ℕ in atTop,‖x i‖≤ C (P.urnMark (s i)))(t:∀ᶠ i:ℕ in atTop,0<v i∧1/v i≤ D (P.urnMark (s i)))(n:ℕ):Tendsto (fun i=>x i/(v i:ℂ)^n) atTop (𝓝 0):=by
 let W:=P.urnMark; let F:=fun z=> C z*D z^n
 have hx:Tendsto F atTop (𝓝 0):=(p0.mul (w.pow n)).tends (Or.inl (by rw [zero_mul,add_zero]; exact pe))
 rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (g:=fun i=>F (W (s i))) (Eventually.of_forall fun i=>norm_nonneg _) ?_ (hx.comp ((Py.Rate.LocalLimit.turnover _).comp hs))
 filter_upwards [h,t] with i h t; obtain ⟨hp,p'⟩:=t
 rw[norm_div,norm_pow,Complex.norm_real, Real.norm_eq_abs,abs_of_pos hp,div_eq_mul_inv, ← inv_pow]
 refine mul_le_mul h (pow_le_pow_left₀ (inv_pos.mpr hp).le ?_ n) (by positivity) ((norm_nonneg _).trans h); simpa only [one_div] using p'


open Phys
local notation "ζκ" s:max L:max i:max=> R.registerAt s L i
local notation "ψ"=> callE
private lemma Cmño :RunRate (-callE/16) 0 (fun x=>3*ClockTurn x):= RunRate.cmul (RunRate.coins ..) _
-- StampM. Slots named at any mesh center. bound cost.Support raw uses count path.
def PointPeek (V:Genre)(q:Waves)(x:ℕ → Cover) (s:ℕ): AdmitA:= (x s,V,q)
include H
theorem tunnel_2 {a b:Waves}{F A:GaugeFieldConstruction.Calibration.Floor}{Z U: Genre}{x y:E4}{J K:ℕ → Cover} (ratura:Tendsto s atTop atTop)(p0:RunRate 0 p T)
 (ts:Tendsto v atTop (𝓝 0))(g:∀ᶠ i:ℕ in atTop,0<v i∧ 1 / v i ≤ T (P.urnMark (s i)))
 (xP:Tendsto (fun i=> mount (v i) (J i)) atTop (𝓝 x))(yP:Tendsto (fun i=> mount (v i) (K i)) atTop (𝓝 y))(e:x≠y)(uX:HomΓ Z F a)(uY:HomΓ U A b)
 (cost:ℕ → ℕ→P.Test→ℂ)(Y:ℕ→Axis)(p:∀ i, Porch P (cost i) (Y i)): let W:= PointPeek Z a J; let L:=PointPeek U b K
 Tendsto (fun i=>moneyDuo (fun j=>cost i (s i) (R.poseFont (s i) j)) (W i) (L i)/ (v i:ℂ)^(aptC F+aptC A)) atTop (𝓝 (BigP x y (Phys.dress (SpineM a)) (Phys.dress (SpineM b)))):=by
 intro X L; let I(i): List AdmitA:=[X i,L i]; let r:ℝ:= ‖a‖+‖b‖

 have hv:∀ᶠ i:ℕ in atTop,∀ a ∈I i, issueA r a :=by
    exact Eventually.of_forall fun i u p=> by
      rcases (show u=X i∨ u=L i from (by simpa [I] using p)) with v|v
      · rw[v]; exact ⟨uX.1,le_add_of_nonneg_right (norm_nonneg b)⟩
      rw[v]; exact ⟨uY.1,le_add_of_nonneg_left (norm_nonneg a)⟩
 have hh:∃ K>0,∀ᶠ i:ℕ in atTop,∀ a∈I i,∀ j:Axis,|v i*(a.1 j:ℝ)|≤K:=by
            obtain ⟨D,t,v⟩:= PoseUp (A:=X) xP; obtain ⟨Y,t',r⟩:=PoseUp (A:=L) yP
            refine ⟨D+Y,add_pos t t',?_⟩; filter_upwards [v,r] with i h h' u p q; rcases (show u=X i∨u=L i from by simpa [I] using p) with v|v <;> rw[v]; exact (h q).trans (le_add_of_nonneg_right t'.le); exact (h' q).trans (le_add_of_nonneg_left t.le)
 obtain ⟨D,Pf,D',τ⟩:=chartline P p0 ratura ts g 2 r I (Eventually.of_forall fun i=>le_rfl) hv hh
 obtain ⟨c,C,V⟩:= R.knockκ 2 r (by unfold r; positivity) Q t u H D D'
 let α(x):ℝ:=3*ClockTurn x; let H₀:=P.urnMark ∘ s
 let S(x):ℝ:=α x+ (α x*c x+(c x+α x)*α x)+α x
 let Z₀(i)(A:List AdmitA):=cost i (s i) (R.poseFont (s i) A)
 let V₀(i)(j):= paidν P (s i) (R.path.subSeq j)
 let φ(i)(j):= quotaZ (V₀ i j (X i)) (V₀ i j (L i)) κg κF
 let F₀(i):=moneyDuo (Z₀ i) (X i) (L i)
 have he:∀ᶠ i:ℕ in atTop, ∃ j, ‖F₀ i - φ i j‖ ≤ S (H₀ i):=by
    filter_upwards [τ, ratura.eventually V, strict_EP (N:=Reifier) (A:=X) (B:=L) e xP yP ts] with i T' w r
    have q(L':List AdmitA)(v:L' ⊆ I i)(q:L'.length≤2):∀ᶠ j:ℕ in atTop, heel (c (H₀ i)) (α (H₀ i)) (Z₀ i L') (ζκ (s i) L' j):= (w L' (Y i) (chartSat (T' (Y i)) v q) (cost i) (p i)).mono fun i h=> ⟨h.1,h.2⟩ -- tune
    let K(j)(L':List AdmitA):= ζκ (s i) L' j
    have H:= R.seatDuo (s i) (X i) (L i) uX.1 uY.1 r
    have ht:0<α (H₀ i):=mul_pos (by norm_num) (BProof.coin_pos ..)
    obtain ⟨j,a,b,c,h'⟩:= ((q (I i) (List.Subset.refl _) le_rfl).and ((q [X i] (by simp [I]) (by simp)).and ((q [L i] (by simp [I]) (by simp)).and (H.norm.eventually (ge_mem_nhds (by rewrite [norm_zero]; exact ht)))))).exists
    have hx:= (a.sub (b.product c)).gap
    exact ⟨j,(norm_sub_le_norm_sub_add_norm_sub (F₀ i) (moneyDuo (K j) (X i) (L i)) (φ i j)).trans (add_le_add hx (by simpa only [norm_zero] using h'))⟩
 let E(i j:ℕ):Prop:=‖F₀ i- φ i j‖≤ S (H₀ i); classical
 let W i:= if p:∃ j,E i j then Classical.choose p else 0
 let D i:= (v i:ℂ)^(aptC F+aptC A); let Q i:=F₀ i- φ i (W i)
 have hv: RunRate (-callE/16) 20 S:=by
    have h:RunRate 0 4 c:=by convert C using 1; norm_num
    let F:=Cmño.mul h; let W:RunRate (-callE/16) 4 (fun x=>(c x+α x)*α x):=by simpa using ((h.add (Cmño.relax (u':=4) (by norm_num [callE,gratuity]))).mul Cmño)
    let R:= (show RunRate (-callE/16) 4 (fun x=>α x*c x) by simpa [α] using F).add W; exact ((Cmño.weaker (Or.inr ⟨rfl,by norm_num⟩)).add (R.weaker (Or.inr ⟨rfl,by norm_num⟩))).add (Cmño.weaker (Or.inr ⟨rfl,by norm_num⟩))
 have pD:Tendsto (fun i=>Q i/D i) atTop (𝓝 0):= cutErr Q S _ hv (by norm_num [callE,gratuity]) p0 ratura (he.mono fun i h=> (show E i (W i) from by unfold W; rw [dif_pos h]; exact Classical.choose_spec h)) g (aptC F+aptC A)
 let T'(x:ℕ → AdmitA)(i:ℕ):=V₀ i (W i) (x i)
 have hh:Tendsto (fun i=> φ i (W i)/ D i) atTop (𝓝 (BigP x y (Phys.dress (SpineM a)) (Phys.dress (SpineM b)))):=
    optic_2 liquid (show InVein (T' X) F Z a from ⟨uX,fun i=> ⟨P.MaleBook _ _,P.penIt (s i),_,(P.billStamp _).2,(P.billStamp _).1,zero_lt_one.trans_le P.par.height,rfl⟩⟩) ts (g.mono fun i p=>p.1) xP
      (show InVein (T' L) A U b from ⟨uY,fun i=>⟨P.MaleBook _ _,P.penIt (s i),_,(P.billStamp _).2,(P.billStamp _).1,zero_lt_one.trans_le P.par.height,rfl⟩⟩) yP e
 have h:= pD.add hh; rw [zero_add] at h; refine h.congr (fun i=>?_); change (_-_)/_+_/_=F₀ i/_; rw [←add_div, sub_add_cancel]
#print axioms tunnel_2
theorem tunnel_3 {a b c':Waves}{F A A₀:GaugeFieldConstruction.Calibration.Floor}{Z U M: Genre}{x y z:E4}{J K J₀:ℕ → Cover} (ratura:Tendsto s atTop atTop)(p0:RunRate 0 p T)
 (ts:Tendsto v atTop (𝓝 0))(g:∀ᶠ i:ℕ in atTop,0<v i∧ 1 / v i ≤ T (P.urnMark (s i)))
 (xP:Tendsto (fun i=> mount (v i) (J i)) atTop (𝓝 x))(yP:Tendsto (fun i=> mount (v i) (K i)) atTop (𝓝 y))(e:x≠y)(uX:HomΓ Z F a)(uY:HomΓ U A b)
 (zP:Tendsto (fun i=> mount (v i) (J₀ i)) atTop (𝓝 z))(pX:x≠z)(pY:y≠z)(uZ:HomΓ M A₀ c')(zG:Z ≠ Genre.mixed)
 (cost:ℕ → ℕ→P.Test→ℂ)(Y:ℕ→Axis)(p:∀ i, Porch P (cost i) (Y i)): let W:= PointPeek Z a J; let L:=PointPeek U b K; let G:=PointPeek M c' J₀
 Tendsto (fun i=>moneyTrois (fun j=>cost i (s i) (R.poseFont (s i) j)) (W i) (L i) (G i)/ (v i:ℂ)^(aptC F+aptC A+aptC A₀)) atTop (𝓝 (Flux.One.prism x y z (Phys.dress (SpineM a)) (Phys.dress (SpineM b)) (Phys.dress (SpineM c')))):=by
 intro X L G; let I(i): List AdmitA:=[X i,L i,G i]; let r:ℝ:= ‖a‖+‖b‖+‖c'‖

 have hv:∀ᶠ i:ℕ in atTop,∀ a ∈I i, issueA r a :=by
    exact Eventually.of_forall fun i u p=> by
      rcases (show u=X i ∨ u=L i ∨ u=G i from (by simpa [I] using p)) with u|u|u
      · rw [u]; exact ⟨uX.1,(le_add_of_nonneg_right (norm_nonneg b)).trans (le_add_of_nonneg_right (norm_nonneg c'))⟩
      · rw [u]; exact ⟨uY.1,(le_add_of_nonneg_left (norm_nonneg a)).trans (le_add_of_nonneg_right (norm_nonneg c'))⟩
      rw[u]; exact ⟨uZ.1,le_add_of_nonneg_left (add_nonneg (norm_nonneg a) (norm_nonneg b))⟩
 have hh:∃ K>0,∀ᶠ i:ℕ in atTop,∀ a∈I i,∀ j:Axis,|v i*(a.1 j:ℝ)|≤K:=by
    obtain ⟨D,t,v⟩:= PoseUp (A:=X) xP; obtain ⟨Y,t',r⟩:=PoseUp (A:=L) yP; obtain ⟨U,p,v'⟩:=PoseUp (A:=G) zP
    refine ⟨D+Y+U, by linarith only [t,t',p],?_⟩; filter_upwards [v,r,v'] with i h h' k u e q
    rcases (show u=X i∨u=L i∨u=G i from by simpa [I] using e) with v|v|v <;> rw[v]
    · exact (h q).trans (by linarith only [t',p])
    · exact (h' q).trans (by linarith only [t,p])
    exact (k q).trans (by linarith only [t,t'])
 obtain ⟨D,Pf,D',τ⟩:=chartline P p0 ratura ts g 3 r I (Eventually.of_forall fun _=>le_rfl) hv hh
 obtain ⟨c,C,V⟩:= R.knockκ 3 r (by unfold r; positivity) Q t u H D D'
 let α(x):ℝ:=3*ClockTurn x; let H₀:=P.urnMark ∘ s
 let Mx(x):=α x * c x + (c x+α x)*α x; let Kx(x):=Mx x*c x + (c x * c x+Mx x)*α x
 let S(x):ℝ:=α x+Mx x+ Mx x+Mx x + (Kx x+ Kx x) + α x
 let Z₀(i)(A:List AdmitA):=cost i (s i) (R.poseFont (s i) A)
 let V₀(i)(j):= paidν P (s i) (R.path.subSeq j)
 let φ(i)(j):= quotas (V₀ i j (X i)) (V₀ i j (L i)) (V₀ i j (G i)) κg κF
 let F₀(i):=moneyTrois (Z₀ i) (X i) (L i) (G i)
 have he:∀ᶠ i:ℕ in atTop, ∃ j, ‖F₀ i - φ i j‖ ≤ S (H₀ i):=by
    filter_upwards [τ, ratura.eventually V, strict_EP (N:=Reifier) (A:=X) (B:=L) e xP yP ts,strict_EP (N:=Reifier) (A:=X) (B:=G) pX xP zP ts,strict_EP (N:=Reifier) (A:=L) (B:=G) pY yP zP ts] with i T' w r r' hq
    have q(L':List AdmitA)(v:L' ⊆ I i)(q:L'.length≤3):∀ᶠ j:ℕ in atTop, heel (c (H₀ i)) (α (H₀ i)) (Z₀ i L') (ζκ (s i) L' j):= (w L' (Y i) (chartSat (T' (Y i)) v q) (cost i) (p i)).mono fun i h=> ⟨h.1,h.2⟩ -- tune
    let K(j)(L':List AdmitA):= ζκ (s i) L' j
    have H:= R.seatTrois (s i) (X i) (L i) (G i) uX.1 uY.1 uZ.1 r r' hq zG
    have ht:0<α (H₀ i):=mul_pos (by norm_num) (BProof.coin_pos ..)
    have hp:= H.norm.eventually (ge_mem_nhds (by rw [norm_zero]; exact ht))
    obtain ⟨j,a,b₁,b₂,b₃,c₁,c₂,c₃,h₄⟩:= ((q (I i) (fun _ k=> k) le_rfl).and ((q [X i,L i] (by simp [I, List.subset_def]) (by simp)).and ((q [X i,G i] (by simp [I,List.subset_def]) (by simp)).and ((q [L i,G i] (by simp [I,List.subset_def]) (by simp)).and ((q [X i] (by simp [I]) (by simp)).and ((q [L i] (by simp [I]) (by simp)).and ((q [G i] (by simp [I]) (by simp)).and hp))))))).exists
    have hx:= (((a.sub (b₁.product c₃)).sub (b₂.product c₂)).sub (b₃.product c₁)).add (((c₁.product c₂).product c₃).double)|>.gap
    simp_rw [← _root_.mul_assoc] at hx
    exact ⟨j,(norm_sub_le_norm_sub_add_norm_sub (F₀ i) (moneyTrois (K j) (X i) (L i) (G i)) (φ i j)).trans (add_le_add (by unfold Kx Mx F₀ moneyTrois; exact hx) h₄)⟩
 let E(i j:ℕ):Prop:=‖F₀ i- φ i j‖≤ S (H₀ i); classical
 let W i:= if p:∃ j,E i j then Classical.choose p else 0
 let D i:= (v i:ℂ)^(aptC F+aptC A+aptC A₀); let Q i:=F₀ i- φ i (W i)
 have hv: RunRate (-callE/16) 20 S:=by
    have h:RunRate 0 6 c:=by convert C using 1; norm_num
    let S₀:= -callE/16; have v:S₀<0:=by norm_num[S₀,callE,gratuity]
    let F:=Cmño.mul h; let W:RunRate S₀ 6 (fun x=>(c x+α x)*α x):=by simpa using ((h.add (Cmño.relax (u':=6) v)).mul Cmño)
    have r:RunRate S₀ 6 Mx:= RunRate.add (by unfold S₀; simpa [α] using F) W
    have k: RunRate S₀ 12 Kx:=RunRate.add (by convert r.mul h using 1; simp; norm_num) (by
       have hp:RunRate 0 12 (fun x=> c x*c x):=by convert h.mul h using 1; ring; norm_num
       simpa [S₀] using (hp.add (r.relax (u':=12) v)).mul Cmño)
    have hp:RunRate S₀ 20 Mx:=r.weaker (Or.inr ⟨rfl,by norm_num⟩); have hK:RunRate S₀ 20 Kx:=k.weaker (Or.inr ⟨rfl,by norm_num⟩); let q:RunRate S₀ 20 α:=Cmño.weaker (Or.inr ⟨rfl,by norm_num⟩); exact (((((q.add hp).add hp).add hp).add (hK.add hK)).add q)

 have pD:Tendsto (fun i=>Q i/D i) atTop (𝓝 0):= cutErr Q S _ hv (by norm_num [callE,gratuity]) p0 ratura (he.mono fun i h=> (show E i (W i) from by unfold W; rw [dif_pos h]; exact Classical.choose_spec h)) g (aptC F+aptC A+aptC A₀)
 let T'(x:ℕ → AdmitA)(i:ℕ):=V₀ i (W i) (x i)
 have hh:Tendsto (fun i=> φ i (W i)/ D i) atTop (𝓝 (Flux.One.prism x y z (Phys.dress (SpineM a)) (Phys.dress (SpineM b)) (Phys.dress (SpineM c')))):=
    optic_3 liquid (show InVein (T' X) F Z a from ⟨uX,fun i=> ⟨P.MaleBook _ _,P.penIt (s i),_,(P.billStamp _).2,(P.billStamp _).1,zero_lt_one.trans_le P.par.height,rfl⟩⟩) ts (g.mono fun i p=>p.1) xP
      (show InVein (T' L) A U b from ⟨uY,fun i=>⟨P.MaleBook _ _,P.penIt (s i),_,(P.billStamp _).2,(P.billStamp _).1,zero_lt_one.trans_le P.par.height,rfl⟩⟩) yP e (show InVein (T' G) A₀ M c' from ⟨uZ,fun i=>⟨P.MaleBook _ _,P.penIt (s i),_,(P.billStamp _).2,(P.billStamp _).1,zero_lt_one.trans_le P.par.height,rfl⟩⟩) zP pX pY zG
 have h:= pD.add hh; rw [zero_add] at h; refine h.congr (fun i=>?_); change (_-_)/_+_/_=F₀ i/_; rw [←add_div, sub_add_cancel]
#print axioms tunnel_3
end Heritor
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
