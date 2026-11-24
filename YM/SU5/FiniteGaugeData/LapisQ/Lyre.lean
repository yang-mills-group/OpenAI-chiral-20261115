import YM.SU5.FiniteGaugeData.LapisQ.Blue
import YM.Next.STATIONARY.Lift.Ward
set_option autoImplicit false
set_option maxHeartbeats 580000
set_option synthInstance.maxSize 21000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Tulipe
open Vulcan Willow Nosh Cordon -- don't open Stationary
variable {α:Type} [Fintype α]
variable {n:Side} {ρ C Δ ε σ K:ℝ} [DecidableEq α]
local notation "W"=> Phase4
local notation "F" x:max=> Exterior.q x
variable (m:ℕ→Side) (v:Tendsto (fun i=>(m i).val) atTop atTop)
abbrev Melody(m:ℕ→Side):= ∀ i:ℕ, Site (m i)
variable (s s':Melody m)(x y:Phase4) (ℓ:ℕ)
def note(m:ℕ→Side)(s:Melody m)(x:Phase4):= Tendsto (fun p:ℕ=> Willow.harp (s p)) atTop (𝓝 (Exterior.q x))
@[fun_prop] private lemma score_c : Continuous Exterior.q:= continuous_pi (fun i=>by unfold Exterior.q; fun_prop)
include v in
lemma aria (he:star x=x): ∃ s: Melody m, note m s x := by
 obtain ⟨b,M,h,v⟩:= YM.Stationary.mesh_stride m v x he; refine ⟨b,(score_c.continuousAt.tendsto.comp h).congr' ?_⟩; refine Eventually.of_forall fun p=>?_ ; funext i; change Exterior.q (M p) i=Exterior.q (mon (b p)) i; unfold Exterior.q; rw [← Exterior.factor,←Exterior.factor,(v p).exp]
lemma h_order(z x:Site n)(i:Axis): harp (z+x) i+1=(harp z i+1)*(harp x i+1):=by simp_rw [harpC,sub_add_cancel,wave_shiftH]
lemma w_order(z x:Phase4)(i:Axis): Exterior.q (z+x) i+1=(Exterior.q z i+1)*(Exterior.q x i+1):=by simp only [Exterior.q,sub_add_cancel,Pi.add_apply,mul_add,Complex.exp_add]
lemma nOrder (u:note m s x)(p:note m s' y) : note m (s+s') (x+y):=by
 refine tendsto_pi_nhds.mpr fun i=>?_ ; have he(k:ℕ): harp ((s+s') k) i=(harp (s k) i+1)*(harp (s' k) i+1)-1:= eq_sub_of_add_eq (h_order ..) -- tune argument order
 simp_rw [he, show Exterior.q (x+y) i = _ from (eq_sub_of_add_eq (w_order x y i))]; exact (((tendsto_pi_nhds.mp u i).add tendsto_const_nhds).mul ((tendsto_pi_nhds.mp p i).add tendsto_const_nhds)).sub tendsto_const_nhds
abbrev pureW (c:ℂ)(a:Axis):Phase4:= Pi.single a c
@[fun_prop] lemma pureC(a:Axis): Continuous (fun c:ℂ=> pureW c a):=by refine continuous_pi (fun i=>?_); unfold pureW; by_cases he:i=a <;> simp [he,Pi.single_apply] <;> fun_prop
lemma p_order(s:Site n)(a:Axis): harp (periodU s a)= pureW (harp s a) a:=by
 funext i; by_cases he:i=a; · subst i; unfold harp Exterior.q pureW; simp [mon,reciprocal,Lattice.lift,periodU];
 unfold harp Exterior.q pureW; simp [mon,reciprocal,Lattice.lift,periodU,he]
lemma p_measure(a:Axis)(x:Phase4): Exterior.q (pureW (x a) a)= pureW (Exterior.q x a) a:=by
 funext i; by_cases he:i=a <;> simp [he,Exterior.q,pureW]
lemma p_note (j:Axis)(v:note m s x): note m (fun i=>periodU (s i) j) (pureW (x j) j):=by unfold note; simp_rw [p_order,p_measure]; exact (pureC j).continuousAt.tendsto.comp (tendsto_pi_nhds.mp v j)
lemma ideal0 : Exterior.q (0:Phase4)=0:=by funext i; simp [Exterior.q]
lemma p_zone : note m (fun _=>0) 0:=by unfold note harp; simp only [mon_zero,ideal0]; exact tendsto_const_nhds
lemma sum_notes(t:Finset α) (Z:α→ Melody m)(X:α→Phase4)(v:∀ i:α,note m (Z i) (X i)) : note m (∑ i∈t,Z i) (∑ i∈ t,X i):= by
 induction t using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact p_zone m
 | insert a s p u=> rw [sum_insert p, sum_insert p]; exact nOrder m _ _ _ _ (v a) u
abbrev rose (t:colorX ℓ)(x:Phase4):Phase4:= ∑ i∈t, pureW (x i.1) i.1
lemma leadR (p:note m s x)(t:colorX ℓ): note m (fun i=> shiftU (s i) ℓ t) (rose ℓ t x) :=by
 refine Eq.mp (congrArg (fun y=> note m y (rose ℓ t x)) (show (∑ i∈t, (fun j:ℕ=> periodU (s j) i.1))=(fun i=> shiftU (s i) ℓ t) from ?_)) (sum_notes m t _ (fun i:bandX ℓ=>pureW (x i.1) i.1) (fun i=>p_note m s x i.1 p))
 funext i; exact Finset.sum_apply ..
lemma grew (z:ℝ)(h:0<z)(p:z<Real.pi) : Complex.exp (Complex.I*(z:ℂ))-1≠0:=by
 refine sub_ne_zero.mpr (fun v=>?_); have hm:= congrArg Complex.im v; simp only [Complex.exp_im, Complex.mul_re,Complex.mul_im, Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im, zero_mul,mul_zero,sub_zero,zero_add,one_mul,Real.exp_zero,one_im] at hm; exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h p) hm
noncomputable abbrev uniformM (c:ℝ):Phase4:= fun _=> (c:ℂ)
noncomputable abbrev rung (r:ℝ)(a:Axis):Phase4:= pureW (r:ℂ) a
lemma uniform_MC : Continuous uniformM:=continuous_pi fun _=> Complex.continuous_ofReal
@[fun_prop] lemma rung_c(a:Axis): Continuous (fun x=>rung x a):=(pureC a).comp Complex.continuous_ofReal
lemma rung_0 (a:Axis):rung 0 a=0:=by unfold rung pureW; simp
abbrev mountain (t:colorX ℓ)(c:ℝ):= rose ℓ t (uniformM c)
@[fun_prop] lemma mountain_c (t:colorX ℓ): Continuous (mountain ℓ t):=by unfold mountain rose; fun_prop -- tune
lemma mountain0(t:colorX ℓ): mountain ℓ t 0=0:=by simp [mountain,rose,uniformM,pureW]
lemma tilt₁ (t:colorX ℓ)(u:t≠∅): ∀ᶠ x:ℝ in 𝓝[>] 0, Exterior.q (mountain ℓ t x)≠0:= by
 obtain ⟨a,b⟩:= Finset.nonempty_iff_ne_empty.mpr u; let w:= a.1; let v:= t.filter (fun i=>i.1=w); let A:ℝ:= v.card; have he(c:ℝ): mountain ℓ t c w= Complex.ofReal (A*c):=by
   unfold mountain rose pureW uniformM; simp_rw [Finset.sum_apply,Pi.single_apply]; -- condition `w=a`
   rw [← Finset.sum_filter,sum_const,nsmul_eq_mul]; unfold A v; push_cast; simp [eq_comm]
 have hp:0<A:=Nat.cast_pos.mpr (card_pos.mpr ⟨a, mem_filter.mpr ⟨b,rfl⟩⟩)
 have hh:Tendsto (fun x:ℝ=> A*x) (𝓝[>] 0) (𝓝 0):=by simpa using (Continuous.tendsto' (by unfold A; fun_prop) (0:ℝ) (0:ℝ) (by simp) : Tendsto (fun x:ℝ=> A*x) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds -- try
                                                       -- need condition
 filter_upwards [hh.eventually (gt_mem_nhds Real.pi_pos), self_mem_nhdsWithin] with c v u; intro p'; exact grew _ (mul_pos hp u) v (by have he_:=congrFun p' w; unfold Exterior.q at he_; rw [show mountain ℓ t c w= _ from he c] at he_; exact he_) -- shadow `he`
-- sample continuum shifts all phases
abbrev dyad (i:colorX ℓ)(x z:ℝ)(a:Axis):= rung z a+mountain ℓ i x
@[fun_prop] lemma dyad_c(t:colorX ℓ)(x:ℝ)(a:Axis): Continuous fun z:ℝ=> dyad ℓ t x z a:=by unfold dyad; fun_prop
open scoped Classical
lemma pure_q (c:ℝ)(a:Axis): Exterior.q (rung c a)=pureW (Complex.exp (Complex.I*c)-1) a:=p_measure a (uniformM c) -- `x=uniformM c`
local notation "T₁" i:max=> dyad ℓ i
lemma buildH (w:ℝ)(p:0<w)(h:0<ε): ∃ x z:ℝ,∀ i:colorX ℓ, let x0:= Exterior.q (dyad ℓ i x z 0); let x1:= Exterior.q (dyad ℓ i x z 2); x0≠0 ∧ x1 ≠0∧‖x0‖<w∧‖x1‖<w∧‖camp x0 f0 f0-camp x1 f0 f0-(if i=∅ then (1:ℂ) else 0)‖≤ε :=by
 let v:ℝ:=w; have he(t:colorX ℓ): ∀ᶠ x:ℝ in 𝓝[>] 0,‖Exterior.q (mountain ℓ t x)‖ < w ∧ (t≠∅→Exterior.q (mountain ℓ t x)≠0):=by
    let p₀:=mountain ℓ t; let H:= Exterior.q (p₀ 0); have he:H=0:=by unfold H p₀; rw [mountain0,ideal0]
    have ht:∀ᶠ x:ℝ in 𝓝[>] 0,‖Exterior.q (p₀ x)‖<w:=(((show Tendsto (fun q'=>‖Exterior.q (p₀ q')‖) (𝓝 0) (𝓝 ‖H‖) from (continuous_norm.comp (score_c.comp (mountain_c ℓ t))).continuousAt).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by rw [he,norm_zero]; exact p))) -- continuityAt equals Tendsto
    by_cases t':t=∅; · exact ht.mono (fun i z=>⟨z,fun u=> (u t').elim⟩)
    exact (ht.and (tilt₁ ℓ t t')).mono (fun i p=>⟨p.1,fun _=>p.2⟩)
 obtain ⟨x,c⟩:= (eventually_all.mpr he).exists; classical
 let y(i:colorX ℓ)(a:Axis)(r:ℝ):= Exterior.q (dyad ℓ i x r a); let Y(i:colorX ℓ)(r:ℝ):= (y i 0 r, y i 2 r)
 suffices he:∀ i:colorX ℓ,∀ᶠ z:ℝ in 𝓝[>] 0, y i 0 z ≠0∧ y i 2 z≠0∧‖y i 0 z‖<w∧‖y i 2 z‖<w∧‖camp (y i 0 z) f0 f0-camp (y i 2 z) f0 f0-(if i=∅ then (1:ℂ) else 0)‖≤ ε by
   obtain ⟨z,v⟩:= (eventually_all.mpr he).exists; exact ⟨x,z,v⟩
 intro i; let Z:= Exterior.q (mountain ℓ i x); have hh(a:Axis): y i a 0=Z:=by unfold y Z dyad; rw [rung_0,zero_add]
 have hp(a:Axis): Tendsto (y i a) (𝓝[>] 0) (𝓝 Z):=by rw [← hh a]; exact ((show Continuous (y i a) from score_c.comp (dyad_c ℓ i x a)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
 have ht(a:Axis): ∀ᶠ z:ℝ in 𝓝[>] 0, ‖y i a z‖<w:= (hp a).norm.eventually (gt_mem_nhds (c i).1)
 by_cases u:i=∅
 · filter_upwards [ht 0,ht 2,self_mem_nhdsWithin (a:=0) (s:=Set.Ioi (0:ℝ)),((nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) (gt_mem_nhds Real.pi_pos))] with z h0 h1 t t' -- method wrong
   let e:= Complex.exp (Complex.I*z)-1; have v:e≠0:= grew z t t'
   have hg(a:Axis): y i a z=pureW e a:=by unfold y dyad mountain rose; rw [u,sum_empty,add_zero,pure_q]
   have hx(a:Axis): y i a z≠0:=by rw [hg]; intro p; apply v; simpa [pureW] using congrFun p a
   exact ⟨hx _,hx _,h0,h1,by rw [if_pos u,hg,hg]; unfold pureW; rw [camp_high e v,camp_nil e]; norm_num; exact h.le⟩ -- tune layout indent
 have e: Z≠0:= (c i).2 u; let f:= fun p:Phase4=> camp p f0 f0; have hy: ContinuousAt f Z:=cap_C Z e ..; have hv(a:Axis):∀ᶠ z:ℝ in 𝓝[>] 0,y i a z≠0:= (hp a).eventually (compl_singleton_mem_nhds e); rw [if_neg u]; filter_upwards [hv 0,hv 2,ht 0,ht 2, (show Tendsto (fun z=>‖f (y i 0 z)-f (y i 2 z)‖) (𝓝[>] 0) (𝓝 0) from (by simpa using ((hy.tendsto.comp (hp 0)).sub (hy.tendsto.comp (hp 2))).norm)).eventually (ge_mem_nhds h)] with z p p0 p1 p2 v; exact ⟨p,p0,p1,p2,(by rwa [sub_zero])⟩ -- tune eq orientation
end Tulipe
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Tulipe.aria
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Tulipe.buildH
