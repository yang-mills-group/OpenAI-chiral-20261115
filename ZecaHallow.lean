import ZecaWhorl
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

variable {ι:Type*} (d:ι→ℝ) {r D:ℝ} {s:Set ℂ}
universe u
-- Simultaneous general finite.
lemma mosaic' (h:Weather s d)(p:0<D)(b:0<r):
 ∃ (F:Finset ι)(a:ι→ℝ),
   ∀ {H:Type u}[NormedAddCommGroup H][InnerProductSpace ℂ H],∀ v:ℕ→Option ι→H, Parallel d s D v →
   ∀ᶠ n:ℕ in atTop,
     ‖v n none - ∑ i∈F,(a i:ℂ) • v n (.some i)‖<r:=by
 obtain ⟨F,a,j⟩:=predictor h p (pow_pos b 2)
 refine ⟨F,a,@fun H _ _ v ⟨K,t,u⟩=>?_⟩
 let g(n:ℕ):=v n none - ∑ i∈F,(a i:ℂ) • v n (.some i)
 have q(i:Option ι):
   Tendsto (fun r=>inner ℂ (v r i) (g r)) atTop
       (𝓝 (K (pitch d i) 0 - ∑ k∈F,(a k:ℂ)*K (pitch d i) (d k))):=by

   apply ((u i none).sub (tendsto_finsetSum F (fun k _=>(u i (.some k)).const_mul (a k:ℂ)))).congr
   intro n; simp only [g,inner_sub_right,inner_sum,inner_smul_right]
 have y:Tendsto (fun n=> inner ℂ (g n) (g n)) atTop (𝓝 (loss K d F a)):=by
   refine ((q none).sub (tendsto_finsetSum F (fun k _=>(q (.some k)).const_mul (a k:ℂ)))).congr ?_
   intro n; conv_rhs => lhs; unfold g
   simp only [inner_sub_left,sum_inner,inner_smul_left,Complex.conj_ofReal]
 filter_upwards [y.norm.eventually (gt_mem_nhds (j K t))] with n e
 change ‖inner ℂ (g n) (g n)‖< r^2 at e
 rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_coe_norm] at e
 exact (lt_of_not_ge fun c=>e.not_ge (pow_le_pow_left₀ b.le c _))

#print axioms mosaic'

open Lattice Regis.Head.Brecht Regis.Circuit Stationary
open Complex (I)
variable (colA:PlaqAxes→ℝ)(G:Gauge){b:Axis}{t β:ℝ}
def drift(β δ:ℝ):ℂ:=Complex.exp (-I*(β:ℂ)*δ)
lemma drifting (δ e β:ℝ):
 starRingEnd ℂ (drift β δ) * drift β e =
 Complex.exp (I*(β:ℂ)*(↑(δ-e):ℂ)):=by
 unfold drift
 rw [← Complex.exp_conj,←Complex.exp_add]
 rw [map_mul,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,Complex.conj_ofReal,Complex.ofReal_sub]
 congr 1; ring

variable {d}{H: Type u} [NormedAddCommGroup H][InnerProductSpace ℂ H]
def Accord(b:Axis)(t:ℝ)(d:ι→ℝ)(v:ℕ→Option ι→H):Prop:=
 ∀i j,Tendsto (fun r=>inner ℂ (v r i) (v r j)) atTop
   (𝓝 (spectrumℓ colA G (rotary b t (pitch d i - pitch d j))))
lemma accord_phase (T:Tar s D (fun z w=>faun colA G b t β (z-w)))
 (h:0<t)(p:b ≠3)
 {v:ℕ→Option ι→H}(a:Accord colA G b t d v)
 (y:ℕ→ℝ)(e:Tendsto y atTop (𝓝 β)):
 Parallel d s D (fun n i=> drift (y n) (pitch d i) • v n i):=by
 refine ⟨_,T, ?_⟩
 intro i j
 let δ:=pitch d i
 let z:=pitch d j
 let w:=(↑(δ-z):ℂ)
 have f:Tendsto (fun n=>Complex.exp (I*(y n:ℂ)*w)) atTop
                       (𝓝 (Complex.exp (I*(β:ℂ)*w))):=
       ((Complex.continuous_ofReal.continuousAt.tendsto.comp e).const_mul I).mul_const w |>.cexp
 have k:=f.mul (a i j)
 unfold w δ z at k
 rw [faun_song colA G b t β p h,Complex.ofReal_sub] at k
 -- rw Complex.ofReal_sub includes f
 apply k.congr
 intro n
 simp only [inner_smul_left,inner_smul_right, ← mul_assoc]
 rw [mul_comm (drift ..) (starRingEnd ℂ _),drifting,Complex.ofReal_sub]
#print axioms accord_phase

variable {a c:ℝ}
lemma geminate {σ:Type*}[Finite σ] (A:σ→Spot)(o:∀i,1≤ (A i).t ∧ (A i).b≠3)
    (e:0≤a)(p:a<c)(j:0<r):
 ∃(F:Finset (brig a c))(f:brig a c→ℝ),
    ∀{H:Type u}[NormedAddCommGroup H][InnerProductSpace ℂ H](i:σ)
    (v:ℕ→Option (brig a c)→H), Accord colA G (A i).b (A i).t (beam5 a c) v →
    ∀y:ℕ→ℝ,Tendsto y atTop (𝓝 ((A i).β))→
      ∀ᶠ n in atTop,‖v n none-
         ∑ k∈F, ((f k:ℂ)*drift (y n) (beam5 a c k)) • v n (.some k)‖<r:=by
 obtain ⟨D,vD,t⟩:=cask_meet colA G A (fun i=>(o i).1) (c+1)
 obtain ⟨F,f,g⟩:= mosaic'.{u} _ (hull5 e p) vD j -- universe param order
 refine ⟨F,f,@fun H _ _ i v h y hy=>?_⟩
 specialize g _ (accord_phase colA G (t i) (zero_lt_one.trans_le (o i).1) (o i).2 h y hy)
 have k:∀n,drift (y n) (pitch (beam5 a c) none)=1:= by intro n; simp [drift,pitch]
 simp_rw [mul_smul]
 simp_rw [k,one_smul] at g
 exact g
#print axioms geminate
