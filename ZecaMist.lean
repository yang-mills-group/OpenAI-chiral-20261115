import ZecaNimbus2
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

variable {ι:Type*} {d:ι→ℝ}{p u r D:ℝ} {s:Set ℂ}

structure Tar (s:Set ℂ)(D:ℝ)(K:ℂ→ℂ→ℂ) : Prop where
 hol (w:ℂ) (v:w∈s): DifferentiableOn ℂ (fun z=>K z w) s
 hol' (w:ℂ) (v:w∈s): DifferentiableOn ℂ (K w) s
 ub (z w:ℂ): z∈s→w∈s→‖K z w‖≤D

def loss (K:ℂ→ℂ→ℂ) (d:ι→ℝ)(F:Finset ι)(a:ι→ℝ):ℂ:=
 (K 0 0- ∑ i∈F,(a i:ℂ)*K 0 (d i))-
  ∑ j∈F,(a j:ℂ)*(K (d j) 0- ∑ i∈F,(a i:ℂ)*K (d j) (d i))

lemma predictor (h:Weather s d)(p:0<D) (b:0<r):
 ∃ (F:Finset ι)(a:ι→ℝ), ∀K, Tar s D K→ ‖loss K d F a‖<r:=by
 have u:=div_pos b p
 obtain ⟨x,v,t⟩:=exists_between (lt_min u (show (0:ℝ)<1 by norm_num))
 obtain ⟨F,a,y⟩:=reached h v
 refine ⟨F,a,fun K c=>?_⟩
 let k z:=K z 0- ∑ i∈F,(a i:ℂ)*K z (d i)

 have z0:(0:ℂ)∈s:= by
    obtain ⟨t,_,a,b,_⟩:=h.lapse
    simpa using a b
 have e(z:ℂ)(g:z∈s):‖k z‖≤D*x:=y p (K z) (c.hol' z g) fun w=>c.ub z w g
 have j:DifferentiableOn ℂ k s:= by
    apply (c.hol _ z0).sub
    apply (DifferentiableOn.sum (fun i (_:i∈F)=> (c.hol _ (h.days i)).const_mul (a i:ℂ))).congr
    exact fun z _=> (Finset.sum_apply z F (fun i z=>(a i:ℂ)*K z (d i))).symm
 refine (y (mul_pos p v) k j e).trans_lt ?_
 exact (mul_lt_of_lt_one_right (mul_pos p v) (lt_min_iff.mp t).2).trans
                 ((mul_comm ..).trans_lt ((lt_div_iff₀ p).mp (lt_min_iff.mp t).1))
#print axioms predictor

variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H]
-- proof sequenced by index 0 target 
abbrev pitch (d:ι→ℝ): Option ι → ℝ:= (Option.elim · 0 d)

variable (d)
def Parallel (s:Set ℂ)(D:ℝ)(v:ℕ→Option ι→H):Prop:=
 ∃K:ℂ→ℂ→ℂ,Tar s D K ∧
    ∀i j,Tendsto (fun r=>inner ℂ (v r i) (v r j)) atTop
          (𝓝 (K (pitch d i) (pitch d j)))

-- Simultaneous general finite.
lemma mosaic (h:Weather s d)(p:0<D)(b:0<r):
 ∃ (F:Finset ι)(a:ι→ℝ),
   ∀ v:ℕ→Option ι→H, Parallel d s D v →
   ∀ᶠ n:ℕ in atTop,
     ‖v n none - ∑ i∈F,(a i:ℂ) • v n (.some i)‖<r:=by
 obtain ⟨F,a,j⟩:=predictor h p (pow_pos b 2)
 refine ⟨F,a,fun v ⟨K,t,u⟩=>?_⟩
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

#print axioms mosaic
