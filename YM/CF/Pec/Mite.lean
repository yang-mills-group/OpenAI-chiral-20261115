import YM.CF.Pec.Sine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {n N c:Side}{T:RG.StepData (More n) (More N)}{F: Forest T.ratio}{X:Cloud n→ℂ}{a b:ℝ}
private lemma fees (v:Edge (Site (More n)))(x:group.Color): put group (More n) v x=∑ i:group.ColorIndex,x i • whisp (n:=n) (Push.Uniform.bolt (Trot (More n) v,i)):=by
 funext a; rw [Finset.sum_apply]; apply PiLp.ext; intro j; rw [WithLp.ofLp_sum, Finset.sum_apply]; change (Pi.single (M:=fun _=> group.Color) (Trot _ v) x a).ofLp j=∑ i:group.ColorIndex, x i * Push.Uniform.bolt (Trot _ v,i) (a,j)
 by_cases h:a=Trot _ v <;>simp [Pi.single_apply,h,Push.Uniform.bolt]; -- tune
variable {k:ℕ}
private def fareC(k:ℕ):ℝ:=Fintype.card (Fin k→ group.ColorIndex) * ((k.factorial:ℝ)⁻¹ * ‖colorL.toContinuousLinearMap‖^k)
lemma fI_pos(k:ℕ):0≤fareC k:=by unfold fareC; positivity
lemma feeInk (p:ContDiffAt ℝ k X 0)(x:Site (More n))(v:Fin k→Blip (More n))(h:Beacon (aTrait T) a k (fun y=> X (whisp y)) (T.ratio.embed x) 0 b)(hx:0≤b)(t:0<a):
 ‖timeA (cake k X) v‖ ≤ fareC k * b*Real.exp (-a*∑ l:Fin k, (separation x (v l).1:ℝ)):=by
 set Δ :ℝ:=∑ l:Fin k,(separation x (v l).1 :ℝ); let H:= cake k X; let L:=(tint group (Body 1 (More n))); let f :=X; have hg:ContDiffAt ℝ k f (L 0):=by rw [map_zero]; exact p
 let s := Real.exp (-a*Δ); let u:ℝ:=(k.factorial:ℝ)⁻¹; let C:= colorL.toContinuousLinearMap
 apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg (fI_pos _) hx) (by positivity)); intro r
 let V (d:Fin k→group.ColorIndex)(i:Fin k) : Coat n:= (Trot _ (v i),d i)
 have hp(d:Fin k→group.ColorIndex): H (fun i=> L (Push.Uniform.bolt (V d i)))=u • Push.Uniform.entry (f∘ L) 0 (V d) :=by
    unfold Push.Uniform.entry; rw [show iteratedFDeriv _ k (f ∘ L) 0 =_ from iter_lin_at (L:=L.toContinuousLinearMap) (k:=k) hg,map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
 have hz(g:Fin k→group.ColorIndex):spanSites (aTrait T) (T.ratio.embed x) (V g)= T.ratio.count.val * ∑ i, separation x (v i).1:=by
    unfold spanSites V; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; exact emptio ..
 have hv(d: Fin k → group.ColorIndex):‖Push.Uniform.entry (f ∘ L) 0 (V d)‖≤ b *s:=by
    refine le_trans (h k le_rfl (V d)) ?_; unfold s; rw [hz]; apply mul_le_mul_of_nonneg_left _ hx; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (by linarith); unfold Δ; rw [←Nat.cast_sum]; exact_mod_cast Nat.le_mul_of_pos_left _ T.ratio.count.property
 let t(i):=r i
 have hh(d:Fin k→group.ColorIndex): ‖∏ i, r i (d i)‖≤‖C‖^k*(∏ i,‖r i‖):=by
    rw [norm_prod]; calc
      _ ≤ ∏ i:Fin k,(‖C‖* ‖r i‖):=Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> (norm_le_pi_norm (C (r i)) (d i)).trans (C.le_opNorm _))
      _ = _:=by rw [Finset.prod_mul_distrib, Finset.prod_const,card_univ,Fintype.card_fin]
 change ‖H (fun i=> put group (More n) (v i) (r i))‖≤ _; simp_rw [fees]; rw [ContinuousMultilinearMap.map_sum]
 let M:=‖C‖^k*(∏ i,‖r i‖)*(u*(b*s))
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>M) ?_).trans_eq ?_); intro g _; rw [ContinuousMultilinearMap.map_smul_univ]; change ‖(∏ i,r i (g i)) • H (fun k=> L (Push.Uniform.bolt (V g k)))‖≤ M; rw [hp g,norm_smul]; let R:= u • Push.Uniform.entry (f∘ L) 0 (V g); refine mul_le_mul (hh g) ?_ (norm_nonneg _) (by positivity); rw [norm_smul, Real.norm_of_nonneg (show 0≤u by unfold u; positivity)]; apply mul_le_mul_of_nonneg_left (hv g); positivity
 simp only [Finset.sum_const,card_univ,nsmul_eq_mul]; unfold M u fareC C s; ring
lemma niche {x:Site (More n)} (p:ContDiffAt ℝ k X 0)(g:Beacon (aTrait T) a k (X∘whisp) (T.ratio.embed x) 0 b)(t:0<a)(hb:0≤b): tiltV x (cake k X) (a/2) 0 ≤ fareC k*b*((Fintype.card Axis:ℝ)*countCost (a/2))^k:=by
 let h:= a/2; let u:= countCost h; let v:= fareC k*b; have hs:0<h:= half_pos t; have hc:0<u:= count_pos hs
 let y(e:Blip (More n)):= Decay h x e.1
 have hz:0≤v:=mul_nonneg (fI_pos k) hb
 have hA: ∑ i:Blip (More n),y i ≤ Fintype.card Axis*u:=by unfold Blip Edge; rw [Fintype.sum_prod_type]; change ∑ i:Site (More n),∑ _:Axis,Decay h x i ≤_; simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (decay_count hs x) (by positivity)
 have h'(r: Fin k→ Blip (More n)):let F:= Real.exp (h*(0+∑ i, (separation x (r i).1:ℝ))); F*‖timeA (cake k X) r‖ ≤ v* ∏ i, y (r i):=by
   intro F; apply (mul_le_mul_of_nonneg_left (feeInk p x r g hb t) (Real.exp_pos _|>.le)).trans_eq; let z:ℝ:= ∑ i:Fin k,(separation x (r i).1:ℝ)
   have hh:F*Real.exp (-a*z)= ∏ i, y (r i):=by simp only [F,y,Decay]; rw [←Real.exp_sum]; simp_rw [←Finset.mul_sum,←Real.exp_add]; congr 1; unfold z h; ring
   rw [mul_left_comm,hh]
 unfold tiltV; apply (sum_le_sum (fun r (_:r∈(univ:Finset _))=> h' r)).trans; rw [← Finset.mul_sum, show ∑ t: Fin k→ Blip (More n),∏ i:Fin k, y (t i)= (∑ i: Blip (More n),y i)^k from ?_]; apply mul_le_mul_of_nonneg_left _ hz; exact pow_le_pow_left₀ (sum_nonneg fun i _=>(decay_pos ..).le) hA _
 convert (Finset.prod_univ_sum (fun i:Fin k=> (Finset.univ:Finset (Blip (More n)))) (fun _ i=> y i)).symm using 1 <;> first|rfl|simp
lemma feeI {z: Cloud n→ AxisChart group F}{X:Snap F→ ℂ}{V:Cloud n→ ℂ}{x:Site (More n)}{c d:ℝ}
 (p: Horizon F z k a b)(ha:0<a)(hb:0≤b)(hv:ContDiffAt ℝ k X 0)(h: Beacon (clothH T F) c k X (T.ratio.embed x) 0 d)(hc:0<c)(hd:0≤d)(g:V∘ whisp =ᶠ[𝓝 0] X ∘ Push.Uniform.curve (station z)):
 ContDiffAt ℝ k V 0∧ Beacon (aTrait T) (litSpan k a c) k (V ∘ whisp) (T.ratio.embed x) 0 (2*(d*machinist k (townCost group) b c)):=by
 let T':=Push.Uniform.curve (station z); let L:=tint group (Body 1 (More n)); let Y:= tint group F.Free; have hs:ContDiffAt ℝ ω (station z) 0:= Y.symm.contDiff.contDiffAt.comp (f:=z ∘ L) _ ((show ContDiffAt ℝ ω z (L 0) by rw [map_zero]; exact p.smooth).comp _ L.contDiff.contDiffAt)
 have hp:T' (0:Positions (Primary _ _))=0:=by unfold T' Push.Uniform.curve station; rw [Function.comp_apply,Function.comp_apply,map_zero,p.flat,map_zero]; change (partSpace ..).symm (0,0)=0; exact map_zero _
 have he: Beacon (aTrait T) (litSpan k a c) k (V∘whisp) (T.ratio.embed x) 0 (2*(d*machinist k (townCost group) b c)):=by
    intro i hi q; unfold Push.Uniform.entry; rw [(g.iteratedFDeriv ℝ i).eq_of_nhds]; exact beacon_complex (g:=T') (x:=0) (by rwa [hp]) ((Push.Uniform.along hs).of_le le_top) hc ha hd hb (by rw [hp]; exact h) p.p (town F) i hi q
 refine ⟨?_,he⟩; have hh: ContDiffAt ℝ k (V ∘ L) (L.symm 0):=by
    rw [map_zero]; exact ((hp.symm ▸ hv: ContDiffAt ℝ k X (T' 0)).comp _ ((Push.Uniform.along hs).of_le le_top)).congr_of_eventuallyEq g
 have he: V=(V ∘ L)∘ L.symm:= by funext; simp
 nth_rw 1 [he]; exact hh.comp 0 L.symm.contDiff.contDiffAt
-- export cost simplif
lemma supplies(k:ℕ) (a:ℝ)(p:0<a):∃ v:ℝ,0≤v∧∀ {n N:Side}{T:RG.StepData (More n) (More N)}{X:Cloud n→ℂ} (x:Site (More n)) (b:ℝ), 0≤b→ContDiffAt ℝ k X 0→ Beacon (aTrait T) a k (X∘whisp) (T.ratio.embed x) 0 b→ tiltV x (cake k X) (a/2) 0 ≤ v*b:=by
 let v:= ((Fintype.card Axis:ℝ)*countCost (a/2))^k; refine ⟨fareC k*v,mul_nonneg (fI_pos _) (pow_nonneg (mul_nonneg (by positivity) (count_pos (half_pos p)|>.le)) _),fun x b h t z=>(niche t z p h).trans_eq (mul_right_comm ..)⟩
end YM.CF.Pec
