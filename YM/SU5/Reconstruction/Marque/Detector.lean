import YM.SU5.Reconstruction.Marque.Ledger
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Passage
open Function Set Filter Metric
open scoped Topology Classical
variable {H:Type*} [MetricSpace H] (P:Passage H)
local notation "W"=> Wander H
variable {Y:Type*}[TopologicalSpace Y]
structure Upright : Prop where
    z : P.Agree (fun v=> Pole (rich v))
    x : P.Agree (fun v=> Tope v 1)
    y : P.Agree (fun v=> Tope v Sugar)
namespace Upright
variable {P}(h:P.Upright)(p:ℂˣ)(t:ℝ)
variable (w:P.Agree (fun v=>Tope v p))
include h in
private lemma speck {L:ℂ→Two}(s:ℝ)(hs:0<s)(b: ∀ u v,L u * L v=L (u+v))(d:∀ v,L (-v)=(L v)⁻¹)(k:ℝ)(x:W)(hx:x∈P.ok (L ((p:ℂ)*↑s)))
   (w: ∀ v:ℝ,rehome (Tuning (k*v)) (L ((p:ℂ)*↑s))=L ((p:ℂ)* ((Real.exp v*s:ℝ):ℂ))) : P.Agree (fun v:ℝ=> L ((p:ℂ)*(v:ℂ))):= by
   have A (f:ℝ→ℝ)(p0:Continuous f)(x0:∀ t, 0<f t):P.Agree (fun t:ℝ=> L ((p:ℂ) * (f t:ℂ))) := by
       let T(v:ℝ):=Real.log (f v/s)
       have he:Continuous T:= (p0.div_const s).log fun t=> (div_pos (x0 t) hs).ne'
       let g(v:ℝ):= Tuning (k*T v); have hv:P.Agree g:=compAgree h.z (show Continuous (fun v=>k*T v) by fun_prop)
       rw [show (fun t:ℝ=> L ((p:ℂ)* (f t:ℂ)))=(fun t=> rehome (g t) (L ((p:ℂ)*↑s))) from ?_]; exact timesAgree (timesAgree hv (hereAgree _ hx)) (reverseAgree hv)
       ext1 y; unfold g; rw [w]; dsimp only [T]; rw [Real.exp_log (by positivity [x0 y]),div_mul_cancel₀ _ hs.ne']
   let g(u:ℝ):=1+ max u 0; let i(u:ℝ):=1+ max (-u) 0
   have hg:P.Agree (fun u=>L ((p:ℂ)*(g u:ℂ))):=A _ (continuous_const.add (continuous_id.max continuous_const)) (fun u=>by unfold g; linarith [le_max_right u (0:ℝ)])
   have hi:P.Agree (fun u=>L ((p:ℂ)*(i u:ℂ))):= A _ (continuous_const.add (continuous_id.neg.max continuous_const)) (fun u=>by unfold i; linarith [le_max_right (-u) (0:ℝ)])
   convert timesAgree hg (reverseAgree hi) using 2; rename_i v
   rw [← d,b,← mul_neg,← mul_add]; congr 2; rcases le_total 0 v with h|j
   · simp [g,i,max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
   simp [g,i,max_eq_left (neg_nonneg.mpr j),max_eq_right j]
variable (P) in
include w in
lemma inverseD (e: p⁻¹=p ∨ p⁻¹=-p):P.Agree (fun v=>Tope v p⁻¹):=by
 rcases e with e|e; rw [e]; exact w
 simp_rw [e,heel]; exact compAgree w continuous_neg
include h w
lemma fareHead:P.Agree (fun v:ℝ=>Head ((p:ℂ)*(v:ℂ))):=by
 obtain ⟨s,hs,H'⟩:= craft; obtain ⟨a,b,c,d,v⟩:= H' p
 obtain ⟨k,hk⟩:= agree_price w a; obtain ⟨k',hk'⟩:= agree_price w c; obtain ⟨u,p₁⟩:= agree_price h.z b; obtain ⟨u',p₂⟩:= agree_price h.z d
 refine speck h p s hs Head_add (fun v=>(Head_inv v).symm) (1/2) _ (v ▸ P.plus (P.plus (P.plus hk p₁) hk') p₂) (fun e=>?_)
 rw[Head_scale, show 2*(1/2*e)=e by ring]
lemma fareTail (v:P.Agree (fun v=>Tope v p⁻¹)): P.Agree (fun v:ℝ=>Tail ((p:ℂ)*(v:ℂ))):=by
 obtain ⟨s,hs,H'⟩:= craft; obtain ⟨a,b,c,d,v'⟩:= H' p
 obtain ⟨k,hk⟩:= agree_price v a; obtain ⟨k',hk'⟩:= agree_price v c; obtain ⟨u,p₁⟩:= agree_price h.z b; obtain ⟨u',p₂⟩:= agree_price h.z d
 refine speck h p s hs Tail_add (fun v=>(Tail_inv v).symm) (-1/2) _ ((carriesTail _ v') ▸ P.plus p₂ (P.plus hk' (P.plus p₁ hk))) (fun e=>?_)
 rw[reversedTail, show - (2*(-1/2*e))=e by ring]
omit w
private lemma combination(f:ℂ→Two)(p:P.Agree (fun v:ℝ=> f ((((1:ℂˣ):ℂ))* (v:ℂ))))(q:P.Agree (fun v:ℝ=>f ((Sugar:ℂ)*(v:ℂ))))(b:∀ u v,f u*f v=f (u+v)):P.Agree f:= by
   have e:Tuning 0=1:= tuning_one -- remove
   convert timesAgree (compAgree p Complex.continuous_re) (compAgree q Complex.continuous_im) using 2
   rename_i y; rw [b]; push_cast; simp [mul_comm Complex.I]
lemma front:P.Agree Head:= by apply combination h Head (fareHead h (1:ℂˣ) h.x) (fareHead h Sugar h.y) Head_add
lemma back:P.Agree Tail:=by
 refine combination h Tail (fareTail h _ h.x ?_) (fareTail h _ h.y ?_) Tail_add
 ·rw [inv_one];exact h.x
 exact inverseD _ _ h.y (Or.inr (by ext1;simp))
variable {ι:Type*}{J:Filter ι}
lemma cross(g:Two){e:ι→Two}(w:Tendsto e J (𝓝 g)):P.Fell e g J:=by
 obtain ⟨s,p⟩:=padded g; let G(x:Two):=x*Head s; replace p:B (G g)≠0:=p
 let Φ (x:Two):ℂ:=(D (G x)-1)/B (G x); let K (x:Two):=(A (G x)-1)/B (G x); let X(x:Two):= B (G x)
 let V (x:Two):=Tail (Φ x)* Head (X x) * Tail (K x)* Head (-s)
 have v(x:Two)(p:X x≠0):x=V x:=by
      unfold V; rw [← pad]; change x=x*_*_; rw [mul_assoc,Head_add];simp; exact p -- tune
 have hv(y:Two):ContinuousAt G y:= continuousAt_id.mul continuousAt_const
 have hy:ContinuousAt X g:= cB.continuousAt.comp (hv g)
 have H0:= atSome h.front (hy.tendsto.comp w); have H2:P.Fell (fun i=>Tail (Φ (e i))) (Tail (Φ g)) J:= atSome h.back ( (show ContinuousAt Φ g from ((cD.continuousAt.comp (hv g)).sub continuousAt_const).div (cB.continuousAt.comp (hv g)) p).tendsto.comp w)
 have H1:P.Fell (fun i=>Tail (K (e i))) (Tail (K g)) J:= atSome h.back ((show ContinuousAt K g from ((cA.continuousAt.comp (hv g)).sub continuousAt_const).div (cB.continuousAt.comp (hv g)) p).tendsto.comp w)
 have H':P.Fell (fun i=>V (e i)) (V g) J:= rolled (rolled (rolled H2 H0) H1) (atSome h.front (show Tendsto (fun i:ι=> -s) J (𝓝 (-s)) from tendsto_const_nhds))
 rw [← v g p] at H'; exact congrFell H' (((hy.tendsto.comp w).eventually (show ∀ᶠ x in 𝓝 (X g), x ≠0 from isOpen_ne.mem_nhds p)).mono (fun i p => (v _ p).symm)) -- tune
lemma always(g:Two):∃ u:W, u∈P.ok g:=by obtain ⟨U,x,p,v,k⟩:=cross h g (tendsto_id (x:=𝓝 g)); exact ⟨x,v⟩
end Upright
end YM.Marque.Passage
