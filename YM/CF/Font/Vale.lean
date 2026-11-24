import YM.CF.Font.Hymn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch Matrix Asymptotics
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {f n c: Side}
def remit (K:Ps n→ℝ):Wind n→ℝ:=Sum.elim K (fun _=>0)
lemma rem_sum{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](K:Ps n→ℝ)(G:Links (Per n) E)(x:Site n): ∑ i:Wind n,remit K i • heat x G i=∑ i:Ps n,K i • heat x G (.inl i):=by simp only [Wind,Fintype.sum_sum_type,remit, Sum.elim_inl,Sum.elim_inr,zero_smul,sum_const_zero,add_zero]
def contour (x:Site n)(u w:Wind n):ℝ:= ↑(dial x u)+↑(dial x w)
lemma ct_pos (x:Site n)(u w):0≤contour x u w:=add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
structure SweepH {c f:Side}(Λ:Ps f→ Ps c→ℝ) (K:Wind f→ Wind c→ℝ)(A:ℝ):Prop where
 mouth(p:Ps f): K (.inl p)=remit (Λ p)
 val(i:Axis): ∑ u,‖K (.inr i) u‖≤ tall f c A
lemma bowl {S:StepData c f}{G:Gauge}(R:Forest S.ratio)(x:Site f)(y:Site c){P Q: Bed}{T:Towers S.patch.L}{A B a γ:ℝ}(h:0<a)(ha:0≤A)(he:P.dual_diag.strip a A)(hf:Q.diagonal.strip a B)(v:T.Deep a A 1){p:Clip}(H:Floor P p f γ B)(g:Towers.Diagonal S P Q T):∃ K:Wind f→Wind c→ℝ,SweepH (lambda (S:=S) P Q T) K A ∧ ∀ u:fieldDir G c 1, let Y:=Channel.rising R (installed S.ratio T.A0) u;∀ i,heat x (collect G Y) i=∑ z,K i z • heat y (collect G u) z:=by
 choose F l W using (fun i=> slopeH_r (G:=G) h he hf v H g R x i y ha)
 let K:= Sum.elim (fun i:Ps f=>remit (lambda (S:=S) P Q T i)) F; refine ⟨K,⟨fun _=>rfl,fun i=> l i⟩,?_⟩; intro u Y i
 cases i with
 | inr a=> exact W a u
 | inl i=>simp only [K,Sum.elim_inl,rem_sum]; exact curlV S P Q T h he hf v H g R u i
variable {Λ: Ps f→Ps c→ℝ}{K:Wind f→Wind c→ℝ}{A:ℝ}
def roseK (K:Wind f→Wind c→ℝ)(x:Site f)(v w:Wind f)(j l:Wind c):ℝ:=match v,w with
 | .inl i,.inl p=> K v j*K w l-K (.inl (x,i.2)) j*K (.inl (x,p.2)) l
 | _,_=> K v j*K w l
-- crude volume test postL
lemma totalH(R:Ratio c f)(h:SweepH Λ K A){e B:ℝ}(v:0<e)(hf:Rails R B e Λ)(ha:0≤A)(hb:0≤B)(i:Wind f):∑ u:Wind c,‖K i u‖≤B+tall f c A:=by
 cases i with
 | inr i=> exact le_trans (h.val i) (le_add_of_nonneg_left hb)
 | inl x=>
   rw [h.mouth]; simp only [Fintype.sum_sum_type, remit,Sum.elim_inr,Sum.elim_inl,norm_zero, sum_const_zero,add_zero];
   apply le_trans (sum_le_sum (g:=fun i=> Faro e (R.parent x.1) i.1*‖Λ x i‖) ?_ |>.trans (hf.rate x))
   · apply le_trans (div_le_self hb (one_le_pow₀ (show (1:ℝ) ≤ spanV R from period_one))); exact le_add_of_nonneg_right (by unfold tall; positivity)
   intro u _; exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity)) -- tune
-- enough after L, includes F endpoint weights and δL budget
lemma probate {L:Side}(e:4≤L.val) (A B S C b:ℝ)(ht:0<S)(hC:0<C)(p:0<b): ∃ N:ℕ,∀ {f c:Side}(R:Ratio c f),N≤ c.val→ R.count=L→ (1+|B|+|tall f c A|)^2*S*nick b (3*c.val) ≤ C*nick b f.val:=by
 let T(z:ℝ):= (Fintype.card (TypeFace 1):ℝ)*z^4*((z*L.val)*(Fintype.card (TypeFace 1):ℝ)*A)*(4*(9*(z+1)+1)^2)
 let t:=(Fintype.card (TypeFace 1):ℝ)
 let U:=t*(L.val:ℝ)*t*|A| *(4*19^2)
 have hl : (4:ℝ)≤ L.val:=by exact_mod_cast e
 have he(z:ℝ)(h:1≤z): |T z|≤ U*z^7:=by
    have ha:0≤z:=by linarith
    have he: 0≤9*(z+1)+1:=by positivity
    unfold T; simp only [abs_mul, abs_pow,abs_of_nonneg ha,abs_of_nonneg he, abs_of_nonneg (show 0≤(Fintype.card (TypeFace 1):ℝ) by positivity),abs_of_nonneg (show 0≤(L.val:ℝ) by positivity),abs_of_pos (show (0:ℝ)<4 by norm_num)]
    refine le_trans (b:= t*z^4*(z* L.val*t*|A|)*(4*(19*z)^2)) ?_ (le_of_eq ?_)
    · unfold t; gcongr; linarith
    unfold U; ring
 let D:=1+|B|+U; have hu:0≤ U:=by unfold U t; positivity
 let q:=b*((L.val:ℝ)-3); have hh:0<q:=by unfold q; nlinarith
 have hx : Tendsto (fun z:ℝ=> D^2*S*z^14*Real.exp (-q*z)) atTop (𝓝 0):=by
   have h:= Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n:=14) -- tune
   convert ((h.comp (tendsto_id.const_mul_atTop hh)).const_mul (D^2*S/q^14)) using 1; ext z:1; simp only [Function.comp_apply,id_eq, neg_mul]; field_simp; ring
    -- indent
 obtain ⟨n,h⟩:= eventually_atTop.1 ((hx.comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hC)) -- specify ℕ
 refine ⟨n,?_⟩; intro f c R u v; let z:ℝ:=c.val; have hz : 1≤z :=by unfold z; exact_mod_cast c.property
 have hp:0<z:=by linarith
 have ht': (f.val:ℝ)=z* L.val:=by unfold z; rw [R.exact_size,v,Nat.cast_mul]
 have hy:tall f c A=T z:=by unfold tall T; rw [ht']
 rw [hy,ht']; have hl: 1+|B|+|T z| ≤ D*z^7:=by apply (add_le_add_right (he z hz) (1+|B|)).trans; unfold D; rw [add_mul]; apply add_le_add_left; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hz)
 refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hl 2) ht.le) (nick_pos b (by positivity)|>.le)).trans ?_
 have hm:D^2*S*z^14*Real.exp (-q*z)≤ C:=h _ u; unfold nick
 calc
  _ = D^2*S*z^14*Real.exp (-q*z) *((1+3*z)*Real.exp (b*(z*L.val))):=by rw [show Real.exp (b*(3*c.val))= Real.exp (-q*z)*Real.exp (b*(z*L.val)) by rw [←Real.exp_add]; unfold q z; ring]; unfold z; ring
  _ ≤ _:=mul_le_mul hm (by apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); nlinarith) (by positivity) hC.le
end YM.CF.Font
