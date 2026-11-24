import Anomaly.Ward.Foliage
import Anomaly.Affine
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
def payAng(s:Sweep N)(A:StemA N):StemA N:=fun i=> let v:=A (lane s i); let u:=if s.s.flip i.2 then -v else v; if s.charge then -u else u
lemma arc_charge(t:ℝ):polarT true (Zephyr.Chern.arc t)=Zephyr.Chern.arc (-t):=by
 rw [arc_neg]; apply SU.group.mat_injective; change SU.fund _= SU.fund _
 rw [show SU.fund (polarT true (Zephyr.Chern.arc t))=cc (SU.fund _) from rfl,SU.fund_inv]
 have he:SU.fund (Zephyr.Chern.arc t)= Matrix.diagonal _:=rfl -- tune
 rw [he]; ext i j; by_cases w:i=j<;>simp [w,cc_apply,Matrix.star_eq_conjTranspose,Matrix.diagonal_apply,Ne.symm]
lemma travels(s:Sweep N)(A:StemA N)(x:ℝ): flashA s (petals A x)=petals (payAng s A) x:=by funext i; rw [flash]; unfold _root_.Zephyr.Chern.petals payAng; cases h:s.s.flip i.2 <;> cases he:s.charge <;> simp only [h,he,arc_charge,ite_true,Bool.false_eq_true,ite_false,map_inv,neg_mul,arc_neg,inv_inv] <;> rfl
lemma ledgerQ (s:Signed)(A:StemA N)(v:ℝ)(p:Temper (node (0:Site N)) A v) : Temper (node (0:Site N)) (payAng (gridTulip s (0:Site N)) A) (2*v):=by
 have hx:=p.above; constructor; · linarith
 intro x; let U:=gridTulip s (0:Site N); let t:=lane U x; have ht:separation t.1 (node (0:Site N))≤ 1+separation x.1 (node (0:Site N)):=by
    apply (separation_triangle _ ((boxA U) x.1) _).trans; have hp:boxA U (node 0)=node 0:=by rw [←nodeA,tieA] -- U local
    exact add_le_add (Ione.tall_y U x) (le_of_eq (by conv_rhs=>rw [←sitT U,hp]))
 unfold payAng; simp_rw [apply_ite (|·|),abs_neg,ite_self]; simp_rw [apply_ite (|·|),abs_neg,ite_self]; refine (p.grow t).trans ?_
 have h:(separation t.1 (node (0:Site N)):ℝ)≤ 1+separation x.1 (node (0:Site N)):=by exact_mod_cast ht
 nlinarith only [hx -- hx Le already
             ,h, mul_le_mul_of_nonneg_left h (zero_le_one.trans hx),Nat.cast_nonneg (α:=ℝ) (separation x.1 (node (0:Site N)))]
lemma toReal {f:ℝ→ℂ}{c:Three ℂ}(h:Bloom f c): Bloom (fun i=> ((f i).re:ℂ)) (fun i=> ((c i).re:ℂ)):=by
 apply Bloom.of_der (a:=fun i=> ((deriv f i).re:ℂ)) ?_ (b:=((((deriv (deriv f) 0).re):ℂ))) ?_ ?_ ?_ ?_
 · refine h.1.1.mono fun i p=>?_; exact (Complex.ofRealCLM ∘L Complex.reCLM).hasFDerivAt.comp_hasDerivAt i p.hasDerivAt
 · exact (Complex.ofRealCLM ∘L Complex.reCLM).hasFDerivAt.comp_hasDerivAt _ h.1.2.hasDerivAt
 · rw [h.2]; rfl
 · rw [h.2]; rfl
 rw [h.2]; change (((( _ / (2:ℂ)).re):ℂ))=_; generalize deriv (deriv f) (0:ℝ)=z; simp [div_eq_mul_inv,mul_comm] -- wrong RHS uses Re so simp
open Py Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
open Buffered.Afterglow.Tower.VacuumSelection
open Rush
private lemma modelCube(P:Spine)(h:SprigFee P)(g:Signed)(m:ℕ)(p:1≤ m)(L:List Axis)(z:Cover):
    ∃ δ : ℝ,0<δ∧∀ᶠ s:ℕ in atTop,∀ i k:ℕ, let U:=mPath (gridTulip g (0:Site (age P.run i s))); let f:=fun t=>squareSum (fun y=> Zephyr.Chern.fullSite P i k s (U y) t) m L (wrap _ z); Bud f ∧ δ ≤ (bud f 2).re := by
  induction L generalizing z with
  | nil =>
    obtain ⟨δ,r,T⟩:=site_reset P h (g.act z); refine ⟨δ,r,T.mono fun s t i k => ?_⟩; intro U f; rw [show f= Zephyr.Chern.fullSite P i k s (wrap _ (g.act z)) from (by unfold f squareSum; unfold U; rw [tie_wrap])]; exact ⟨(t i k).1,(t i k).2.le⟩
  | cons l L e=>
    let Z(c:ℕ): Cover:= z-m • step l+(c+1) • step l; let J(i s):=mPath (gridTulip g (0:Site (age P.run i s)))
    choose d hp ht using fun i=> e (Z i)
    let c:=range (2*m); have ho:0∈c:= mem_range.mpr (by omega)
    have hx:∀ᶠ s:ℕ in atTop,∀ j∈c,∀ i k, let f:=fun t=>squareSum (fun y=> fullSite P i k s (J i s y) t) m L (wrap _ (Z j)); Bud f ∧ d j ≤ (bud f 2).re := eventually_all_finset c|>.2 fun j _=>ht j
    refine ⟨d 0,hp 0,hx.mono fun s t i k=>?_⟩
    intro U f; let K(j:ℕ)(x:ℝ):ℂ:=squareSum (fun y=> Zephyr.Chern.fullSite P i k s (U y) x) m L (wrap _ (Z j))
    have hF : Bloom f (∑ j∈c,bud (K j)):= by
      have hG : f=fun x=> ∑ j∈c, K j x :=by
        funext; simp only [f,squareSum, stripSum,K,moveSite,Z,map_sub,map_nsmul,map_add,wrap_step]; rfl
      rw [hG]
      exact bloomCube (f:=fun i' t'=>Zephyr.Chern.fullSite P i k s (U i') t') (fun j=>wrap _ (Z j)) (fun j v=>(t j v _ k).1.bloom)
    refine ⟨hF.1,?_⟩
    rw [hF.bud_eq,Finset.sum_apply,Complex.re_sum]
    exact (single_le_sum (fun j _=>(hp j).le) ho).trans (sum_le_sum fun j q=>(t j q i k).2)

lemma underTurn (P:Spine)(p:SprigFee P)(m:ℕ)(w:1 ≤ m)(g:Signed)(a b:ℝ)(ha:0<a): ∃ δ:ℝ,0<δ ∧ ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s<P.run.uv k →∀ J T: Axis→SOp (age P.run i s), ∀ X Z:SOp (age P.run i s),∀ f d : ℝ,
        CartPins P.run i k s m a b f d J T X Z → let R:=RootBook P.run i k s; let B:=R.p; let K:= (P.run.voyage i).CapeT s;
          let F:=traceMeter B K (0:Site (age P.run i s)) X ∘ flashA (gridTulip g 0) ∘ (_root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream (age P.run i s)))
          Bud F ∧ δ < (dollar g)*(bud F 2).re:=by
 obtain ⟨δ,q,K⟩:= modelCube P p g m w (List.ofFn (id:Axis→Axis)) 0
 obtain ⟨W,⟨T'⟩⟩:= oily ha P.par.dpos (2*16)
 let y(s:ℕ):=CF.Vale.hat P.par.R.L P.par.x s; let r(s:ℕ):=W*(Real.exp (-a*((Pressure.radiusB (y s)/10:ℕ):ℝ))*b)
 have hδ: ∀ᶠ s:ℕ in atTop,r s< δ/2:=by apply Filter.Tendsto.eventually _ (gt_mem_nhds (half_pos q)); simpa only [mul_zero,zero_mul] using (((tailDecay P a ha).mul_const b).const_mul W)
 refine ⟨δ/2,half_pos q,?_⟩; filter_upwards [K,hδ,age_above P.run P.par.U.roundZ] with s h w hv i k hk J T X Z f d V R B K' F
 let N:=age P.run i s; let g':=gridTulip g (0:Site N); let A:=_root_.Zephyr.Chern.stream N; let Z':=payAng g' A; let H(t:ℝ):= (_root_.Zephyr.Chern.petals Z' t)
 let S(t:ℝ):= _root_.Zephyr.Chern.petals A t; let Y(t:ℝ):=traceJet Z Z' t
 let L:= List.ofFn (id:Axis→Axis); let E:=fun t=> Matrix.trace (tapestryQ P.par R.J.M N (H t)* windmill 0 m)
 let G:=fun t=> squareSum (fun y=> fullSite P i k s (mPath g' y) t) m L (wrap _ 0)
 have he: (fun t=> dollar g*(E t).re)=ᶠ[𝓝 0] fun t=> (G t).re:=by
    filter_upwards [petals_safe A P.par.dpos] with t ht; unfold E G; rw [wind_read,map_zero]; have hz(i':Site N):dollar g*(siteRead i' (tapestryQ P.par R.J.M N (H t))).re= (fullSite P i k s (mPath g' i') t).re:=by
       dsimp only [H]; rw [← travels, weaveT g (0:Site N) i' (S t) R.J.M ht (hv i),←mul_assoc,show dollar g*dollar g=1 from (by cases y:Spire.detX g <;>simp [dollar,y]),one_mul]; rfl
    exact byApply g m L 0 (fun y=> siteRead y (tapestryQ P.par R.J.M N (H t))) (fun y=> fullSite P i k s (mPath g' y) t) hz -- tune
 have hG: Bud G ∧ δ ≤ (bud G 2).re:= h i k
 have hA: Temper (node (0:Site N)) A 16:= by rw [node,map_zero,zero_add]; exact stream_mild N
 obtain ⟨u,V'⟩:= inTrace V.ropes.tubes.tailX T' (ledgerQ g A 16 hA); have hzY: Bud Y:=u
 obtain ⟨u',Zt⟩:= inTrace V.ropes.tubes.capX.pay T' (ledgerQ g A 16 hA)
 have Hl:F=ᶠ[𝓝 0] traceJet X Z' := by rw [show F= fun t=>traceMeter B K' 0 X (H t) from funext fun t=>congrArg (traceMeter B K' (0:Site N) X) (travels g' A t)]; exact meter_pass _ _ V.pulse.roof V.pulse.reach
 have Hf: Bud F:=(u'.bloom.congr Hl).1
 have ht:E=ᶠ[𝓝 0] fun v=> F v+Y v:=by
    filter_upwards [Hl,petals_safe Z' P.par.dpos] with v p y; unfold E; rw [p]; change Matrix.trace ((funde _ _ _ _- _) * _)=_ ; rw [V.ropes.tubes.readsX _ y, Matrix.trace_add]; rfl
 let e:=(Hf.bloom.add hzY.bloom).congr ht; have hp := ((YM.CF.Swell.Sonar.toReal hG.1.bloom).congr (show (fun i=> (dollar g:ℂ)*((E i).re:ℂ)) =ᶠ[𝓝 0] fun i=>((G i).re:ℂ) from he.mono fun i t=> by dsimp only at t ⊢; rw [←Complex.ofReal_mul,t])); have hW:= hp.unique ((YM.CF.Swell.Sonar.toReal e).scale (dollar g))
 have hh: B.B=Pressure.radiusB (y s):=by have hv0:B=P.run.meter.a s:= (((P.run.voyage i).X (P.run.uv k)).pull.owns s hk.le).width.symm; rw [hv0]; exact (P.run.meter.boot s).2.1 -- replace
 refine ⟨Hf,?_⟩
 have hq:(dollar g)*(bud Y 2).re<δ/2:=by refine (le_abs_self _).trans_lt ?_; rw [abs_mul,dollar_fixed,one_mul]; apply lt_of_le_of_lt (Complex.abs_re_le_norm _); apply (V' _).trans_lt; exact hh.symm ▸ w
 have Hδ:(bud G 2).re=dollar g*((bud F 2).re+(bud Y 2).re):=by
    have h:= congrArg Complex.re (congrFun hW 2); simpa only [Complex.ofReal_re, Complex.re_ofReal_mul, Pi.smul_apply, smul_eq_mul,Pi.add_apply,Complex.add_re] using h
 linarith only [hq,Hδ,hG.2]
where byApply {N:Side}(g:Signed)(m:ℕ)(L:List Axis)(o:Site N)(f z:Site N→ℂ)(h:∀ i,dollar g*(f i).re=(z i).re): dollar g*(squareSum f m L o).re=(squareSum z m L o).re:=by
       induction L generalizing o with
       | nil=> exact h _
       | cons i l e=> unfold squareSum stripSum; simp_rw [Complex.re_sum,Finset.mul_sum]; exact sum_congr rfl fun _ _=> e _
end YM.CF.Swell.Sonar
