import YM.CF.BPress.Pf.Brooks
/- Gauge covariance (on all these compression/grant domains). `Frame` only needs P,Q fixed for moving. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass Helm Thera Bridge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q:Finset I}{P' Q' A T K L B C:Op I}{x y:Wave I}{r ε:ℝ}
-- Price expansion: average real site traces later. Move everything on exact types.
namespace Frame
variable (V:UNI I)
lemma curried {M:Op I}(h:IsStarProjection M): IsStarProjection (twist V M):=⟨show _*_=_ from by rw [←map_mul,h.isIdempotentElem.eq], show star _=_ from by rw [←map_star,h.isSelfAdjoint]⟩
lemma movedX (X:Pass P' Q' L T r) : Pass (twist V P') (twist V Q') (twist V L) (twist V T) r:=by
 refine ⟨⟨curried V X.p,curried V X.q,by rw [X.l0,map_sub,map_one,map_add],by rw [←map_mul,X.orth,map_zero]⟩,curried V X.a,X.pos,X.small,?_,?_⟩;
 · exact (by simpa only [map_smul,map_mul] using (twist_mono V X.payP))
 simpa only [map_smul,map_mul,map_sub,map_one] using twist_mono V X.payQ
lemma comes (X:Pass P' Q' L T r)(u:ℝ)(h:‖u‖≤1) : let Z:= slide P' Q' L T u; let f:=twist V; let Y:=slide (f P') (f Q') (f L) (f T) u
 rent1 (f P') (f T)=f (rent1 P' T) ∧ rent0 (f P') (f T)=f (rent0 P' T) ∧ Y=f Z ∧ Trans.beam (f T) Y=f (Trans.beam T Z) ∧ Trans.pinv (f T) Y=f (Trans.pinv T Z)∧ Basement.slip (f P') (f Q') (f L) (f T) u=f (Basement.slip P' Q' L T u) := by
 intro Z f Y; have he: rent1 (f P') (f T)=f (rent1 P' T):=by unfold rent1; rw [←map_mul]; exact X.gate1.shine _
 have ht: rent0 (f P') (f T)=f (rent0 P' T):= by unfold rent0; rw [he,map_sub]
 have hx: Y=f Z:=by unfold Y Z slide; unfold coeff0 coeff1; simp only [ht,he,map_mul,map_add,map_smul]
 refine ⟨he,ht,hx,by rw [hx]; exact (X.enjoy u h).shine _,by rw [hx]; exact (X.enjoy u h).inv_move _,?_⟩
 simp only [Basement.slip,Basement.slopeP1, he,ht,map_smul,map_mul,map_add]
lemma static (p:Top A x): Top (twist V A) (acts (quant V.val) x):= by
 let U:=quantU V; refine ⟨curried V p.star,?_ ,norm_pos_iff.mp ?_⟩; rw [line_twist,show quant _= U.val from rfl,← swivel U,p.line]
 exact (norm_pos_iff.mpr p.live).trans_eq (act_unit_norm U x).symm
lemma bill_wick (M:FC I): wick (acts (quant V.val) x) (acts (quant V.val) y) (twist (quantU V) M)=wick x y M:= by
 let U:=quantU V; unfold wick; rw [show quant _ = U.val from rfl,←swivel U, act_unit_inner,act_unit_inner] -- tune
lemma pick {P:Op I}(p:IsStarProjection P): ∃ x, Top P x:= by
 obtain ⟨U,s,rfl⟩:= spot_projection _ p; let E:= basisKet s; refine ⟨_, static U (x:=E) (topOnSea (cutM_idp s) ⟨?_,?_⟩)⟩; rw [cutLine,cut_basis,if_pos (mem_singleton_self _)]; simp [E,basisKet]
lemma seed (A T C: Op I)(u:Bore A C r): (seedM (twist V A) (twist V T) (congrC V C)).trace=(seedM A T C).trace ∧ (dinoM (twist V A) (congrC V T) (congrC V C)).trace= (dinoM A T C).trace:=by
 obtain ⟨x,p⟩:= pick u.p; let H:=u.turned V; rw [← pays_right u p,←pays_left u p,←pays_right H (static V p),←pays_left H (static V p)]; have he(T):pairWave (congrC V T)= acts (quant V.val) (pairWave T):= (pair_cov ..).symm
 rw [he, ←dg_cov,bill_wick, show coupl (congrC V T)=twist (quantU V) (coupl T) from ?_,←map_star,bill_wick]; exact ⟨rfl,rfl⟩
 rw [twist_formula]; let U:=quantU V; change _=U.val*_*star U.val; rw [show U.val*coupl T=coupl (congrC V T)*U.val from coupl_cov .., mul_assoc,U.property.2,mul_one]
lemma turnsC {P:Op I}(t:twist V P=P)(q:cc P=P)(h:P*C=C*P): P*congrC V C=congrC V C*P:=by
 have hx: P*V.val=V.val*P:=by have he:= twist_product V P; rwa [t] at he
 -- transpose Pin REAL idp? need P self-adjoint via argument.
 have hp: cc P=P:=q; let U:=ccU V; have hh: twist U P=P:=by have hh:=cc_twist V P; rw [t,hp] at hh; exact hh.symm
 have he: P*star U.val=star U.val*P:=by
    have hy:= congrArg (twist (star U)) hh; rw [twist_inv] at hy; nth_rw 1 [hy]; exact twist_product (star U) P -- tune
 rw [congr_form,←mul_assoc P,←mul_assoc P,hx,mul_assoc V.val P,h,mul_assoc (V.val*C),←he]; simp only [←mul_assoc]; rfl
variable (X:ℝ→ Op I)(d:ℝ){U U':ℝ→Op I}
def atC (C:ℝ→ Op I):= fun x=> congrC V (C x)
lemma beat(q: TagG A T): TagG (twist V A) (twist V T):= ⟨by rw [←map_mul,q.1,map_zero],by rw [←map_mul,q.2]⟩
lemma s_fixed (t:twist V (cutM P)=cutM P) (q:twist V (cutM Q)=cutM Q) :twist V (shun I P Q)=shun I P Q:= by rw [shun,map_sub,map_add,map_one,t,q]
variable (J:Issued P Q A T U U' r ε)
include J
lemma transport (p:twist V (cutM P)=cutM P)(q:twist V (cutM Q)=cutM Q) : Issued P Q (twist V A) (twist V T) (atC V U) (atC V U') r ε:=by
 let f:= twist V; let rV:= J.rails; let a:=cutM P; let b:=cutM Q; let L:=shun I P Q; let A':=mood A T; let Q':=mood (f A) (f T); have hL:= s_fixed V p q; have hu(x:ℝ): tilt (f A) (f T) x=f (tilt A T x):= Spin.rotate_tilt J.proj J.she x V; have ht:mood (f A) (f T)=f A':=hu 1; have hh(x:ℝ)(t:‖x‖≤1): traceM P Q (f A) (f T) x=f (traceM P Q A T x):=by
    have he: smoothP (f a) (f b) (f L) (f A') x=f _ := (comes V rV x t).2.2.2.1; unfold L a b f at he; rw [p,q,hL] at he; unfold traceM; rw [ht]; exact he
 have S:= J.skit; refine ⟨curried V J.proj,beat V J.she,(twist_norm V T).trans_le J.near,?_ ,J.apart,?_, ?_,?_,fun v x=> by rw [hu]; exact (J.front _ x).turned _, fun v x=>by rw [ht]; exact (J.center _ x).turned _,fun v x=>by rw [hh v (tiny_t x)]; exact (J.warp _ x).turned _,fun v x=>by rw [hh 0 (by simp)]; exact (J.back _ x).turned _⟩
 · have hx:=movedX V rV; rw [p,q,hL] at hx; rw [ht]; exact hx
 · exact ⟨S.toEmpties,cut_real _,cut_real _, turnsC V p (cut_real _) S.pC,turnsC V q (cut_real _) S.qC⟩
 · unfold atC congrC; exact ((continuousOn_const.mul J.cont).mul continuousOn_const)
 intro x hx; unfold atC congrC; exact ((J.diff x hx).const_mul V.val).mul_const _
omit J in
private lemma z01 {t:ℝ}(x:t∈Set.uIcc (0:ℝ) 1) : t∈ Set.Icc (0:ℝ) 1:=by rwa [Set.uIcc_of_le zero_le_one] at x
lemma march(p:twist V (cutM P)=cutM P)(q:twist V (cutM Q)=cutM Q) : sweepR P Q (twist V A) (twist V T) (atC V U) (atC V U')=sweepR P Q A T U U':=by
 let f:= twist V; let s:= J.rails; have hu(x:ℝ): tilt (f A) (f T) x=f (tilt A T x):= rotate_tilt J.proj J.she x V; have ht:mood (f A) (f T)=f (mood A T):=hu 1; have hL:= s_fixed V p q
 have hv(v:ℝ)(x:‖v‖≤1) : traceM P Q (f A) (f T) v=f (traceM P Q A T v)∧ cue P Q (f A) (f T) v=f (cue P Q A T v):=by
    obtain ⟨_,_,_,he,ht',hg⟩:=comes V s v x; rw [p,q,hL] at hg; rw [p,q,hL] at he ht'; refine ⟨by rw [traceM,ht]; exact he,?_⟩; rw [cue,ht,hg,cue,map_mul]; unfold cabin; rw [ht, ht'] -- tune
 unfold f at hu ht hv; unfold sweepR; refine congrArg₂ (·+·) (congrArg₂ (·-·) (congrArg₂ (·+·) ?_ ?_) ?_) ?_ <;> apply intervalIntegral.integral_congr <;> intro x hx <;> dsimp only
 · unfold firstD; rw [hu]; exact (seed V _ _ _ (J.front _ (z01 hx))).1
 · unfold prepD; rw [ht]; exact (seed V _ _ _ (J.center _ (z01 hx))).2 -- seed T? wrong transformation uses both dino & seed; T input same,
 · unfold starD; rw [(hv x (tiny_t (z01 hx))).1,(hv x (tiny_t (z01 hx))).2]; exact (seed V _ _ _ (J.warp _ (z01 hx))).1
 unfold passD; rw [(hv 0 (by simp)).1]; exact (seed V _ _ _ (J.back _ (by rwa [Set.uIcc_of_le (by norm_num:(1:ℝ)≤2)] at hx))).2
end Frame
end YM.CF.BPress.Pf
