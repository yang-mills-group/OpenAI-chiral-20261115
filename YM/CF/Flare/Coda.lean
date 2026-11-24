import YM.CF.Flare.Home
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side}{b:Candle}{j:ℕ}{r C u s a:ℝ}{d:Candle}
abbrev brimV(S:Slide N d)(i:Stag N):= Kea.angle S i
def portT (S:Slide N b)(M:Jill.Male)(j:ℕ)(r s:ℝ):=openW (risky S j M r) (s*pinch N)
abbrev lakeV:= fun (_:Stag N)=> Aop
lemma torn(S: Slide N b)(g:Even N.val)(j)(M:Jill.Male)(K W V:Stag N→Op SpinIdx)(h:∀ i,Clad (field S j M i) Aop (W i) (V i) (K i)):Clad (Dofu N (field S j M)) (tickA N) (Dofu N W) (Dofu N V) (Dofu N K):=by
 let Q:=Dofu N; let B:=field S j M; have hp:tickA N= Dofu N lakeV:=landP N
 refine ⟨idol S j M g,cut_t _,?_,?_,?_,?_,?_⟩
 · rw [← Dofu_s,←map_mul,show star V*W=1 from funext fun i=>(h i).balance,map_one]
 · rw [hp,←map_mul,←map_mul,←map_mul]; exact congrArg Q (funext fun i=>(h i).left)
 · rw [hp,←map_mul,←map_mul,←map_mul]; exact congrArg Q (funext fun i=>(h i).right)
 · rw [←map_mul]; exact congrArg Q (funext fun i=>(h i).tray)
 rw [hp,←map_mul]; exact congrArg Q (funext fun i=>(h i).stem)
lemma markQ (A:Stag N→Op SpinIdx)(p:0≤C)(h:∀ i,‖A i‖≤C): ‖Dofu N A‖≤C:=by change ‖twist _ (arch A)‖≤_; rw [twist_norm,arch, StarAlgEquiv.norm_map]; exact jump_bound _ _ p h
lemma ripe_d: ∃ C:ℝ,0<C ∧∀ M:Op SpinIdx, ‖M-1‖ ≤1/2 → ‖M.det‖ ≤ C :=by
 obtain ⟨a,h⟩:= (isCompact_closedBall (1:Op SpinIdx) (1/2:ℝ)).bddAbove_image (continuous_id.matrix_det.norm.continuousOn); refine ⟨max 1 a,lt_max_of_lt_left one_pos,fun M e=>?_⟩; exact le_trans (h ⟨M,show dist M 1≤ _ from (by rw [dist_eq_norm]; exact e),rfl⟩) (le_max_right ..)
def orbT (S:Slide N b)(j:ℕ)(M:Jill.Male)(T:Stag N→Op SpinIdx)(i:Stag N):Op SpinIdx:= let H:= Aop*T i*field S j M i; H*star H+minA
lemma cool(P:Op SpinIdx)(W:Op SpinIdx)(a:ℝ)(h:0<a):let T:=Aop*W*P; let X:=a⁻¹ • T; X*star X+minA=((a^2)⁻¹ • Aop+minA)*(T*star T+minA):=by
 intro T X; have hp:Aop*T=T:=by unfold T; simp only [←mul_assoc,AOne]
 have hx:minA*T=0:=by unfold minA; rw [sub_mul,one_mul,hp,sub_self]
 unfold X; rw [star_smul, Matrix.smul_mul,Matrix.mul_smul, star_trivial, smul_smul,add_mul,mul_add,mul_add,Matrix.smul_mul,Matrix.smul_mul,←mul_assoc Aop,hp,Porth A_id,smul_zero,add_zero,←mul_assoc minA T,hx,zero_mul,minA_p.1,zero_add,←mul_inv,sq]
lemma ray_j{p:ℝ}(h:0<r)(v:p≥heave r):∃ C:ℝ, 1≤C∧∀ N:Side,Even N.val→ r *pinch N^2≤1/8→∀ s:ℝ,heave r≤s→s≤p→∀ b:Candle,∀ S:Slide N b,∀ (j:ℕ) (M:Jill.Male) (i:Stag N), let f:=Jill.cup N j M r (brimV S i); let U:= portT S M j r s; ‖(orbT S j M U i).det‖≤ (if i∈risky S j M r then C else 1)*f^2 :=by
 obtain ⟨c,k,K⟩:=ripe_d; refine ⟨max 1 (c*p^4/r^2),le_max_left ..,fun N g w s b u t S j M i=>?_⟩; intro f U
 let T:=risky S j M r; by_cases e:i∈T; swap
 · obtain ⟨P,q,F,X⟩:= crestQ j M S g i; have ht:U i=1:=by simp [U,portT,openW,shake, show i∉ risky _ _ _ _ from e]
   let d:=disk j M (brimV S i); have he:0≤d:=norm_nonneg _; have hv:r*pinch N^2 ≤ d:=le_of_lt (lt_of_not_ge (fun x=>e (mem_filter.mpr ⟨mem_univ _,x⟩)))
   rw [orbT,ht,mul_one]; rw [star_mul,P.isSelfAdjoint.star_eq,Aadj,←mul_assoc,mul_assoc Aop (field _ _ _ _) (field _ _ _ _),P.isIdempotentElem.eq,footQ S g, seatQ,if_neg e]; change ‖(d:ℂ)^2‖≤ 1*(max _ d)^2; rw [norm_pow,Complex.norm_real,max_eq_right hv,Real.norm_of_nonneg he,one_mul]
 obtain ⟨P,q,F,X⟩:= crestQ j M S g i; let d:=high_d M S i j; have hp:0≤d:=norm_nonneg _; have hm:d≤r*pinch N^2:=(mem_filter.mp e).2; let a:=s*pinch N; have hv:=pinch_pos N; have hh:0<s:=lt_of_lt_of_le (heave_p _) b; have ht:0<a:=mul_pos hh hv; have hl:Real.sqrt d ≤ a/16:=by
   have he:=Real.sqrt_le_sqrt hm; rw [Real.sqrt_mul h.le,Real.sqrt_sq hv.le] at he; unfold a; unfold heave at b; nlinarith
 obtain ⟨hg,H⟩:=Low.serv P hp F X ht hl (hm.trans w); have hz:U i=1+a • warpF:=by unfold U portT openW; simp [shake,(show i∈ risky _ _ _ _ from e)]; rfl -- tune
 let Q:=field S j M i; rw [← hz,cool Q _ a ht] at H -- cool is ∗
 let G:=orbT S j M U i; have he:=K _ H; change ‖(( ((a^2)⁻¹ • Aop+minA))* G).det‖ ≤ c at he; rw [Matrix.det_mul, ← BZ.ofReal_action, seatQ,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at he; rw [if_pos e]
 rw [show f=_ from (show f=r*pinch N^2 from max_eq_left hm)]; apply (le_trans (b:= a^4*c)); · field_simp at he; linarith
 apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)); unfold a; rw [mul_pow]; calc
    _ ≤ p^4 * pinch N ^4 * c := by gcongr
    _ = _:= by field_simp
lemma octant(J)(H:1≤J)(p:0<r)(t:heave r≤s):∃ C:ℝ,1≤C∧∀ N:Side,Even N.val → r *pinch N^2≤1/8→∀ b:Candle,∀ S:Slide N b,∀ (M:Jill.Male)(v:ℝ),heave r≤v→v≤s→∀ W:Wave (Single N),Sea (Dofu N (field S J M)) W → ‖skyGlow (mateK N) (Dofu N (portT S M J r v)) W‖ ≤ C*iceK J S M r:=by
 obtain ⟨A,D⟩:=risky_card J H _ p; obtain ⟨c,t,B⟩:=ray_j p t; refine ⟨c^A,one_le_pow₀ t,fun i g hx b Y M v u t' W w=> ?_⟩
 let f:= portT Y M J r v; let U:= Dofu i; let Q:= field Y J M; let a:= tickA i; let y:=skyGlow (mateK i) (U f) W
 have hp:∏ k:Stag i, ‖(orbT Y J M f k).det‖ = ‖y‖^2 :=by
    have hv:=prismK (idol Y J M g) (cut_t _) (meanV Y J M) (U f) W w (mateK i) (tickB i) -- tune
    dsimp only at hv; change _= Matrix.det _ at hv; let A':=a*U f*U Q
    have hr:A'*star A'+(1-a)=U (orbT Y J M f):=by
      have he:A'=U (lakeV*f*Q):=by unfold A'; rw [map_mul,map_mul, show a=U lakeV from landP i]
      rw [he,←Dofu_s,←map_mul, show a=U lakeV from landP i,← show U 1=1 from map_one U,← map_sub,←map_add]; rfl -- tune
    rw [hr] at hv; change (↑(‖y‖^2):ℂ) = Matrix.det (twist _ (arch _)) at hv; rw [det_d,det_a] at hv
    rw [← norm_prod,← hv,Complex.norm_real,Real.norm_of_nonneg (by positivity)] -- inspect
 let R:=risky Y J M r; let K:=iceK J Y M r; have hK:0<K:=ice_p _ _ _ p; change ‖y‖ ≤ c^A*K; apply (sq_le_sq₀ (norm_nonneg _) (by have he:= one_le_pow₀ t (n:=A); positivity)).1; rw [←hp]
 apply le_trans (Finset.prod_le_prod (f:=fun k:Stag i=> ‖(orbT Y J M f k).det‖) (fun i _=>norm_nonneg _) (fun k _=>B i g hx v u t' b Y J M k)); rw [prod_mul_distrib, Finset.prod_pow]; change (∏ i:Stag i, if i∈R then c else 1)* K^2 ≤ _
 rw [prod_ite, prod_const_one, mul_one,prod_const, show Finset.filter (·∈R) univ=R from filter_mem_eq_inter .. |>.trans (univ_inter _),mul_pow]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); have he:= D i g b Y M; rw [← pow_mul]; apply pow_le_pow_right₀ t; change R.card ≤ A at he; omega
end YM.CF.Flare
