import YM.CF.Pec.Aid
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N: Side}{a b:ℝ}
lemma folioP{P:Pride n}(p:WordK P)(x:Site n): ∀ i j, mom (P x) i j=mom (P 0) i j:=by intro i j; have he: rebate x P=P:=funext fun i=> funext fun j=>funext fun w=> p ..; rw [←zero_add x, ← word_p,he]
lemma potP {W:Pride n}(p: merit W) : merit (stageM W):=by
 intro x y z; unfold stageM mom; simp_rw [Pi.smul_apply, Finset.sum_apply, ← Finset.smul_sum] 
 let f(i j:Orig n)(k:Site n):= rebate k W x (Sum.inl (i,y)) (Sum.inl (j,z))
 have he : ∑ i:Orig n,∑ j:Orig n,∑ k:Site n,f i j k=∑ k:Site n,∑ i:Orig n,∑ j:Orig n,f i j k:=by rw [sum_comm (s:=(univ:Finset (Site n)))]; apply sum_congr rfl; intro i _; rw [sum_comm]
 change torch n • (∑ i,∑ j,∑ k,f i j k)=0; rw [he,sum_eq_zero,smul_zero]; intro i _; change mom ((rebate i W) x) y z=0; rw [word_p]; exact p ..
lemma repLag(t:Cover)(K:Pride n)(x:Post n):zinger (rebate (wrap n t) K) (Yg (lagX t) x)=zinger K x:=by
 let a:= wrap n t
 unfold zinger; conv_rhs=> rw [←Equiv.sum_comp (Equiv.addRight a)]; -- indent
 apply sum_congr rfl; intro i hi
 unfold tag; conv_rhs=> rw [←Equiv.sum_comp (feedback a)]
 have he(k): silt (node i) k (Yg (lagX t) x) = silt (node (i+a)) (feedback a k) x:=by unfold silt a; rw [Ylag,y_up,hose,virtue,pin_v]
 simp_rw [he]; refine sum_congr rfl ?_; intro v _; conv_rhs=>rw [←Equiv.sum_comp (feedback a)]
 rfl
lemma vibe(t:Cover)(K:Pride n)(U:Post n):zinger (rebate (wrap n t) K) U=zinger K (Yg (lagX (-t)) U):=by have he:= repLag t K (Yg (lagX (-t)) U); rw [←kor,trips,neg_add_cancel,show lagX 0=incX 1 from rfl,blank] at he; exact he
abbrev letter(W:Pride n)(X:Cloud n):=∑ i:Site n,datam (node i) (W i) X
lemma hut(t:Cover)(K:Pride n)(x:Cloud n): letter (rebate (wrap n t) K) x=letter K (SubMotion (-t) x):=by
 apply tendsto_nhds_unique (zdata (rebate (wrap n t) K) x); refine (zdata K _).congr fun i=>?_ ; simp only [Function.comp_apply, vibe,← height]
lemma letter_n{κ:Type}[Fintype κ](W:κ→Pride n)(f:Pride n)(x:Cloud n)(v:ℝ)(h:f=v •∑ i,W i):letter f x=v • ∑ i,letter (W i) x:=by
 unfold letter datam; rw [h]; simp only [Pi.smul_apply,Finset.sum_apply]; simp_rw [smul_comm _ v, Finset.smul_sum]; rw [sum_comm (s:=(univ:Finset κ))]; apply sum_congr rfl; intro i _; rw [sum_comm (s:=(univ:Finset κ))]; refine sum_congr rfl ?_; intro j _; rw [sum_comm]
lemma cook {W:Pride n}{f:Cloud n→ℂ}{Q:Cloud n→ℂ}(H:Nacre.crystal 2 f Q)(h:∀ t x,∀ᶠ s:ℝ in 𝓝 0, f (s • SubMotion t x)=f (s • x))(ht:letter W=Q):letter (stageM W)=Q:=by
 have hp(t:Cover)(x:Cloud n): Q (SubMotion t x)=Q x:=by apply tendsto_nhds_unique (H (SubMotion t x)); refine (H x).congr' ?_; filter_upwards [(h t x).filter_mono nhdsWithin_le_nhds] with s hs; rw [hs]
 funext x; have he(i:Site n):letter (rebate i W) x=Q x:= by rw [← wrap_lift i,hut,ht,hp]
 rw [letter_n (κ:=Site n) (fun i=>rebate i W) (stageM W) x (torch n) rfl]; simp_rw [he]; simp only [torch, sum_const, card_univ, ←Nat.cast_smul_eq_nsmul ℝ,smul_smul]; rw [inv_mul_cancel₀ (by positivity),one_smul] -- let proof
variable {T:RG.StepData (More n) (More N)}{F: Forest T.ratio}{z:Cloud n→AxisChart group F}
lemma tourists (H:Nativity F z)(K:Pride N):
 Nacre.crystal 2 (fun x=> zinger K (baby F z x)) (fun x=> letter K (fderiv ℝ (Iteration.chartOf F z) 0 x)):=by
 obtain ⟨P,V⟩:= asideF ((tick0 K).of_le (m:=(2:WithTop ℕ∞)) le_top) _ (zdata K); intro x; dsimp only; rw [show letter K _= _ from V _]; refine ((ride_eps ((tick0 K).of_le le_top) _ (H.kala.of_le le_top) H.icicle P).2 x).congr' ?_; filter_upwards [((Hull.ray_home x).eventually H.foldM).filter_mono nhdsWithin_le_nhds] with s hs; rw [hs]; rfl
lemma tip_p {G:Ratio n N}(e:T.ratio=ratio G)(H:Nativity F z){K:Pride N}(p:WordK K)(t:Cover)(x:Cloud n):∀ᶠ s:ℝ in 𝓝 0, zinger K (baby F z (s • SubMotion t x))=zinger K (baby F z (s • x)):=by
 have he:= H.translation (x:=fun s:ℝ=>s • x) (y:=fun s:ℝ=>s •SubMotion t x) (by fun_prop) (zero_smul ..) (by fun_prop) (zero_smul ..) e t (Eventually.of_forall fun s=>height ..)
 filter_upwards [he] with i ⟨u,v,w⟩; rw [w,fine_g,show Shape.broad G (lagX t)=lagX (G.count.val • t) from rfl,wageJ p]
lemma tour_s {G:Ratio n N}(e:T.ratio=ratio G)(H:Nativity F z)(W:Pride N){P:Pride n}(t:letter P= letter W ∘(fderiv ℝ (Iteration.chartOf F z) 0)): Nacre.crystal 2 (pigment W ∘baby F z) (diem P):=by
 intro x; let U(s:Signed)(i:ℝ):= pays s ((i^2)⁻¹ • zinger W (Yg (incX s) (baby F z (i • x))))
 have he(s:Signed): Tendsto (U s) (𝓝[≠] 0) (𝓝 (pays s (letter P (litX s x)))):=by
    rw [t]; refine (((pays s).continuous.tendsto _).comp (tourists H W (litX s x))).congr' ?_
    have hx:= H.slash (x:=fun s:ℝ=>s • x) (y:=fun v:ℝ=>v • litX s x) (by fun_prop) (zero_smul ..) (by fun_prop) (zero_smul ..) e s (Eventually.of_forall fun i=> (roomy ..).symm)
    filter_upwards [hx.filter_mono nhdsWithin_le_nhds] with i ⟨u,q,r⟩; change pays s _=U s i; unfold U; dsimp only; rw [r,fine_g,show (incX s).broad G=incX s from ?_]; simp [incX,Shape.broad]
 refine (((tendsto_finsetSum (s:=univ) fun s _=> he s)).const_smul ((Fintype.card Signed:ℝ)⁻¹)).congr (fun i=> ?_); unfold pigment lexn Function.comp U; simp_rw [map_smul]; rw [← Finset.smul_sum, smul_comm ((Fintype.card Signed:ℝ)⁻¹) ((i^2)⁻¹)]
end YM.CF.Pec
