import YM.SU5.FiniteGaugeData.ArchiveK.Belling
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable (x : ℝ)(q:Space3)(X:E4)(y:ℚ)
open Submodule
local notation "Ω"=> E4≃ₗᵢ[ℝ] E4
/- rational G construction. normal near diagonal. leverage polynomial explicit via vanishing at 4 real fixed points only proving poly≠0. design t.Unique. Zeta after alias.Width. D.Any larger (some). -/
section curve
def fern (x:ℝ)(a:Tang):ℝ:= 1/3+x^(a.val+1)
def frit (x:ℝ):Space3:= toLp 2 (fern x)
def boxy (x:ℝ):E4:= (1+‖frit x‖^2)⁻¹ • position ((2:ℝ) • frit x) (1-‖frit x‖^2) -- 2ℕ vs ℝ irrelevant
abbrev cone_f(x:ℝ):= 1+‖frit x‖^2
lemma cone_fire(x:ℝ): 0<cone_f x:= by unfold cone_f; positivity
lemma boxy_unit : ‖boxy x‖=1:=by
 let Q:= ‖frit x‖; rw [←sq_eq_sq₀ (norm_nonneg _) zero_le_one]; unfold boxy; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (cone_fire _).le), mul_pow,norm_xray, norm_smul]; norm_num; have ht:1+Q^2≠0:=by unfold Q; positivity; -- tune
 field_simp; ring
lemma office: ∀ᶠ x:ℝ in 𝓝 0, ∀ i:Axis,(1:ℝ)/3 < boxy x i:= by
 have hv: ‖frit 0‖^2=(1:ℝ)/3:=by rw [EuclideanSpace.real_norm_sq_eq]; norm_num [frit,fern,SpaceAxis, Fin.sum_univ_succ]
 have hb: Continuous boxy:=by
    have ht:Continuous frit:= by unfold frit fern; fun_prop -- maybe `continuous_toLp`.
    unfold boxy; exact (show Continuous (fun x=> (cone_f x)⁻¹) from (continuous_const.add (ht.norm.pow _)).inv₀ (fun i=> (cone_fire _).ne')).smul (show Continuous (fun x=> rectX (WithLp.toLp 2 ((2:ℝ) • frit x,1-‖frit x‖^2))) by fun_prop)
 apply eventually_all.mpr (fun i=> ((show Continuous (fun x=>boxy x i) by exact (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hb).continuousAt (x:=0) |>.eventually (lt_mem_nhds ?_))) -- tune le_mem_nhds
 dsimp only; unfold boxy; rw [hv]; fin_cases i <;> norm_num [position, Fin.snoc, frit,fern]
-- polynomial tactic nonzero by evaluation additive.Inner etc
open Polynomial
lemma boxy_avoids (A:E4)(t:A≠0) : ∀ᶠ x:ℝ in 𝓝[≠] 0, inner ℝ A (boxy x)≠0 := by
 let Y(i:Tang):Polynomial ℝ:=Polynomial.C (1/3)+Polynomial.X^(i.val+1); let v1:Polynomial ℝ:=∑ i:Tang, Y i^2; let P : Polynomial ℝ := (∑ i:Tang, Polynomial.C (2*A i.castSucc) * Y i) + Polynomial.C (A 3)*(1-v1)
 have he(i:Tang)(x:ℝ): (Y i).eval x= fern x i:= by simp [Y,fern]
 have ht(x:ℝ) : P.eval x = cone_f x *inner ℝ A (boxy x):=by
    unfold P; simp only [v1,eval_add,eval_mul,eval_C,eval_finsetSum,eval_sub,eval_pow,he,eval_one]; unfold boxy; rw [real_inner_smul_right, mul_inv_cancel_left₀ (cone_fire x).ne']; rw [pis,foldBig]; congr 1 -- tune
    · apply Finset.sum_congr rfl; intro i _; simp [position,frit]; ring
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
 -- evaluate P at ±1, ±2, 0. even pieces include t², t⁴ from v3 & v2.e. eliminate etc. use norm_num & linarith only.
 have hp: P≠0:=by
    intro v; have h(x:ℝ):P.eval x=0:=by rw [v]; simp; -- precedence
    have hu:= h 0; obtain p:=h 1; have hz:=h 2; obtain s:=h 3; have vk:=h 4; apply t; unfold P v1 Y at p s vk hu hz -- Y order
    norm_num [Tang, Fin.sum_univ_succ] at p s vk hu hz
    apply PiLp.ext; intro i; change A i=0; fin_cases i <;> linarith! only [p,hz,s,vk,hu]
 have hc: Set.Finite {x| P.eval x=0}:= Polynomial.finite_setOf_isRoot hp
 exact (hc.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite (0:ℝ))).mono (fun x u w=>u (by change P.eval x=0; rw [ht,w,mul_zero]))
end curve
set_option linter.unusedSimpArgs false
section ration
-- exists pole avoiding short hyp.G. checkout integer-orth scaled frame. Big denomin; permit enlarging up to Nature.
def augQ (x:E4):= ∃ p:Axis→ℚ, x=toLp 2 (fun i=>(p i:ℝ))
lemma quinQ : augQ (boxy y) := by
 let f(i:SpaceAxis):ℚ:=1/3+y^(i.val+1); let t:=∑ i:SpaceAxis,(f i)^2; let p : Axis→ℚ:= full (fun i=> 2*f i/(1+t)) ((1-t)/(1+t)); have he: ‖frit (↑y)‖^2=(t:ℝ):=by rw [EuclideanSpace.real_norm_sq_eq]; unfold t; push_cast; apply Finset.sum_congr rfl; intro i _; unfold f frit fern; push_cast; rfl -- tune
 refine ⟨p,?_⟩; unfold boxy; rw [he]; apply PiLp.ext; intro i; refine Fin.lastCases ?_ (fun i=> ?_) i
 · change (1+(t:ℝ))⁻¹*((1-(t:ℝ)):ℝ)= (((1-t)/(1+t):ℚ):ℝ); push_cast; ring
 simp only [WithLp.ofLp_toLp,p,full_before,position,PiLp.smul_apply,smul_eq_mul,Fin.snoc_castSucc]; unfold frit fern f; push_cast; ring
lemma vaunt (x:E4) (v:augQ x)(t:‖x‖=1) : ∃ G:Ω, sailX G=x ∧ ∀ j:Axis,augQ (G (YM.basis j)):=by
 let a:Axis:=3; let A:= YM.basis a; let B:=A-x; let G:=reflection (ℝ ∙ B)ᗮ; have ht: ‖A‖=‖x‖:=(YM.basis_norm _).trans t.symm
 refine ⟨G,?_,fun j=>?_⟩
 · unfold sailX; rw [up_G]; rw [show position 0 1=A from ?_]; exact reflection_sub ht; unfold A a; apply PiLp.ext; intro i; fin_cases i<;> norm_num [position,Fin.snoc] <;> decide
 obtain ⟨u,h⟩:=v; let b(i:Axis):ℚ:=if i=a then 1-u i else -u i; have hb(i:Axis): B i= (b i:ℝ):=by unfold B b A; split_ifs with hv <;> simp [hv,h]
 let R:= ∑ i:Axis,b i^2; have hr: ‖B‖^2=(R:ℝ):=by unfold R; rw [EuclideanSpace.real_norm_sq_eq]; simp_rw [hb]; push_cast; rfl -- tune
 let f(i:Axis):ℚ:=(if i=j then 1 else 0)-2*(b j/R)*b i; refine ⟨f,?_⟩; unfold G; rw [reflection_orthogonal_apply,reflection_singleton_apply, ← real_inner_comm B, YM.basis_inner, RCLike.ofReal_real_eq_id,id_eq,hr]; apply PiLp.ext; intro i; rw [hb]; unfold f; simp only [WithLp.ofLp_toLp, PiLp.neg_apply, PiLp.sub_apply, two_smul, PiLp.add_apply,PiLp.smul_apply, smul_eq_mul, hb,YM.basis_eq]; split_ifs <;> push_cast <;> ring
lemma aug_mul_denom {Q:Type}[Fintype Q] (F:Q→E4)(p:∀ i, augQ (F i))(D:ℕ) : ∃ (m :ℕ),D<m ∧ ∀ i: Q,∃ z:Cover, emitX z=(m:ℝ) • F i:=by
 choose f hf using p; let F'(j:Q×Axis):= f j.1 j.2; let M:= ∏ i:Q×Axis,(F' i).den; let m:=(D+1)*M; have he:0<M:= Finset.prod_pos (fun i _=>(F' i).den_pos); have hh(x:Q×Axis): (F' x).den ∣ m:= (Finset.dvd_prod_of_mem (fun i=>(F' i).den) (mem_univ x))|>.trans (Nat.dvd_mul_left _ _); choose g hv using hh
 refine ⟨m,(by unfold m; nlinarith [he]),fun i=> ⟨fun j=> ((g (i,j):ℕ):ℤ)*(f i j).num,?_⟩⟩; apply PiLp.ext; intro j; rw [hf i]; simp only [emitX,ofLp_toLp,PiLp.smul_apply,smul_eq_mul]; let k:= F' (i,j); have hy: k.num/k.den=k:= (Rat.num_div_den k); rw [hv (i,j)]; change (↑((g (i,j):ℤ)*k.num):ℝ) = ((↑(k.den*g (i,j)):ℝ):ℝ) *(k:ℝ); have ht:k.den≠0:= k.den_nz; nth_rw 1 [show (k:ℝ) = _ from (Eq.symm (congrArg ((↑):ℚ→ℝ) hy))]; push_cast; field_simp
structure ZephyrG (G:Ω)(D:ℕ)(m:ℕ):Prop where
 unitC:0<D
 flat (a:Axis): (1:ℝ)/3 ≤ sailX G a
 apart (y:Cover)(u:y∈ Lattice.box m)(t:y≠0): depthG G (emitX y)≠0
 roof (a:Axis) : ∃ z:Cover, emitX z=(D:ℝ) • G (YM.basis a)
lemma unusual(m K:ℕ):∃ G D,K<D∧ ZephyrG G D m:=by
 let f(z:Cover): E4:= emitX z; let T:= (Lattice.box m)\{0}; let P:ℝ→Prop:=fun x=> (∀ i:Axis,(1:ℝ)/3<boxy x i)∧(∀ z∈ T, inner ℝ (emitX z) (boxy x)≠0); have hp:∀ᶠ x in 𝓝[≠] 0,P x:= (office.filter_mono nhdsWithin_le_nhds).and ((eventually_all_finset T).mpr (fun i t=>boxy_avoids _ (by rw [← emit_origin]; exact emit_in.ne (by simpa using (mem_sdiff.mp t).2))))
 obtain ⟨v,t,u⟩:= Metric.mem_nhdsWithin_iff.mp hp; obtain ⟨q,hq,y⟩:=exists_rat_btwn t; obtain ⟨G,B,Q⟩:= vaunt _ (quinQ q) (boxy_unit _); obtain ⟨D,hD,P'⟩:= aug_mul_denom _ Q K; have he:P (q:ℝ):=u ⟨(by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hq] using y),hq.ne'⟩; refine ⟨G,D,hD,by omega,fun i=> ?_, fun v t u=> ?_,P'⟩; · rw [B]; exact (he.1 i).le
 unfold depthG; rw [B,real_inner_comm]; exact he.2 _ (mem_sdiff.mpr ⟨t,by simp [u]⟩)
end ration
#print axioms unusual
section equip
variable {G:Ω}{D m:ℕ}(S:ZephyrG G D m)
def runeX(a:Axis):Cover:= (S.roof a).choose
local notation "Γ"=> emitX
@[simp] lemma rune_p(i:Axis): emitX (runeX S i)=(D:ℝ) • G (YM.basis i):= (S.roof i).choose_spec
lemma seed_basis (i:Tang): seedX G (EuclideanSpace.single i 1)= G (YM.basis i.castSucc):=by
 rw [seedX,up_G]; apply congrArg; apply PiLp.ext; intro j; refine Fin.lastCases ?_ (fun k=> ?_) j; change (0:ℝ)= YM.basis i.castSucc 3; symm; rw [YM.basis_eq,if_neg (Ne.symm (show i.castSucc≠3 from Fin.castSucc_ne_last _))]; simp [position,PiLp.single_apply,Pi.single_apply,eq_comm] -- tune
lemma sail_basis : sailX G = G (YM.basis 3):=by unfold sailX; rw [up_G]; apply congrArg; apply PiLp.ext; intro i; fin_cases i <;> norm_num [position,Fin.snoc]<;> decide
lemma rune_camera (x:Cover): Γ (∑ i:Axis,x i • runeX S i)= (D:ℝ) • G (Γ x):=by
 let u:Cover→+E4:={toFun:= Γ, map_zero':=emit_origin,map_add':=emit_add}; rw [show Γ (∑ i:Axis,x i • runeX S i) =_ from map_sum u _ _]; have he: (∑ i:Axis,(x i) • YM.basis i) = Γ x:= by apply PiLp.ext; intro i; simp [WithLp.ofLp_sum,Finset.sum_apply, YM.basis_eq, smul_ite, eq_comm] -- tune
 simp_rw [_root_.map_zsmul, show ∀ i:Axis,u (runeX S i)=(D:ℝ) • G _ from rune_p S, show ∀ i:Axis, x i • ((D:ℝ) • G (YM.basis i))=(D:ℝ) • (x i • G (YM.basis i)) from (fun i=> smul_comm ..)] -- tune parser
 simp_rw [← map_zsmul G]; rw [← Finset.smul_sum,← map_sum G,he]
end equip
end YM.CF.Window.ArchiveK
