import YM.CF.Pec.Height
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:Bed}{p:RG.Clip}{a b c d C A η:ℝ}
def signK (P:Pride n) := mom (P 0)
def flag(W:Pride n):= priceC (signK W)
def drain (W:Pride n)(K:Bed): Pride n:= W-roan (signK W)+ flag W • (roan tasteA - rushP K)
lemma drain_p {W:Pride n}(w:WordK W): WordK (drain W P):=by
 unfold drain; intro i v x y; simp only [Pi.smul_apply,Pi.sub_apply,Pi.add_apply,w i v x y, octavo P i v x y,roan_t _ i v x y]
lemma minty_m {W:Pride n}(w:WordK W)(h:Floor P p (More n) η C) (v:P.metric.strip a A)(t:0<a) : merit (drain W P):=by
 intro x i j
 have he:= bed_r h v t x
 have hx (p): mom (@roan n p x) i j=p i j:=by rw [roan_m]
 have hm:= folioP w x i j
 change _= _; rw [show mom (drain W P x) i j=mom (W x) i j - mom (@roan n (signK W) x) i j + flag W • (mom (roan tasteA x) i j - mom (rushP P x) i j) by unfold mom drain; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply,sum_add_distrib,sum_sub_distrib,smul_sub,Finset.smul_sum,sum_add_distrib,sum_sub_distrib]]
 rw [hm,hx,hx,he, sub_self,smul_zero]; change _-_+0=0; unfold signK; abel
lemma dimey(W V:Pride n)(x:Cloud n): diem (W-V) x=diem W x-diem V x:=by
 have hx:= congrFun (stemR (W-V) V) x; rw [sub_add_cancel,Pi.add_apply] at hx; rw [hx]; abel
lemma dimeQ(W:Pride n)(x:ℝ)(v:Cloud n): diem (x • W) v=x • diem W v:=by
 unfold diem datam; simp only [Pi.smul_apply]; simp_rw [smul_comm _ x,← Finset.smul_sum,map_smul]; rw [← Finset.smul_sum, smul_comm]
lemma minty_p {W:Pride n}(p:Bid.Sworn P (More n) group)(u:Cloud n) : diem (drain W P) u= diem W u-(flag W/16) • (↑(Bid.gaugeFiscal P u u):ℂ):=by
 unfold drain; rw [stemR,Pi.add_apply,dimey,dimeQ,dimey,roan_o,roan_o,show priceC tasteA=_ from price_one, fiscal_p p]; simp only [flag,Complex.ofReal_mul,one_mul,smul_sub, Complex.real_smul,Complex.ofReal_div, Complex.ofReal_inv]; ring_nf -- tune
lemma toned {P:RG.PathData group}{p:RG.Clip}{H:Bed}{η a b c d:ℝ}{Λ:ℝ}(h:P.Bounds p a b Λ)(g:Floor H p (More n) η c)(w:Attached H P)(q:Bid.Sworn H (More n) group): Nacre.crystal 2 (fun x:Cloud n=>(↑(secondTerm p P (represent x)):ℂ)) (fun x=> (↑(Bid.gaugeFiscal H x x/2):ℂ)):=by
 intro x; let S(t:ℝ):= represent (t • x)
 have hp:= Work.F03.main_limit h w g q x -- lean
 have hu := Iteration.Jets.drop (by omega:2<3) (Iteration.action_limit P.cubic h.width h.three x)
 have he := Iteration.Jets.drop (by omega:2<4) (Iteration.action_limit P.quartic h.width h.four x)
 have hk(t:ℝ): mainTerm p P (S t)- Iteration.action P.cubic (S t)-Iteration.action P.quartic (S t)=secondTerm p P (S t):=by
    unfold mainTerm secondTerm Iteration.action RG.Patch.average; simp_rw [sum_add_distrib,mul_add]; abel
 have ht :Tendsto (fun t:ℝ=> secondTerm p P (S t)/t^2) (𝓝[≠] 0) (𝓝 (Bid.gaugeFiscal H x x/2)):=by
   have hh:= (hp.sub hu).sub he; rw [sub_zero,sub_zero] at hh; apply hh.congr; intro i; rw [←hk]; simp [sub_div,S]
 exact (Complex.continuous_ofReal.tendsto _).comp ht |>.congr (fun i=>by simp only [Function.comp_apply,Complex.ofReal_div]; simp [Complex.real_smul,S,div_eq_mul_inv]; ring)
def momentBill (a A:ℝ):=1+unitK a+lime*(unitK a+ bed_c a A)
lemma oxygen(p:0<a)(v:0<A):0<momentBill a A:=by
 unfold momentBill; have ht:0≤unitK a:=mul_nonneg (by positivity) (nick_pos _ (by norm_num)|>.le); have hw:0≤ lime:=norm_nonneg _; have hh:0≤bed_c a A:=by
   unfold bed_c; have hm:0≤hailP a A:=mul_nonneg (mul_nonneg (nick_pos a (by norm_num)|>.le) (Iteration.momentPrice_pos _ (half_pos p)|>.le)) v.le; positivity
 positivity
lemma wagesP {W:Pride n}(hb:∀ x,cents (node x) (W x) b≤ C)(h:P.metric.strip a A)(p:0<a)(v:0≤b)(e:b≤a/2)(w:0≤C)(u:0<A): |flag W| ≤ lime*C∧∀ x, cents (node x) (drain W P x) b≤ C*momentBill a A:=by
 have he(i j): ‖signK W i j‖≤ C:=(summer _ _ _ _ v).trans (hb 0)
 have hx :|flag W| ≤ lime*C:=price_safe (signK W) w he
 refine ⟨hx,fun x=>?_⟩; let p':=node x; have hp(X Y:Dues n):cents p' (X-Y) b ≤ cents p' X b+cents p' Y b:=by simpa only [cents,sub_eq_add_neg,Pi.neg_apply,norm_neg] using coverG (a:=b) p' X (-Y)
 have hh:cents p' (roan (signK W) x) b≤unitK a*C:=uv _ _ v (by linarith) he; have hV:= hp (W x) (roan (signK W) x); have ht:cents p' (roan tasteA x) b≤unitK a:=(uv (b:=1) _ _ v (by linarith) (fun i j=> by by_cases h:i=j <;>simp [tasteA,h])).trans_eq (mul_one _)
 let K:= roan (n:=n) tasteA -rushP P; have hK:cents p' (K x) b≤ unitK a +bed_c a A:= (hp _ _).trans (add_le_add ht (strut h p v e x))
 have he':cents p' ((flag W) • K x) b=|flag W| * cents p' (K x) b:=by unfold cents; simp_rw [Pi.smul_apply,norm_smul, Real.norm_eq_abs,mul_left_comm _ |flag W|, ←Finset.mul_sum]
 have hH:cents p' ((flag W) • K x) b ≤ (lime*C)*(unitK a+bed_c a A):=he' ▸ mul_le_mul hx hK (Czero ..) ((abs_nonneg _).trans hx)
 apply (coverG p' (W x-roan (signK W) x) (flag W • K x)).trans; exact (add_le_add (hV.trans (add_le_add (hb _) hh)) hH).trans_eq (by unfold momentBill; ring)
end YM.CF.Pec
