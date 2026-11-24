import YM.CF.Pec.Plane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n X m A L B :Side}{j k w:ℕ}{ho:Odd L.val} {Y:Pricing j L ho (Thread j)}{e d b a r:ℝ}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F: Forest T.ratio}{z:Vox m B→ AxisChart group F}
variable (H:Hull j L ho a b d e k m A B G T F z Y P)
lemma mildly {ι E:Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]{x:Positions ι}{l:ι→Site n}{y:Site n}{U:Positions ι→E}(h:Beacon l a k U y x b)(p:d≤a)(t:0≤b):Beacon l d k U y x b:=fun i e v=> (h _ e v).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg p) (Nat.cast_nonneg _))) t)
lemma beacon_n {ι E:Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]{x:Positions ι}{l:ι→Site n}{y:Site n}{U:Positions ι→E}(h:Beacon l a k U y x b)(v: ContDiffAt ℝ (↑k) U x): Beacon l a k (fun y=> -U y) y x b:=by
 intro i hi q; unfold Push.Uniform.entry; rw [show (fun y=> -U y) = (-1:ℝ) • U from funext fun i=> by simp, iteratedFDeriv_const_smul_apply (v.of_le (by exact_mod_cast hi)),_root_.smul_apply]; simp only [neg_smul,one_smul,norm_neg]; exact h i hi q -- target?
section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def deflate(V:E→ℂ)(x:E):ℂ:=V x-V 0
lemma def_c {f:E→ℂ}(h:ContDiffAt ℝ k f 0):ContDiffAt ℝ k (deflate f) 0:=h.sub contDiffAt_const
lemma cake_p {f:E→ℂ}(h:ContDiffAt ℝ k f 0)(u:0<k): cake k (deflate f)=cake k f:=by unfold cake; congr 1; rw [show deflate f=f-(fun _=> f 0) from rfl,iteratedFDeriv_sub_apply h contDiffAt_const,iteratedFDeriv_const_of_ne (ne_of_gt u),Pi.zero_apply,sub_zero] -- tune
lemma crystalH {f:E→ℂ}(h:cFoot (k+1) f)(p:ContDiffAt ℝ k f 0): Nacre.crystal k f 0:=by rw [show (0:E→ℂ)=trim k f from ?_]; exact (argent p).mp (fun i hi=> h i (hi.trans (Nat.lt_succ_self _))); unfold trim Tensor.diagonal cake; simp only [h k (Nat.lt_succ_self _),smul_zero]; rfl
end
lemma bio {V:Cloud n→ℂ}(h: Vale V): Vale (deflate V):=by
 constructor; intro g x; filter_upwards [h.life g x] with t ht; unfold deflate; rw [ht]
 intro x z; filter_upwards [h.pier x z] with t ht; unfold deflate; rw [ht]
lemma shine {f:Cloud n→ℂ}(V:Pride n)(ht:∀ t x,∀ᶠ s:ℝ in 𝓝 0,f (s • SubMotion t x)=f (s • x))(hs:∀ i x,∀ᶠ s:ℝ in 𝓝 0,f (s • litX i x)=pays i (f (s • x))) (p:Nacre.crystal 2 f (letter V)) : Nacre.crystal 2 f (diem (stageM V)):=by
 let X:=stageM V; have hy:= cook p ht (W:=V) rfl; have hh:Nacre.crystal 2 f (letter X):= hy.symm ▸ p
 intro i; have he(k:Signed): pays k (letter X (litX k i))= letter X i:=by
    have hx:Tendsto (fun t:ℝ=> pays k ((t^2)⁻¹ • f (t • litX k i))) (𝓝[≠] 0) (𝓝 (pays k (letter X (litX k i)))):= ((pays k).continuous.tendsto _).comp (hh (litX k i))
    apply tendsto_nhds_unique _ (hh i); apply hx.congr'; filter_upwards [(hs k i).filter_mono nhdsWithin_le_nhds] with t ht; simp only [map_smul, ht,complX,sign_seq,Bool.xor_self]; rfl
 rw [show diem (stageM V) i= letter X i from ?_]; exact hh i; unfold diem; change ((Fintype.card Signed):ℝ)⁻¹ • (∑ s:Signed,pays s (letter X _))= _; simp_rw [he]; rw [sum_const,card_univ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul, inv_mul_cancel₀ (by positivity),one_smul]
lemma ink_w (K:Pearl P)(g:Stamped j L ho Y)(px:Spack j L ho a b d k)(ha:0<a)(hc:0<b)(hd:0<d)(hu:0<e)(hp:1≤j) {r s c l:ℝ}(t:0<r)(h:0<s)(u:0<c)(y:0<l):∃ β C:ℝ,0<β ∧ 0<C ∧∀ {m A:Side}{G:Ratio (CSide m B) (CSide A B)}{T: Roam m A B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F},Hull j L ho a b d e k m A B G T F z Y P→Horizon F z 2 c l→∀ M:Male,∀ U:Dress (CSide A B),Ample U→ ReadY F G (fun i=>foot G (U (fine group F i))) r s 2 → let X:=deflate (lush G P M U ∘ ears F z); ContDiffAt ℝ (↑(2:ℕ)) X 0 ∧∃ W:Pride (CSide m B), WordK W ∧ Nacre.crystal 2 X (diem W) ∧∀ i,cents (node i) (W i) β≤ C:=by
 obtain ⟨f,V,hf,hV,D⟩:= pollen 2 K g hu hp; obtain ⟨w,M,p,hM,X⟩:= coatPay 2 px ha hc hd t h; obtain ⟨v,R,hv,hR,Z⟩:= estimate_cost 2 p hM L ho
 let a:= min f v; have hp:0<a:=lt_min hf hv; let C:=V+R; let b':= litSpan 2 c a; have ht:= litSpan_pos (N:=2) u hp; let V':=2*(C*machinist 2 (townCost group) l a); have hV':0<V':= by have hc:=machinist_pos (N:=2) (K:=townCost group) y.le hp; unfold V' C; positivity
 obtain ⟨W,hW,B'⟩:=supplies 2 _ ht; obtain ⟨β,F',hb,hF,H⟩:=clad (half_pos ht)
 refine ⟨β,1+F'*(W*V'),hb,(by positivity),fun {m A G T F z} Q U M T' J L=>?_⟩
 intro Y'; let S:=CSide m B
 obtain ⟨V'',he,Yx⟩:= D m A G Q.fromL Q.size_p M F Q.alignT
 let W':= coatG _ ho j G M T'; have hx:ReadY F G (W'∘ hats F) w _ 2:= X _ Q.alignT Q.fromL Q.request M T' L
 let Fv:=ears F z; let Bs(x:Snap F):= hats F x
 let g(i:Site S)(x):= -(V'' i x)+(-(estimateH G (bore (W' x)) i)); let f(i):= g i ∘ Fv; let ℓ:= lush G P M T' ∘ Fv
 have hZ(i:Site S): ContDiffAt ℝ (↑(2:ℕ)) (f i) 0∧ Beacon (aTrait T) b' 2 (f i∘whisp) (T.ratio.embed (node i)) 0 V':=by
    obtain ⟨Pp,Hp⟩:= Z _ Q.alignT Q.fromL (W'∘ hats F) hx i
    let T':Snap F→ℂ:= g i ∘ Bs -- shadow
    refine feeI U u y.le ((he.regular i|>.neg).add Pp.neg:ContDiffAt ℝ (↑(2:ℕ)) T' 0) (beacon_b (he.regular i|>.neg) Pp.neg (mildly (beacon_n (he.sold i) (he.regular i)) (min_le_left ..) hV.le) (mildly (beacon_n Hp Pp) (min_le_right ..) hR.le)) hp (add_pos hV hR|>.le) (Eventually.of_forall fun x=>?_)
    change g i (ears F z (whisp x))=g i (hats F (Push.Uniform.curve (station z) x)); rw [wellPath]
 let Y(i):=deflate (f i)
 have hr(i):Vale (f i):=by refine glacier Q _ ?_; filter_upwards [paidP Q M _ J,Q.native.melod _ Q.hi G] with x h ht i'; unfold g; rw [he.gauge i i' (Fv x) ht, show W' _= _ from h i',tuneV]
 have hG(i): ContDiffAt ℝ (↑(2:ℕ)) (Y i) 0:=def_c (hZ i).1; have hV(i): Y i 0=0:=by unfold Y deflate; rw [sub_self]; done
 choose P' Jt M' using fun i:Site S=> H (node i) (bio (hr i)) (hV i) (hG i) (W*V') (show tiltV _ _ _ _ ≤ _ by rw [show cake 2 (Y i)= _ from cake_p (hZ i).1 (by positivity)]; exact B' _ V' hV'.le (hZ i).1 (hZ i).2)
 let T''(x):= W' (Fv x); have hX:ContDiffAt ℝ (↑(2:ℕ)) T'' 0:=(Q.terms M J.self).2.1.of_le le_top
 have he:T'' (0:Vox m B)=0:=by -- shadow B issue
   exact Q.kin M J.self |>.1
 let R(x):= invoice (T'' x)- trout (bore (T'' x)); obtain ⟨hD,hr'⟩:= ebbV (F:=T'') (by norm_cast) he
 have hu': ContDiffAt ℝ (↑(2:ℕ)) R 0:=((by simpa only [Nat.cast_ofNat] using hD: ContDiffAt ℝ (↑(2:ℕ)) (invoice ∘ T'') 0).sub ((trout (n:=Iota G)).contDiff.contDiffAt.comp (f:=fun x=> bore (T'' x)) _ (((hX.pow 1).const_smul _).add ((hX.pow 2).const_smul _))))
 have hpR:R 0=0:=by simp [R,he,invoice,Fock.slope,bore]; done
 have he':∀ᶠ x in 𝓝 0, ℓ x=(∑ i,f i x)-R x:=by
    filter_upwards [Q.native.melod e Q.hi G] with x hx; change lush _ _ M _ (Fv x)= _; unfold lush; rw [Yx _ hx]; change -_ - invoice (T'' x)=_; unfold R f g Function.comp; rw [tuneU, sum_add_distrib, sum_neg_distrib, sum_neg_distrib]; unfold T'' W'; unfold Fv; abel -- ℓ
 have hh: (Y') =ᶠ[𝓝 0] (fun x=>(∑ i,Y i x)-R x):=by
    have he0:= he'.self_of_nhds; filter_upwards [he'] with x hx; change ℓ x-ℓ 0= _; unfold Y deflate; rw [he0,hpR,sub_zero,hx, sum_sub_distrib]; abel
 refine ⟨((ContDiffAt.sum fun i _=> hG i).sub hu').congr_of_eventuallyEq hh,stageM P',repose _,shine P' (fun t i=> ?_) (fun s i=>?_) ?_,fun i=> (W_h_cost Jt i).trans (le_add_of_nonneg_left zero_le_one)⟩
 · filter_upwards [(nycR Q M T' J K i).1 t] with x hx; change ℓ _-ℓ _=ℓ _-ℓ _; rw [show ℓ (x • SubMotion t i)= _ from hx]
 · have hp:= (nycR Q M T' J K i).2 s; have hy:ℓ 0= pays s (ℓ 0):=by have ht:=hp.self_of_nhds; simpa only [ℓ, zero_smul] using ht
   filter_upwards [hp] with x hx; change ℓ _-ℓ _= pays _ (ℓ _-ℓ _); rw [show ℓ (x • litX s i)= pays s (ℓ (x • i)) from hx,map_sub,←hy]
 intro x; have ht(i):cFoot 2 (Y i):=Vale.first (bio (hr i)) (hV i) ((hG i).of_le (by norm_num))
 have hz(i):Nacre.crystal 2 (Y i) (datam (node i) (P' i)):= (M' i) ▸ (argent (hG i)).mp (ht i)
 have hv:= (tendsto_finsetSum (s:=univ) fun i _=> hz i x).sub (crystalH hr' hu' x); rw [Pi.zero_apply,sub_zero] at hv
 apply hv.congr'; filter_upwards [((Hull.ray_home x).eventually hh).filter_mono nhdsWithin_le_nhds] with t h; rw [h, smul_sub _ (∑ i,Y i (t • x)),Finset.smul_sum]
end YM.CF.Pec
