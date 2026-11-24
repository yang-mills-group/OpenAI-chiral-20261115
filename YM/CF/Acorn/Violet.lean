import YM.CF.Acorn.Clover
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(S:Broc.Table m B)
lemma peakC {F:Boat m B S e → ℂ}{T:Broc.Table m B}{c C:ℝ}(p:Pro (StemX n K S e) T F c)(hx:Inspired (dealX n K S e) (Shorn S) (artX n K S e) C n) : Pro (landX n K S e) (tentX m B T) (means (Shorn S) F) (mercury (capeX (tentX m B T)).card n C c):=by
 let W:= LUX S e
 have he: Flash W.botL (artX n K S e) n (tentX m B T) F c:=⟨⟨p.pos,fun t=>(foams (8*B.val) (mul_pos (show 0<8 by decide) B.property) _).plus (p.travel t),p.cont,p.sumline,p.reads,fun x g=> rfl⟩,p.plot⟩
 let H:= flash_mean W hx _ he (fun x=>capeL S x _) (fun x y p=>cape_h S _ x y p) (fun _ _ _ _ _ _=>rfl)
 exact ⟨H.pos,H.travel,H.cont,H.sumline,H.reads,H.plot⟩
lemma grove_foam(S:Broc.Table m B)(g:Grove (terr _) S): Grove (terr _) (tentX m B S) := (foams (8*B.val) (mul_pos (show 0<8 by decide) B.property) _).plus g
lemma raise_foam(S:Broc.Table m B)(g:Grove (terr _) S): ((tentX m B S).card:ℝ)≤ feeG (8*B.val)*S.card:= (foams (8*B.val) (mul_pos (show 0<8 by decide) B.property) _).band g
lemma cape_n(S:Broc.Table m B):(capeX S).card≤ 2*S.card:=by unfold capeX; simp only [Finset.card_product, card_univ,Fintype.card_bool]; exact Nat.mul_le_mul_left _ (rate_cap S) -- tune
abbrev rateC (a:ℝ)(B:Side):ℝ:= a/(2*feeG (8*B.val))
lemma gather_v (B:Side)(a:ℝ)(ha:0<a)(C:ℝ)(h:0≤C)(n:ℕ): ∃ K:ℝ,0<K ∧ ∀m (S:Broc.Table m B) (v:ℝ),Grove (terr _) S→0≤v → rent (rateC a B/2) (tentX m B S)*mercury (capeX (tentX m B S)).card n C v ≤ K*(rent a S*v):=by
 let W:=feeG (8*B.val); have he:0<W:=by unfold W feeG; positivity
 let p:=rateC a B; have hp:0<p:= div_pos ha (mul_pos (by norm_num) he)
 obtain ⟨K,hK,H⟩:=stash C h n hp
 let J:= max 1 K
 refine ⟨J,lt_max_of_lt_left zero_lt_one, fun m S v hx ht=> ?_⟩
 let y:=tentX m B S; let F:=mercury (capeX y).card n C v; have hv:0≤ F:=ht.trans (bigger _ _ ht h)
 apply le_trans _ (le_trans (H v ht (2*y.card) _ (cape_n _)) _)
 · apply mul_le_mul_of_nonneg_right _ hv; apply Real.exp_monotone; gcongr; unfold y; omega
 apply mul_le_mul (le_max_right ..) _ (by positivity) (lt_max_of_lt_left zero_lt_one).le; apply mul_le_mul_of_nonneg_right _ ht; apply Real.exp_monotone
 push_cast; change p*(2*_ )≤_; unfold p rateC; change a/(2*W)*(2*_ )≤_; have hg:= raise_foam _ hx; calc
   _ ≤ a/(2*W)*(2*(W*S.card)) := by gcongr
   _ = _:=by field_simp
lemma restore_x {χ:Type}[LinearOrder χ][Fintype χ]{T:Type}[Fintype T] (A:T→ Boat m B S e→ℂ)(c:T→ℝ)(p:∀i,Continuous (A i) ∧ ∀ y,‖A i y‖≤c i)(L:T→FC χ)(F G:Castle m B e S→ Wave χ) (h:∀ y: Boat m B S e,acts (∑ i:T,A i y • L i) (F y.val.1)=G y.val.1)(x: Castle m B e S) : acts (∑ i:T,means (Shorn S) (A i) x • L i) (F x)=G x:=by
 let J:=Shorn S x; let Y:=I (Index m) → Ballot; let Q(t:T)(v:Y):=cream (Shorn S) (A t) (x,v); let T':= F x
 have he(t:T): Continuous (Q t):= (cream_gift (Shorn S) (A t) (c t) (sh_c S) (p t).1 (p t).2).weighted.comp (show Continuous (fun v:Y=>(x,v)) from continuous_const.prodMk continuous_id)
 have hp(y:Y): ∑ i:T,Q i y • acts (L i) T'=fall J y • G x:=by
   by_cases g: fall J y≠0
   · let q:Boat m B S e:=⟨(x,y),g⟩
     have hl(i:T): Q i y=fall J y • A i q := congrArg (fun t:ℂ=>fall J y • t) (sampler_p (A:=Shorn S) (A i) (x,y) g) -- tune
     simp_rw [hl,smul_assoc,← Finset.smul_sum]; have hx:= h q; rw [act_sum] at hx; simp_rw [act_smul] at hx; exact congrArg (fun t:Wave χ=> fall J y • t) hx
   rw [not_not] at g; simp_rw [show ∀ i:T,Q i y=0 from fun i=>by unfold Q cream; change fall J y • _=_; rw [g,zero_smul],g]; simp
 rw [act_sum]; simp_rw [act_smul]; unfold means; simp_rw [← integral_smul_const]; rw [← integral_finsetSum]; change ∫ y,∑ i:T,Q i y • _ ∂_=G x
 · change ∫ y,∑ i:T,Q i y • acts (L i) T' ∂_=G x; simp_rw [hp]; rw [integral_smul_const,sails_all,one_smul]
 intro i _; exact net_compact ((he i).smul continuous_const)
lemma save_x {χ:Type}[LinearOrder χ][Fintype χ] {a h C c P:ℝ}(ha:0<a)(ht:0≤h)
    (p: Inspired (dealX n K S e) (Shorn S) (artX n K S e) C n)(hp:0≤ c)(q: ∀ R:Broc.Table m B,∀ v:ℝ,Grove (terr _) R→0≤v→ rent (rateC a B/2) (tentX m B R)*mercury (capeX (tentX m B R)).card n C v ≤ c*(rent a R*v)){A:Boat m B S e→FC χ}{O:χ→ Site (Domain m B)}{F G:Castle m B e S→Wave χ}(t:Carries (StemX n K S e) O (tentX m B S) a h A P)(g:∀x: Boat m B S e,acts (A x) (F x.val.1)=G x.val.1):∃ U: Castle m B e S→FC χ, Carries (landX n K S e) O S (rateC a B/2) h U (c*rent a (tentX m B S)*P)∧∀ x,acts (U x) (F x)=G x:=by
 obtain ⟨I,o,f,l,s,k⟩:=t; let T:=Site (Domain m B); let Z:=tentX m B S; let r:=rateC a B/2; have hr:0≤r:=by unfold r rateC feeG; positivity
 let L:Tiny T (Boat m B S e) χ→Tiny T (Castle m B e S) χ:=fun v=>let y:=tentX m B v.1; (y,v.2.1,means (Shorn S) v.2.2.1,mercury (capeX y).card n C v.2.2.2)
 let U(x:Castle m B e S):= ∑ i:I,valK (L (f i)) x
 refine ⟨U, ⟨I,o,L ∘ f,fun i=> ?_,?_,fun x=> rfl⟩,?_⟩
 · let W:= f i; let M:= L W; have he(r:W.2.2.2≠0) := (l i).2 r
   refine ⟨peakC n K S (l i).1 p,fun v=>?_⟩
   change M.2.2.2≠0 at v
   obtain ⟨hx,hy,hz⟩:= he (fun r=>v (by simp [M,L,r,mercury]))
   exact ⟨((foam_in _ _ S).trans hx).trans (foam_in _ _ W.1),hy,fun i h=>foam_in _ _ W.1 (hz i h)⟩
 · apply le_trans _ (mul_le_mul_of_nonneg_left s (mul_nonneg hp (rent_pos ..).le)); rw [Finset.mul_sum]; refine sum_le_sum fun i _=> ?_
   let j:= f i; let g':=j.1; let X:=j.2.2.2
   by_cases h':X=0; · change bill r h S (L j) ≤ c*_ * bill _ _ _ j; unfold X at h'; simp [bill,L,h',mercury] -- tune
   have hv:= (l i).1.travel h'; have hx:=q g' X hv (l i).1.pos; let y:=tentX m B g'; let H:=h^j.2.1.length; let W:= mercury (capeX y).card n C X; have he:0≤H:=pow_nonneg ht _; have hh:0≤ W:= (l i).1.pos.trans (bigger _ _ (l i).1.pos p.pos) -- tune
   change cost r S y*H*W≤ c*Branch.rent a Z*(cost a Z g'*H*X)
   have ht':rent a g'=rent a Z*cost a Z g':=by
     have hd:Z⊆g':= (l i).2 h'|>.1; have hg : g'.card= Z.card+(g'\Z).card:=by rw [Finset.card_sdiff_of_subset hd]; have h:=card_le_card hd; omega -- tune
     unfold cost Branch.rent; rw [hg,Nat.cast_add,mul_add, Real.exp_add]
   rw [mul_right_comm (cost r S y) H]; apply le_trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (cost_trim hr ..) hh).trans hx) he) (le_of_eq ?_); rw [ht']; ring
 intro x; refine restore_x S (fun i:I=>(f i).2.2.1) (fun i=>(f i).2.2.2) (fun i=> ⟨(l i).1.cont,(l i).1.sumline⟩) (fun i=>(((f i).2.1).map pen).prod) _ _ ?_ x
 intro y; have hh:=g y; rw [k] at hh; exact hh
end YM.CF.Acorn
