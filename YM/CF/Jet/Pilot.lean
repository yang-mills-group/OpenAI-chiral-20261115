import YM.CF.Jet.Leg
import YM.CF.Broc.Wage
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {m B b:Side}{j l n y k:ℕ}{e p d a w:ℝ}
section
variable {Y D T G: Type}[Fintype Y][DecidableEq Y][TopologicalSpace D]{Q:Draw D}{M:Light Y D G}
lemma screen_sum (s:Finset T)(f:T→ D→ℂ)(h:∀ i∈s,Screen M Q n (f i) a w): Screen M Q n (fun x=>∑ i∈s,f i x) a (s.card*w):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty,card_empty,Nat.cast_zero,zero_mul]; refine ⟨fun _ _=>0,fun _=>0,fun R=>⟨Peak.emptyB,?_⟩,fun i=>by simp [hitE],by simp⟩; intro E _ _ _ V g p t u hx; exact allows_const _ (norm_zero.le)
 | @insert i s hi ih=>
   simp only [sum_insert hi,card_insert_of_notMem hi,Nat.cast_add_one,add_mul,one_mul]; rw [add_comm (_*w)]; exact (h _ (by simp)).plus (ih (fun i g=>h _ (by simp [g])))
end
lemma rate_cap (S:Seal (Site (Domain m B))) : (complexA m B S).card≤ S.card:=by
 let W:= complexA m B S; rw [← Finset.card_image_of_injective (f:=address m B) W ((scaleR m B).embed_injective)] -- tune
 exact card_le_card fun i h=>by obtain ⟨j,k,rfl⟩:=mem_image.mp h; exact (mem_filter.mp k).2 (raddr ..)
lemma spritz(n':ℕ)(K:ℝ)(hK:1≤K)(H:CoinG j l k n d a w)(G:Guide b e p d)(h:0<a)(hw:0<w):∃ C:ℝ,0≤C∧∀ m N:Side,∀ T:Bars m b N,k≤N.val→∀ M:Male, Screen (foamK N e p) (Tu N e p n' K) n' (fun x=>tread m b j l n M N T x.val.1 x.val.2.1 x.val.2.2) (rateK a b/2) C:=by
 obtain ⟨V,t,hV⟩:=agree_test n' K hK b; obtain ⟨D,hD,P⟩:=spin_l H h hw G n' K hK
 obtain ⟨Y,hY,Q⟩:= stash V t n' (ratePos _ h b)
 refine ⟨Y*(n*D+n*D),by positivity,fun m N T k' M=>?_⟩; unfold Bars at T; subst N
 let F:= forestB m b e p; let A:=ranK m b e p; have hC (s:Bool): Screen F.botL (AuX m b e p n' K) n' (fun i=>antler j l n M m b (stampA i) (tided s i) (brim i)) (rateK a b) (n*D):=by
   have he:=screen_sum (range n) (fun i (x:backS m b e p)=> facePay j l n M m b (stampA x) (solesK s x) (tided s x) (stick 1) i) (fun i hi=> P m k' M i (mem_range.mp hi) s); rw [card_range] at he; exact he
 letI : LocallyCompactSpace ↑(BinK (CSide m b) e p):=local_cpn ..
 let Q' := fun x:backS m b e p=> hero j l n M m b (stampA x) (tided false x) (tided true x) (brim x)
 have ht' : Screen F.botL (AuX m b e p n' K) n' Q' (rateK a b) (n*D+n*D):=by unfold Q' hero; simp_rw [sub_eq_add_neg]; exact (hC false).plus (hC true).minus
 have hv:= screen_mean F (hV m e p) ht' rate_cap (fun T x=>cover_s m b T x) (fun T x y h=> overB m b x y h) (fun T x=>⟨fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩) hY (fun T v p=> Q v p _ _ (rate_cap T))
 convert hv using 1; funext x; let K:=lick j l n M m b x.val.1 x.val.2.1 x.val.2.2
 have hy(y): cream A Q' (x,y)=fall (A x) y • K:=by
   by_cases u:fall (A x) y≠0; swap; rw [not_not] at u; unfold cream; change fall (A x) y • _=fall (A x) y • _; rw [u,zero_smul,zero_smul]
   let f: Sam A:= ⟨(x,y),u⟩
   have he' : Q' f= K :=(priceHero H G k' x.property.1 x.property.2.1 x.property.2.2 (sealS m b (f:backS m b _ _)) M).symm
   exact congrArg (fun v:ℂ=>fall (A x) y • v) ((sampler_p (A:=A) Q' (x,y) u).trans he')
 change K=means A Q' x; unfold means; simp_rw [hy]; rw [integral_smul_const,sails_all,one_smul]
lemma ryth(n:ℕ)(K:ℝ)(B:Side)(h:1≤K):∃ C:ℝ,0≤C∧∀ (m:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](S:Set E),IsOpen S→∀ (p:E→ Skin m B),(∀ x∈S,TransK n p x K)→ FireK S (rock m B ∘ p) C n:=by
  obtain ⟨C,V,H⟩:= zap (X:=Unit) Finset.univ (by simp) n B h
  refine ⟨C,V,fun m E _ _ _ S u p l=> ?_⟩
  have hx (x:E)(g:x∈S)(a:Index m)(i:Cue m): CashCold (fun t=>(rock m B (p t)).run a i) x n C:=by
    apply H E S u m p (fun t (u:Unit)=>slot m i) (fun _=>i) (fun x hx=> ⟨l x hx,fun k=>allows_const _ ((vote_unit _).trans_le h),fun _ _ j=>allows_const _ ((vote_unit _).trans_le h)⟩) 0 (fun _=>∅) a x g
  exact ⟨u,V,fun x h i t=> (hx x h i t).1,fun x h i t=> (hx x h i t).2⟩
def partQ (m B:Side)(e p:ℝ)(n:ℕ)(K:ℝ): Draw (Brace.Chord m B e p):=⟨fun E _ _ _ V f=>∀ x∈V,TransK n (fun i=>(f i).val.1) x K ∧ seek (fun i=>(f i).val.2) n x K ⟩
def partRose (m B:Side)(e p:ℝ)(n:ℕ)(K:ℝ): Draw (fete m B e p):=⟨fun E _ _ _ V f=>∀ x∈V, TransK n (fun i=>(f i).val.1.val.1) x K ∧ seek (fun i=>(f i).val.1.val.2) n x K ∧ ToR n (fun i=>(f i).val.2) x K⟩
lemma cores (B:Side)(K:ℝ)(n:ℕ)(h:1≤K):∃ C:ℝ,0≤C∧∀ (m:Side)(e p:ℝ), Inspired (partQ m B e p n K) (rose m B e p) (partRose m B e p n K) C n:=by
 obtain ⟨C,c,H⟩:=ryth n K B h; refine ⟨C,c,fun m e p=>⟨c,fun E _ _ _ S u q r=> H m E S u (fun i=>(q i).val.1) (fun x hx=> (r x hx).1),?_⟩⟩
 intro E _ _ _ V W v u w f g F t s x hx
 refine ⟨fun i=> ((g x (v hx)).1 i).germ ?_,fun i=> ((g x (v hx)).2 i).germ ?_, fun i=>(allows_const _ ((vote_unit (t i)).trans_le h)).germ ?_⟩
 · filter_upwards [w.mem_nhds hx] with i' g'; exact (congrArg (fun x=> SU.fund (x.1.val.1 i)) (s i' g')).symm
 · filter_upwards [w.mem_nhds hx] with i' g'; exact (congrArg (fun x=> hook x.1.val.2 i) (s i' g')).symm
 filter_upwards [w.mem_nhds hx] with i' g'; exact (congrArg (fun x=>(x.2 i).val) (s i' g')).symm
end YM.CF.Jet
