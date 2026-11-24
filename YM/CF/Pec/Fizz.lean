import YM.CF.Laic.Hope
import YM.Push.STRESS_FLUX.Color
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n: Side}{a b:ℝ}
abbrev Orig(n:Side):=Site (More n)
abbrev Post(n:Side):= Bkg (More n)
abbrev Ok(n:Side):=PrizeX n
abbrev Dues(n:Side):= Ok n→ Ok n→ℂ
abbrev Pride(n:Side):= Site n→ Dues n
def tag (x:Orig n)(K:Dues n)(U: Post n):ℂ:= ∑ i,∑ j, inner ℝ (silt x i U) (silt x j U) • K i j
abbrev cents(x:Orig n)(T:Dues n)(a:ℝ):ℝ :=∑ i,∑ j,nick a (contour x i j)*‖T i j‖
def mom(K:Dues n)(a b:PlaqAxes):ℂ:=∑ i:Orig n,∑ j:Orig n,K (Sum.inl (i,a)) (Sum.inl (j,b))
def merit(W:Pride n):Prop:=∀ x p q,mom (W x) p q=0
def zinger(W:Pride n)(U:Post n):ℂ:= ∑ i,tag (node i) (W i) U
lemma tag_g (U:Post n)(W:Dues n)(p: Orig n→E)(x:Orig n) : tag x W (gauge p U)= tag x W U:=by unfold tag; simp_rw [silt_g, StressFlux.inner_adjoint]
lemma Czero (x:Orig n)(K:Dues n):0≤ cents x K a:= Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=>mul_nonneg (nick_pos _ (ct_pos ..)|>.le) (norm_nonneg _)
lemma summer(q:Dues n)(x:Orig n)(p k:PlaqAxes) (h:0≤a): ‖mom q p k‖≤ cents x q a:=by
 let F(i j:Ok n):=nick a (contour x i j)*‖q i j‖; have hf (i j):0≤ F i j:=mul_nonneg (nick_pos _ (ct_pos ..)|>.le) (norm_nonneg _); let Z(p:PlaqAxes)(x:Orig n):Ok n:=Sum.inl (x,p)
 have hs(f:Ok n→ℝ)(p:PlaqAxes)(h:∀ i,0≤ f i):∑ i:Orig n,f (Z p i)≤∑ i,f i:=by
    have hi:(univ.image (Z p)).card=Fintype.card (Orig n):=by rw [card_image_of_injective _ (by intro q v ht; exact Prod.mk.inj (Sum.inl.inj ht)|>.1), card_univ]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image (Z p))) (fun i _ _=> h i)); rw [sum_image]; intro i _ j _ ht; exact (Prod.mk.inj (Sum.inl.inj ht)).1
 refine le_trans (norm_sum_le ..) (le_trans (sum_le_sum (g:=fun i=>∑ j,F (Z p i) j) fun i _=> ?_) ?_); · apply le_trans (norm_sum_le ..); apply le_trans _ (hs _ k (hf (Z p i))); exact Finset.sum_le_sum fun j _=> le_mul_of_one_le_left (norm_nonneg _) (nick_cheap (ct_pos ..) h)
 exact hs _ p (fun i=> sum_nonneg fun j _=>hf i j)
lemma fine_g(W:Pride n)(U:Post n)(p:Orig n→E):zinger W (gauge p U)=zinger W U:=by unfold zinger; simp_rw [tag_g]
def pays(s:Signed): ℂ→L[ℝ]ℂ:= if detX s then Complex.conjCLE.toContinuousLinearMap else ContinuousLinearMap.id ℝ ℂ
lemma complX (s:Signed)(x:ℂ): pays s x=cSignX (detX s) x:=by cases h:detX s<;>simp [h,pays,cSignX]
lemma pays_t(s t:Signed)(x:ℂ):pays s (pays t x)=pays (s*t) x:= by simp only [complX,sign_seq,det_p]
def lexn (f:Post n→ℂ)(x:Post n):ℂ:= (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, pays s (f (Yg (incX s) x)) -- inverse? pays order comm det+transpose valued. projection
abbrev pigment(W:Pride n)(x:Post n):ℂ:=lexn (zinger W) x
lemma prog(f:Post n→ℂ)(U:Post n)(p:Signed):lexn f (Yg (incX p) U)= pays p (lexn f U):=by
 unfold lexn; rw [map_smul,map_sum]; congr 1; conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft p)] 
 apply sum_congr rfl; intro s _; rw [←kor,wink]; change pays s _= pays p (pays (p*s) _); simp only [complX,sign_seq,det_p]; cases h:detX p<;> cases v:detX s<;> simp
lemma pinG(W:Pride n)(U:Post n)(g: Orig n→E): pigment W (gauge g U)=pigment W U:=by unfold pigment lexn; simp_rw [van,fine_g]
def feedback (t:Site n):Equiv.Perm (Ok n):= pinP (2 • Lattice.lift t)
lemma hose(x:Cover): @feedback n (wrap n x) = pinP (2 • x):=by
 have ht:wrap (More n) (2 • Lattice.lift (wrap n x))= wrap _ (2 • x):=by rw [←show ∀ z:Cover,(assembly n).embed (wrap n z)= wrap _ (2 • z) from fun z=>Ratio.embed_wrap ..,← show ∀ z:Cover,(assembly n).embed (wrap n z)= wrap _ (2 • z) from fun z=>Ratio.embed_wrap ..,wrap_lift]
 unfold feedback pinP; rw [ht]
lemma mint(x y:Site n)(b:Ok n): feedback x (feedback y b)=feedback (y+x) b:=by cases b with
 | inr i=>rfl
 | inl i=> rw [← wrap_lift x,← wrap_lift y,hose,hose, ←map_add,hose]; obtain ⟨j,k⟩:=i; simp [pinP,add_assoc, smul_add] -- tune
lemma virtue(x:Site n)(t:Cover): node (x+wrap _ t)= node x+wrap _ (2 • t):=rolls t (x,0)

def WordK(T:Pride n):Prop:=∀ i t a b,T (i+t) (feedback t a) (feedback t b)=T i a b
lemma wageJ {W:Pride n}(p:WordK W)(t: Cover) (U:Post n):zinger W (Yg (lagX t) U)=zinger W U:=by
 unfold zinger; conv_rhs => rw [←Equiv.sum_comp (Equiv.addRight (wrap n t))]
 refine sum_congr rfl fun i _=> ?_; let X:=node i; let V(j):= silt X j (Yg (lagX t) U)
 let A:=wrap n t; have hx(v: Ok n): V v=silt (node (i+A)) (feedback A v) U:=by
   unfold V silt A X; rw [Ylag,y_up,virtue,hose,pin_v]
 unfold tag; conv_rhs => rw [← Equiv.sum_comp (feedback A)]
 refine sum_congr rfl fun v _=> ?_; conv_rhs=> rw [←Equiv.sum_comp (feedback A)]
 refine sum_congr rfl fun j _=>?_ ; change inner ℝ (V v) (V j) • _= inner ℝ _ _ • W (i+A) _ _; rw [p,hx,hx]; rfl
lemma tolls {W:Pride n}(p:WordK W)(t:Cover)(U:Post n):pigment W (Yg (lagX t) U)=pigment W U:=by unfold pigment lexn; apply congrArg ((Fintype.card Signed:ℝ)⁻¹ • ·); apply sum_congr rfl; intro i _; rw [←kor, show joinX (lagX t) (incX i)=joinX (incX i) (lagX (i⁻¹.act t)) from by simp [joinX,lagX,incX],kor, wageJ p]
end YM.CF.Pec
