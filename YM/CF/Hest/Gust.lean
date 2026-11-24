import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable {G:Ratio (CSide m B) (CSide X B)}
lemma scull {G:Ratio N P}{C:Seal (Site (More P))→Toll (Iota G)}(p:Ledger d C A)(g:∀ S i j,0≤C S i j): Ledger d (fun S i j=> C S (patchQ G i) (patchQ G j)) A:=by
 let H:=patchQ G; let D:= fun S i j=>C S (H i) (H j)
 have hv(f: Iota G→ℝ)(p:∀ i,0 ≤ f i):∑ i,f (H i)≤ ∑ i,f i:=by
    have hh: ∑ i∈univ.image H,f i=∑ i,f (H i):= by rw [sum_image H.injective.injOn]
    rw [← hh]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _=> p _
 exact ⟨p.posP,fun i=> (hv (saleM d C (H i)) fun j=> sale_nn g d ..).trans (p.rows _),fun i=>(hv (fun j=> saleM d C j (H i)) fun j=> sale_nn g d ..).trans (p.cols _)⟩
section
variable{D:NoteS G e}
lemma boundP(h:Odd G.count.val)(p:Bisca G e false false d u D): Bisca G e false false d (population*u) (ced G e Bool.xor (glade G D) false):=by
 let L:= glade G D; apply serene_p G h e L Bool.xor _ false; intro i; cases i; exact p; have he:= Bisca.sm (-1) (Bisca.flips p); simp only [norm_neg,norm_one,one_mul, neg_one_smul] at he; exact he
lemma popeP (p:e≤ d)(g:0< e)(x: Rent0 G e): ball (poseT G g p x).val d ⊆ cro G d:=by
 have he:=g.trans_le p; rintro ⟨u,v⟩ h; let W:= x.val; have hx: x.val∈Rent0 G e:=x.property; have h':max ‖u-unionP W‖ ‖v-profile W.1‖<d:= mem_ball_iff_norm.mp h; exact ⟨⟨W,ampleB hx p,(max_lt_iff.mp h').1⟩,W.1,(JointB.fg x.property).shrink p, (max_lt_iff.mp h').2⟩ -- tune
lemma ep (n:ℕ)(p:0≤C)(hd:0 < d):∃ c:ℝ,1 ≤ c ∧∀ {m X B:Side}(G:Ratio (CSide m B) (CSide X B)),Odd G.count.val →∀ e:ℝ,∀ a:ℝ,∀ f: NoteS G d, Bisca G d false false a u f →∀ v:0<e,∀ l:e ≤ d,∃ W:mSeal X B→ Toll (Single (CSide m B)), Ledger a W (c*u) ∧∀ S, Filer G S (W S) C n (fun x=> summit (patchQ G) (f S (poseT G v l x))):=by
 obtain ⟨A,h,H⟩:= profile_X n C p
 let T:= (1+2^n/d)^n; let L:= max 1 (composeCost n T A); have hp:1≤L:=le_max_left ..; have hP:0≤ L:=zero_le_one.trans hp
 refine ⟨L,hp,fun {m X B} G hg e a f ho v ℓ=>?_⟩; obtain ⟨C',Y,F⟩:= ho; let p:= poseT G v ℓ
 let W(S:Seal (Site (More (CSide X B))))(i j:Iota G):= L*C' S i j; have he S i j:0≤ W S i j:=mul_nonneg hP ((Y S).nonn i j)
 let K:=patchQ G; have hv(i:Single (CSide m B)): (tempo G d).home (K i)= (ratio G).embed (place_x i):= trK G i hg
 refine ⟨fun S i j=> W S (K i) (K j), scull (F.funds hP) he,fun S=>?_⟩
 have ht x y (h:(dressL G e).rel S x y) i j:F=F ∧ f S (p x) i j=f S (p y) i j:=by
    let A:=(Y S).expo i j; have hx:= A.variation (p x) (p y); rw [show (hall G d).eval _ _ _=0 from porch G v ℓ S x y h,mul_zero] at hx; exact ⟨rfl,sub_eq_zero.mp (norm_le_zero_iff.mp hx)⟩
 refine ⟨fun g x=>?_,fun x y h=>?_,continuous_matrix (fun i j=>((Y S).expo (K i) (K j)).connected.comp (pier_c ..)),fun i j=>he _ _ _,fun i j=>?_,fun i j a=>?_,fun i j x=>?_⟩
 · rw [prance, show f _ ((hall G d).drive _ _)=_ from (Y S).frame.frame g _]; exact summit_l G d ..
 · ext i j; exact (ht x y h (K i) (K j)).2
 · intro E _ _ _ V g d' t x z; let X(x):=(p (d' x)).val; have ht:Set.MapsTo X Set.univ (cro G d):=fun x _=>(p (d' x)).property
   let C₀ (x):=f S x (K i) (K j); let c:=C' S (K i) (K j); have hu:=t x z; have h':Allows n X x A:= ((H _ x hu.1).pair (H _ x hu.2)).pair (H _ x hu.1)
   let p':= (Y S).expo (K i) (K j); have hp: Allows n (equalizer C₀ ∘ X) x (composeCost n (c*T) A):=(allows_looks ((Y S).fuel _ _) p'.connected (popeP ℓ v (d' x)) hd _ p'.bounded).comp (f:=X) h'
   apply (hp.mono ?_).germ (Eventually.of_forall fun i=> dif_pos (p (d' i)).property)
   · rw [show composeCost n (c*T) A=composeCost n T A*c by unfold composeCost; ring]; exact mul_le_mul_of_nonneg_right (le_max_right ..) p'.positive
 · obtain ⟨g,z,y⟩:= ((Y S).expo (K i) (K j)).triggered (right_ne_zero_of_mul a); change (tempo G d).home (K i)∈ S at z; change (tempo G d).home (K j)∈S at y; rw [hv] at y z; exact ⟨g,mem_filter.mpr ⟨mem_univ _,z⟩,mem_filter.mpr ⟨mem_univ _,y⟩⟩
 exact (((Y S).expo (K i) (K j)).bounded (p x)).trans (le_mul_of_one_le_left ((Y S).nonn _ _) hp)
end
end YM.CF.Hest
