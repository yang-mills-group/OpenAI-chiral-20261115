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
variable{G:Ratio (CSide m B) (CSide X B)}
structure Filer (G:Ratio (CSide m B) (CSide X B))(S:mSeal X B)(K:Toll (Single (CSide m B)))(s:ℝ)(k:ℕ)(F:Rent0 G e→ Op (Single (CSide m B))):Prop where
 gauge(g:Site (More (CSide X B))→E)(x:Rent0 G e):F ((dressL G e).dress g x)=ActZ (scaleG G g) (F x)
 reads(x y:Rent0 G e): (dressL G e).rel S x y→ F x=F y
 cont :Continuous F
 pos(i j):0≤ K i j
 folk(i j): OrderD (LineE k G s e) k (fun x=> F x i j) (K i j)
 root(i j): K i j≠0 → Grove (terr _) S ∧ place_x i∈ cloudG G S∧ place_x j∈ cloudG G S
 gate(i j x):‖F x i j‖≤ K i j
abbrev Haze (m X B:Side)(G: Ratio (CSide m B) (CSide X B))(e:ℝ):= mSeal X B→Rent0 G e→ Op (Single (CSide m B))
structure Ind (G:Ratio (CSide m B) (CSide X B))(F:Haze m X B G e)(a b K:ℝ)(n:ℕ)(D:nomA m X B→ Op (Single (CSide m B))): Prop where
 port : ∃ W:mSeal X B→ Toll (Single (CSide m B)), (∀ S,Filer G S (W S) K n (F S)) ∧ Ledger a W b
 meet(x:Rent0 G e):∑ S,F S x=D x.val
 motion(k: Sweep (CSide m B))(S:mSeal X B)(x:Rent0 G e):F (toRoar G k⁻¹ S) (male e G k x)= yank k.charge (castX k) (spinU k.charge k.s) (F S x)
lemma fare_z{X V:Side}{A:Seal (Site (More V))}{x y:Bkg (More V)}(h: Agrees A x y):fare A (profile x) (profile y)=0:=by
 unfold fare; apply sum_eq_zero; intro i hy; rw [show profile x i=profile y i from funext fun z=>by unfold profile; rw [h i (mem_filter.mp hy).2.1 (mem_filter.mp hy).2.2],sub_self,norm_zero]
variable(G)(h:0 < e)(p:e≤d)
def poseT (x:Rent0 G e):↑(cro G d):= ⟨(unionP x.val,profile x.val.1),ambient _ _ h p x.property,by refine ⟨x.val.1,x.property.fg.shrink p,?_⟩; simpa using h.trans_le p⟩
lemma surf (k:Sweep (CSide m B))(x: Rent0 G e): poseT G h p (male e G k x)=toWish G d k (poseT G h p x):=Subtype.ext ((wish_g G d k (poseT G h p x) x.val x.val.1 rfl).symm)
lemma pier_c : Continuous (poseT G h p):=by
 apply Continuous.subtype_mk; have hu: Continuous (fun y: Rent0 G e=>profile y.val.1):= profile_c.comp (continuous_fst.comp continuous_subtype_val); exact (hu.prodMk (profile_c.comp (continuous_snd.comp continuous_subtype_val))).prodMk hu
lemma prance(g:Site (More (CSide X B))→ E)(x:Rent0 G e): poseT G h p ((dressL G e).dress g x) = (hall G d).drive g (poseT G h p x):=Subtype.ext (Prod.ext (jig G g _) (profile_g ..)) -- tune names
lemma polar_p (x:Rent0 G e): chillF G d (poseT G h p x)=poseT G h p x:=Subtype.ext (Prod.ext (revI ..) (ice_pr ..))
lemma porch (S:mSeal X B)(x y:Rent0 G e)(k:(dressL G e).rel S x y):(hall G d).eval S (poseT G h p x) (poseT G h p y)=0:=by
 change deal _ S (unionP _) (unionP _) / _ + fare _ _ _ / _=0; unfold deal ; dsimp only [unionP,poseT]; simp only [fare_z (X:=B) k.1, fare_z (X:=B) k.2,add_zero,zero_div] -- tune
end YM.CF.Hest
