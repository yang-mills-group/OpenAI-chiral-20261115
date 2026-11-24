import YM.SU5.Relativistic.Caval
import YM.SU5.Relativistic.Thunder
/-! # aperture of single probes: NOT using connectivity links borrowed from between the regions. Budget. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV.Chateau
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Crest.Sleet.Sorcerer Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable (K:Calibration)(v:Cover)(A d:ℕ)(c:Fin 3)
def topOut (o:Cover)(F:Waxy): Finset Cover:= plusHalf.biUnion fun a=> (TwistT A).biUnion (fun j=> (F a j).support.image (fun t=>o+Crest.Sleet.tack t j))
lemma glean (o u:Cover)(F:Waxy): InTest K false (viabox (topOut A o F) u) true (glebe K u o F A c):=by
 refine bind_T K (F:=august K u o F A c) (fun l=>?_); unfold august; refine InTest.sum _ _ (fun i e=> InTest.sum _ _ (fun j w=> InTest.sum _ _ (fun q p=>.smul _ ?_)))
 have hp:o+Crest.Sleet.tack q j∈ topOut A o F:= mem_biUnion.mpr ⟨i,e, mem_biUnion.mpr ⟨j,w,mem_image_of_mem _ p⟩⟩
 exact ray_test K _ u _ (fun a q=>mem_biUnion.mpr ⟨_,hp,q⟩) (via_ok _ _ _ hp) c i e l
-- single mount. TA for pricing only. May require orientation for each coherent chart later.
def Seat5(A:ℕ):Cover:= (4*(A:ℤ)) • step TA
local notation "X"=> Seat5 A
def hallW:Finset Cover:=(Lattice.box (2*A)).image (fun z:Cover=>nodeC X+z)
lemma bellH (i:Cover): i∈ hallW A ↔ ∀ j:Axis,nodeC X j- 2*(A:ℤ) ≤ i j ∧ i j ≤ nodeC X j+2*A:=by
 constructor
 · intro v; obtain ⟨z,u,rfl⟩:=mem_image.mp v; obtain ⟨x,h⟩:=box_test.mp u; intro j; specialize x j; specialize h j; change _≤ _+ z j ∧ nodeC X j+z j ≤ _; omega
 intro h; apply mem_image.mpr; refine ⟨i-nodeC X,box_test.mpr ⟨fun j=> ?_,fun j=>?_⟩, by abel⟩
 · specialize h j; simp; omega
 specialize h j; change i j-nodeC X j≤_; omega
local notation "Z"=> Lilt v d A
def wreath := nodeC (X - v)
local notation "O"=> wreath v A
def snowF:=insert O (viabox (topOut A X Z) O)
local notation "F"=> snowF v A d
def latticeFieldEstimates:= glebe K O X Z A c
def auger(A:ℕ)(c:Fin 3):= gyre K (Seat5 A) c
lemma latticeFieldEstimates_N:Neutral K (latticeFieldEstimates K v A d c):=glebe_N K O X Z A c -- tune arguments iri.
lemma latticeFieldEstimates_T: InTest K false F true (latticeFieldEstimates K v A d c):= (glean K A c X O Z).mono (Finset.subset_insert ..)
lemma horns (p:v∈ Lattice.box A) : O∈ hallW A:=by
 apply (bellH A O).mpr; intro j; obtain ⟨x,t⟩:=box_test.mp p; specialize x j; specialize t j; unfold wreath; simp [nodeC]; omega
private abbrev B₀:=district (TwistT A) X Z
private def Soil :Finset Cover:= insert X (B₀ v A d)
lemma town (x:Cover)(p:x∈B₀ v A d)(j:Axis): nodeC X j-2*(A:ℤ) ≤ nodeC x j ∧ nodeC x j ≤ nodeC X j+2*A :=by
 obtain ⟨i,_,u⟩:=mem_biUnion.mp p; obtain ⟨a,e,s⟩:=mem_biUnion.mp u; obtain ⟨y,h,rfl⟩:= mem_image.mp s; obtain ⟨q,g⟩:=box_test.mp (casing _ _ _ h); specialize q j; specialize g j; unfold nodeC; -- simp t auto
 simp; omega
private lemma village (p:v∈ box A): viabox (B₀ v A d) O⊆ hallW A:=by
 have hp:= (bellH A _).mp (horns v A p); intro i u; exact (bellH A _).mpr (fun j=> via_lim _ _ _ _ _ (hp j).1 (hp j).2 (fun z t=> town v A d _ t j) _ u)
lemma latticeFieldEstimates_S (p:v∈ box A): F ⊆ hallW A:=by
 intro i g; rcases mem_insert.mp g with g|g; exact g.symm ▸ horns v A p
 obtain ⟨x,h,u⟩:=mem_biUnion.mp g; obtain ⟨i',-,r⟩:=mem_biUnion.mp h; exact village v A d p (mem_biUnion.mpr ⟨_,mem_biUnion.mpr ⟨_,mem_univ i',r⟩,u⟩)
lemma bow (x:Cover)(p:x∈ F)(j:Axis):nodeC X j- 2*v j-2*d ≤ x j ∧ x j ≤ nodeC X j- 2*v j+2*d:=by
 have he: O j=nodeC X j-2*v j:=by simp [wreath,nodeC]; ring
 rcases mem_insert.mp p with p|p; subst x; rw [he]; omega
 apply via_lim _ _ _ _ _ (by rw [he]; omega) (by rw [he]; omega) _ _ p; intro z H; obtain ⟨i,h,q⟩:=mem_biUnion.mp H; obtain ⟨y,t,hQ⟩:=mem_biUnion.mp q; obtain ⟨w,q',rfl⟩:= mem_image.mp hQ; obtain ⟨r,g⟩:=box_test.mp (garnishing v d A h q'); specialize r j; specialize g j; simp only [Pi.add_apply] at g r; simp [nodeC]; omega
local notation "D"=> {nodeC X}
lemma inset (k:ℕ)(h:∀ i:Axis,k+d ≤ (v i).natAbs):∀ j, (∀ x∈F, x j+ 2*k ≤ nodeC X j) ∨ (∀ x∈F,nodeC X j+2*k ≤ x j):=by
 intro i; specialize h i; by_cases q:v i ≤ 0
 · right; intro x t; have he:= (bow v A d x t i).1; omega
 left; intro x t; have he:= (bow v A d x t i).2; omega
lemma arenaSep (k:ℕ)(h:∀ i:Axis,zig K k+d ≤ (v i).natAbs): ∀ j:Axis,∃ y:ℤ, Till K k j y D F ∨ Till K k j y F D :=by
 intro j; let t:=nodeC X j
 rcases inset v A d _ h j with u|u
 · obtain ⟨y,p⟩:=zig_here (K:=K) F D k j (t-zig K k) (fun x v=> by have hp:=u x v; unfold t; omega) (fun x v=>by rw [mem_singleton.mp v]; omega); exact ⟨y,Or.inr p⟩
 obtain ⟨y,p⟩:=zig_here (K:=K) D F k j t (fun x v=> by rw [mem_singleton.mp v]) (fun x v=>by have ht:=u x v; unfold t; omega); exact ⟨y,Or.inl p⟩
-- town ledger and packing
lemma bill_A (u:K.ℓ≤A): Tower.SlabMark.Between K TA 0 (ruler K.B* (heightB A)) (hallW A):=by
 intro i p; obtain ⟨p,q⟩:= (bellH A i).mp p TA; rw [show nodeC X TA=8*(A:ℤ)+1 from (by simp only [Seat5,nodeC,Pi.smul_apply]; simp; ring)] at p q -- tune
 unfold heightB; push_cast; have ht:= (mul_le_mul_of_nonneg_right (ruler_gene K.B) (show 0 ≤ (12:ℤ)*((A:ℤ)+1) by positivity)); omega
lemma tall :∃ i:Cover, Transom TA (hallW A) i (4*A):=by
 refine ⟨fun i=> nodeC X i-2*A,fun i _ x v=>?_⟩; have h:=(bellH A x).mp v i; dsimp only; omega -- tune
abbrev Tag (m:Side):Cliplet (K.c m) 1:=AWork K Z (fun _=> X) c A O m (hallW A)
abbrev Banner := billboard K Z (fun _:Fin 1=> X) c A O
local notation "t⊹"=> Tag K v A d c
lemma frameB (m:Side): (t⊹ m).frame=Banner K v A d c m:=rfl
lemma TagMap: Banner K v A d c=1+ auger K A c * latticeFieldEstimates K v A d c:=by unfold Banner billboard auger latticeFieldEstimates; simp [prompter] -- tune
lemma TagCost (p:v∈ box A) : InTest K false (hallW A) false (Banner K v A d c):=by rw [TagMap]; exact InTest.one.add (((gyre_T ..).mono (Finset.singleton_subset_iff.mpr ((bellH A _).mpr (fun j=>by omega)))).mul ((latticeFieldEstimates_T K v A d c).mono (latticeFieldEstimates_S v A d p))) -- arguments _ not infer
private lemma rose (s:ℕ)(p:s≤ 2*A)(m:Side) : Lattice.halo s (t⊹ m).s ⊆ (t⊹ m).broad:=by
 let n:=More (K.c m)
 intro i h; obtain ⟨j,y,h⟩:= halo_spec.mp h; obtain ⟨u,e,rfl⟩:=mem_image.mp y
 let a:= nodeC X; let b:=wrap n a; let z:= lift (i-b); have ht:z∈ Lattice.box (2*A):=by
    have hz(l:Axis):(z l).natAbs ≤ 2*A:= (component_le (i-b) l).trans ((show pdist (i-b) ≤ s from (separation_comm _ _).trans_le h).trans p)
    exact box_test.mpr ⟨fun i=>by have ht:=hz i; omega,fun i=>by have ht:= hz i; omega⟩
 change i ∈ Finset.image (wrap n) (hallW A); apply mem_image.mpr; refine ⟨a+z, mem_image_of_mem _ ht,?_⟩; rw [map_add,show wrap n z=i-b from wrap_lift _]; unfold b; abel
-- Mint input at currency. Forge for entire plate by lacing. external Halo unrestricted.
private lemma march_u {n:Side}{u x:Cover}(h:Lifted.nodeC x∈hallW A)(t:u∈hallW A)(q:∀ i∈ hallW A,∀ j∈ hallW A,lift (wrap n i-wrap n j)=i-j) : march (wrap n u) (wrap n (nodeC x)) 1=TrackV u x:=by
 unfold march; rw [q (nodeC x) h u t]; simp only [route,TrackV,axisRoute,Pi.sub_apply,Pi.zero_apply,sub_zero]
private lemma rightful_less (g f:ℝ)(l:g≤f){n:Side}{V:Pane n}(C T:Finset (Seat n))(h:C⊆ T) (p:Rightful T V 1 g): Rightful C V 1 f:=by apply (riotPort ..).2; intro j t; exact ((riotPort ..).1 p j (mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp t).2.1,h (mem_filter.mp t).2.2⟩)).trans l
lemma signway {κ R R' γ γ':ℝ}{s l:ℕ}{V:ℝ}(b:v∈ box A)(e:chipPay (damper d) v≠0)
    (p:s+l+1 ≤ 2*A)(x:0<γ)(w:0<γ')(h:0≤V)(c':R'+V ≤ R)(u:∀ n:Side,∀ j:SU.Slot, ‖strum n X A Z j‖ ≤ R')
    (j:ℕ)(g:∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male), N≤ M.val.val→∀ n: Side,∀ j':SU.Slot, ‖acts (spar j M (1:Pane n)) (strum n X A Z j')- strum n X A Z j'‖≤V) (r m₀:ℕ):
    ∃ τ₀> (0:ℝ),∃ T:ℕ, m₀+r≤ T ∧ ∃ N:ℕ,∀ m:Side,N≤ (K.c m).val→∀ (M:Jill.Male),N≤M.val.val→IsStarProjection (spar j M (1:Pane (K.c m)))→∀ τ:ℝ,0≤τ→τ≤τ₀→∀ c:Fin 3,Column j M s l r T γ γ' τ (3*V) R (Tag K v A d c m):=by
 let L:= hallW A; obtain ⟨a,hu⟩:= disperse L; obtain ⟨Q,z⟩:= disperse_wrap (Soil v A d); obtain ⟨Y,hY⟩:= long_cost L O; let f:=Y+r; let T:= max (m₀+r) (f+1); let g₀:= min γ γ'
 obtain ⟨τ,t,hτ⟩:=stampG_price f g₀ (lt_min x w); obtain ⟨N,w'⟩:=g.exists; refine ⟨τ,t,T,le_max_left .., a+Q+N+2*(f+1)+1,fun m hm M hv u' x p' e0 c=>?_⟩
 let n:= K.c m; have ht: 2*(f+1)< (More n).val:= by change _ < (K.c m).val*2; omega -- tune
 have he (i: Cover) (u:i∈B₀ v A d): Lifted.nodeC i∈ L:= (bellH A _).mpr (town v A d i u); let W:=Tag K v A d c m; let y:= wrap (More n) O; have hy:O∈L:=horns v A b
 have ha:X∈ Soil v A d∧ Lifted.nodeC X∈L:= ⟨mem_insert_self ..,(bellH A _).mpr (fun i=>by omega)⟩
 apply warrant K Z (fun _=>X) c A O m (Soil v A d) L (z _ (by omega)) (TwistT A) _ (fun i=>ha) (fun i z u=>⟨Finset.mem_insert_of_mem u,he z u,march_u A (he z u) hy (fun i p j q=> hu i p j q _ ?_)⟩) (fun _=>village v A d b) l (A+1) (fun i=>?_ ) R' V R h c' (drink v V e (by omega)) j M u' (fun i u₁=> u n u₁) (fun _ t=> w' _ (by omega) n _) s r T γ γ' x (Function.injective_of_subsingleton _) _ (rose K v A d c (s+l+1) p m) -- tune dot
 all_goals try first
 | exact p
 | (change a≤(K.c m).val*2; omega)
 | (refine ⟨fun _=>0,rfl,?_⟩; intro i; simp only [smul_zero]; rw [show Crest.Sleet.tack (0:WalkA) 0=0 by funext i; induction i using Fin.lastCases <;> simp only [Crest.Sleet.tack, Fin.lastCases_last,Fin.lastCases_castSucc] <;> rfl,add_zero])
 | (intro i _ j e; ext y; rw [Finsupp.zero_apply,← Finsupp.notMem_support_iff]; intro h; apply e; obtain ⟨p,q⟩:=box_test.mp (casing v d A h); specialize p TA; specialize q TA; rw [tack_right] at p q; exact mem_Icc.mpr ⟨p,q⟩)
 | (intro i t j u g; obtain ⟨x,_,rfl⟩:= mem_image.mp t; obtain ⟨y,_,rfl⟩:=mem_image.mp u; exact (g rfl).elim)
 intro U hu; have hx: hot W r ⊆ BlockP f y:=by
    intro x h; obtain ⟨u,m,l⟩:= halo_spec.mp h; obtain ⟨z,t,rfl⟩:= mem_image.mp m; exact blocks_test.mpr ((separation_triangle y (wrap (More n) z) x).trans (Nat.add_le_add (hY _ z t) l))
 have ht:=hτ x p' e0 ht (le_max_right (m₀+r) _) _ _ (hu.mono_left (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem _ hy))))
 exact ⟨rightful_less _ _ (min_le_left ..) _ _ ((halo_subset r W.broad).trans hx) ht,rightful_less _ _ (min_le_right ..) _ _ hx ht⟩
end YM.CF.Pannier.Chancel.ScreeV.Chateau
#print axioms YM.CF.Pannier.Chancel.ScreeV.Chateau.signway
