/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Fineness.Harmonics
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
/-!
# Determinant traversal through forest frame. Nothing depends on choosing COVARIANT
preferred inside of any block.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Lattice RG Matrix Exterior Precision Tree
open scoped Topology Matrix BigOperators
variable {I J : Type*}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
lemma derives_int (T:Matrix I J ℤ)(p:Surjective (T *ᵥ ·)) : ∃ U:Matrix J I ℤ,T*U=1:=by
 choose f u using p
 let U:Matrix J I ℤ:= Matrix.of fun j i=> f (Pi.single i (1:ℤ)) j
 refine ⟨U,?_⟩; ext i j; change (T*ᵥ f (Pi.single j 1)) i= (1:Matrix I I ℤ) i j; rw [show T*ᵥ f (Pi.single j 1)= Pi.single j 1 from u _,one_apply]; by_cases h:i=j <;> simp_all
lemma layout_units (e:I≃J)(T:Matrix I J ℤ)(p:Surjective (T *ᵥ ·)) : let A:Tab I J:=T.map (Int.castRingHom ℝ); (∃ B:Tab J I, A*B=1) ∧ (A*Aᵀ).det=1:=by
 obtain ⟨U,g⟩:= derives_int T p; intro A; let f:= Int.castRingHom ℝ
 have hx: (T.submatrix id e)*(U.submatrix e id)=1:=by rw [submatrix_mul_equiv,g]; rfl
 refine ⟨⟨U.map f,?_⟩,?_⟩
 · unfold A; rw [show T.map (Int.castRingHom ℝ)=T.map f from rfl,← Matrix.map_mul, g]; exact Matrix.map_one f f.map_zero f.map_one
 let Z:= A.submatrix id e; have he: Z * Zᵀ=A*Aᵀ:=by unfold Z; rw [transpose_submatrix,submatrix_mul_equiv]; rfl
 have hz: Z.det=f (T.submatrix id e).det:= (RingHom.map_det f (T.submatrix id e)).symm -- tune defeq
 rw [← he,det_mul,det_transpose,hz]; rcases Int.isUnit_eq_one_or (Matrix.isUnit_det_of_right_inverse hx) with H|H <;> simp [H] -- tune
section
variable {c g : Side} (r: Ratio c g)
abbrev Shoot (r: Ratio c g) := {x:Site g// Tree.leaf r x}
def turnBond (g:Side) := Equiv.prodCongr (Equiv.refl (Site g)) axisEquiv
variable (T:Forest r)
def internalBond : Shoot r ⊕ T.Free ≃ Body 1 g := by
 let t : Shoot r ≃ (↥T.trunks) := Equiv.ofBijective (fun i:Shoot r=>(⟨SectorNext.Vacuum.FlatTree.sendKey T i,(T.trunk_mem_iff _).mpr ⟨i.val,i.property,rfl⟩⟩:↥T.trunks)) (by
  constructor
  · intro i j t; exact YM.SectorNext.Vacuum.FlatTree.used_inj T (congrArg Subtype.val t)
  rintro ⟨i,V⟩; obtain ⟨x,h,rfl⟩:= (T.trunk_mem_iff _).mp V; exact ⟨⟨x,h⟩,rfl⟩)
 exact ((Equiv.sumCongr t (Equiv.refl _)).trans (Equiv.sumCompl (fun i=> i∈T.trunks))).trans (turnBond g)
-- D leaf. expose coefficients for int conversion
variable (R:Type*) [CommRing R]
def tagsZ : Matrix (Body 1 g) (Shoot r) R:= Matrix.of fun i k => let x:= i.1; let a:=axisEquiv.symm i.2; (if k.val=x+step a then 1 else 0)-(if k.val=x then 1 else 0)
def branchesZ : Matrix (Body 1 g) T.Free R:= Matrix.of fun i k=> if i=(turnBond g) k.val then 1 else 0
open YM.SectorNext.Vacuum.FlatTree (erase trunk_clear climb clear blank leafWard root_clear)
private lemma qualities (x:Shoot r→R)(v:Site g)(i:Axis) : let Q:=fun y:Site g=> if h : leaf r y then x ⟨y,h⟩ else 0; (tagsZ r R *ᵥ x) (v,coord i)=Q (v+step i)-Q v:=by
 intro Q; simp only [tagsZ,mulVec,Matrix.of_apply,dotProduct,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _,Matrix.sub_mul,_root_.sub_mul,ite_mul,one_mul,zero_mul,Finset.sum_sub_distrib]
 have h(y): (∑ k:Shoot r, if k.val=y then x k else 0)=Q y:=by
    unfold Q; split
    next he=>
      let Y: Shoot r:=⟨y,he⟩; simp only [show ∀ k:Shoot r,k.val=y ↔ k=Y from fun k=>(show k.val=Y.val ↔ k=Y from Subtype.ext_iff.symm)]; simp; rfl
    next he=> apply Finset.sum_eq_zero; intro i _; rw [if_neg]; intro h; exact he (h ▸ i.property)
 rw [h,h]
private lemma keeps_z (v : Edge (Site g))(x:T.Free→R) : (branchesZ r T R*ᵥ x) ((turnBond g) v)=blank T x v:=by
 unfold branchesZ blank mulVec dotProduct
 split
 next he=>
    exact Finset.sum_eq_zero fun i _=>by
      change (if (turnBond g) v= _ then 1 else 0)*_= (0:R); rw [if_neg (show (turnBond g) v≠(turnBond g) i.val from (turnBond g).injective.ne (fun h=>i.property (h▸ he))),zero_mul]
 next ht=>
    let Y:T.Free:=⟨v,ht⟩; simp only [Matrix.of_apply,EmbeddingLike.apply_eq_iff_eq,ite_mul,one_mul,zero_mul]
    change ∑ i:T.Free,(if Y.val=i.val then x i else 0) =x Y; simp only [Subtype.coe_inj]; simp

lemma internal_split (R:Type*)[CommRing R] : Surjective ( (fromCols (tagsZ r R) (branchesZ r T R))*ᵥ ·) :=by
  intro z; let U(i : Edge (Site g)):= z ((turnBond g) i); let W:= SectorNext.Vacuum.FlatTree.erase T U; let D:= leafWard T U
  -- erase=U+climb; climb=minus d.
  let F(s:Shoot r):= D s.val; let G(e:T.Free):= W e.val
  refine ⟨Sum.elim F G,?_⟩; dsimp only; rw [fromCols_mulVec_sumElim]; funext e; obtain ⟨⟨x,i⟩,rfl⟩:= (turnBond g).surjective e
  rw [Pi.add_apply,keeps_z]
  have hx(y:Site g) : (if h:leaf r y then F ⟨y,h⟩ else 0)=D y:=by split; rfl; rename_i he; have h:y=r.embed (r.parent y):=Classical.not_not.mp he; rw [h]; exact (root_clear ..).symm
  rw [show ((turnBond g) (x,i))=(x,coord i) from rfl,qualities]; dsimp only; rw [hx, hx,show blank T G (_,_)=W _ from congrFun (YM.SectorNext.Vacuum.FlatTree.clear T U) (x,i) ] -- erase Eq.ofLp
  change D (x+step i)-D x+(U (x,i)+(D x-D (x+step i)))=U (x,i); abel

noncomputable def splints : Tab (Body 0 g) (Shoot r):= FreeResolvent.insertion fun i=> (i.val,vac)
lemma leaf_bright : d 0 g * splints r=tagsZ r ℝ:=by
 apply mulVec_injective; funext z; rw [← mulVec_mulVec]; funext ⟨x,j⟩; obtain ⟨v,rfl⟩:=axisEquiv.surjective j
 let u:= fun y:Site g=> if h:leaf r y then z ⟨y,h⟩ else 0
 have hx(y:Site g):(splints r*ᵥ z) (y,vac)=u y:=by
    unfold u; split
    next h=> let i:Shoot r:= ⟨y,h⟩; change _=z i; change (splints r*ᵥ z) (i.val,vac)=_; simp [splints,FreeResolvent.insertion,mulVec,dotProduct,Subtype.coe_inj]
    next h=> unfold mulVec dotProduct; apply Finset.sum_eq_zero; intro i _; unfold splints FreeResolvent.insertion; simp only [of_apply]; rw [if_neg,zero_mul]; intro l; exact h ((show i.val=y from congrArg Prod.fst l) ▸ i.property)
 rw [coord_map,d_sites, hx, hx,qualities]; -- rfl
lemma bolt_split : let S := fromCols (tagsZ r ℝ) (branchesZ r T ℝ); (∃ U:Tab (Shoot r⊕T.Free) (Body 1 g), S*U=1) ∧ (S*Sᵀ).det=1 :=by
 intro S; let i:= (Int.castRingHom ℝ); obtain ⟨u,g⟩:= layout_units (internalBond r T).symm _ (internal_split r T ℤ); have ht: (fromCols (tagsZ r ℤ) (branchesZ r T ℤ)).map i = S:=by
    ext x (p|p)
    · change i ((tagsZ r ℤ) _ _)=tagsZ r ℝ x p; simp only [tagsZ, Matrix.of_apply,map_sub]; split_ifs <;> simp
    change i ((branchesZ r T ℤ) _ _)=_; change i _=branchesZ r T ℝ x p; simp only [branchesZ,Matrix.of_apply]; split_ifs <;> simp
 exact ht ▸ And.intro u g
end
end YM.Fineness
#print axioms YM.Fineness.bolt_split
