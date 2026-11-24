import YM.SU5.Relativistic.Magnol
/-! # finite two-sided accounting + seat-only cost. -/
/-! # Concretion with caloric flags. Exact direct fields. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 590000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Franc.Meshy
open Function Filter NormedSpace Metric Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel Pannier.Chancel.ScreeV Cliplet RG Tenant Scree Loaves
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate (sites)
open Afterglow.Tower Afterglow.Journey
variable {N m n:Side}{k w d:ℕ}{M:Tulip.Male}{η p μ C B τ:ℝ}
variable (pB:∀ (S:Side)(A:Op (Single S))(q:IsStarProjection A)(T:Pea (Single S)), Franc.Price (T.mint.foldC (Saber (B:=tickA S) q k)) B)
variable {L:List (Cliplet N 1)}
def soot(U:Pane N)(t:ℝ)(d:ℕ)(A:Cliplet N 1) : Bool:= @decide (¬A.feel t d U) (Classical.propDecidable _)
private lemma chartRent {α:Type*}(L:List α) (p:α→Bool)(a b:ℝ): (L.map fun i=>a+ if p i=true then b else 0).sum= L.length *a + (L.filter p).length*b:=by
 induction L with| nil=>simp| cons i L ih=>simp only [List.map_cons,List.sum_cons,ih,List.length_cons,List.filter_cons]; split <;> rename_i h <;> simp [*,add_mul] <;> ring
open _root_.YM.CF.Py.Rate.Pannier
include pB
lemma turrV {Y: Skye.Orbit N→Pane N}{s:ℕ}{u:ℝ}(W:Roof N u p s Y)(g:τ≤u)(f:w+s≤d)(x:0≤η)(p':0 < C)(U:Battalion M k w d p τ η μ C B L)(A: Skye.Orbit N) (v:Wave (Single N))(X:IsStarProjection (spar 4 M (Y A)))(r:Sea (spar 4 M (Y A)) v) (a:0≤ μ) (p0:4*η≤ μ):
    ∃ (T:Shaft (Single N))(b:ℝ), 0<b ∧ ‖T.sell‖≤ 2 ∧ ‖T.buy‖≤2 ∧ ‖(Saber (B:=tickA N) X k).glow (probe L (A.1,Y A))*((b:ℂ)⁻¹ • quant T.buy)‖ * ‖(b:ℂ) • acts (quant T.sell) v‖ ≤ Real.exp (L.length*(μ+μ)+ C*(4*(d+d+1)^4:ℕ)*flakes τ A.1) :=by
 classical
 let q:= soot A.1 τ d
 have he(i):q i=true ↔ ¬ i.feel τ d A.1:=by unfold q soot; exact @decide_eq_true_iff _ (Classical.propDecidable _)
 let F:Fields N:=(A.1,Y A);let G(i:Cliplet N 1):=modesIn N i.broad; let H:=Saber (B:=tickA N) X k; let s0:= slept (Single N)
 let δ(i):=μ+ if q i then C else 0
 have hp(i)(t:i∈ L): Nought H (i.frame F) (spar 4 M (Y A)) η (δ i) (G i):=by -- can't infer P
    unfold δ; split
    next x'=>
       constructor; refine ⟨s0,(by unfold Shell s0; rw [Pea.slept_r,mul_zero]),(by rw [show s0.leak _=0 from Pea.slept_b.2.2 _]; exact x),fun T _=>?_⟩
       let V:= (U.granted i t).raw F (T.mint.foldC H) (pB _ _ X T); rw [show s0.hat=1 from slept_b.1,mul_one]; apply V.trans; linarith only [Real.add_one_le_exp (μ+C),a]
    next h=>
       have hT:i.feel τ d A.1:=by_contra fun k=>h ((he i).mpr k)
       rw [add_zero]; refine (U.granted i t).casts F (W.paid A) hT (fledged W (Lattice.halo w i.broad) A g ?_) X
       exact Finset.disjoint_of_subset_left (Finset.Subset.trans (Staff.hollowG i.broad) (Staff.crease f (Subset.refl _))) hT
 obtain ⟨Z,c,j⟩:=victoryS _ _ G δ L (U.lock.imp (fun {a b} h=> disjoint_left.mpr (fun i g e=>disjoint_left.mp h ((modes_at ..).1 g) ((modes_at ..).1 e)))) hp s0 ∅ (by unfold s0 Shell; rw [Pea.slept_r,mul_zero]) (fun _ _=>disjoint_empty_left _)
 rw [show s0.tagH=1 from slept_b.2.1,one_mul] at j; rw [show s0.leak (spar 4 M (Y A))=0 from slept_b.2.2 _,zero_add] at c
 refine ⟨Z.mint,Z.candy,Z.duty,Z.signed.1,Z.signed.2,?_⟩; rw [probe_at]; apply (mul_le_mul j (Z.frosty X v r) (norm_nonneg _) (Real.exp_pos _).le).trans; rw [←Real.exp_add,show _ = L.length * μ +(L.filter q).length*C from chartRent L q μ C]; apply Real.exp_monotone
 have hz:= mul_le_mul_of_nonneg_left p0 (show 0 ≤ (L.length:ℝ) by positivity); have hx:( (L.filter q).length:ℝ) ≤ (4*(d+d+1)^4:ℕ)*flakes τ A.1:=by
    apply (Nat.cast_le.mpr (U.dirty A.1)).trans_eq; unfold flakes; push_cast; ring
 nlinarith only [c,hz,mul_le_mul_of_nonneg_left hx p'.le]
omit pB
open Buffered.Afterglow.Tower
open Tower.SlabMark
variable {K:Calibration}{I:Side}
private lemma rails (p:I=K.c m)(L:List (Cliplet I 1))(F:Buffered.Family K)(S:Finset Cover)(T:Axis)(X:Cover)(a b:ℕ) (v:whereV L⊆ region S I)(H:Between K T 0 (b:ℤ) S)(u: Transom T S X a) : cows T (whereV L) b∧ ∀ i≠ T,cows i (whereV L) a:=by
 constructor
 · refine ⟨0,fun i o=>?_⟩; obtain ⟨z,h,rfl⟩:= mem_image.mp (v o); obtain ⟨u,w⟩:=H z h; exact ⟨z T, by omega,by omega,rfl⟩
 intro i g; refine ⟨X i,fun j x=>?_⟩; obtain ⟨z,h,rfl⟩:= mem_image.mp (v x); obtain ⟨p,v⟩:=u i g z h; exact ⟨z i,p,v,rfl⟩
-- coarse exponent > omega per LENGTH all placements. Kernel sensitivity permits comparing
lemma curr {q':ℕ}(n:ℕ)(X Y:Mark m→ℂ)(T:Axis)(e:m=K.c I)
    (h': Twosome K m Y) (p0:Muster p m M)
    (s:ℕ) (a:s*ruler K.B*(staveP n:ℕ)+ addgap K ≤ (m.val:ℤ))(q:q'+addgap K≤ m.val)
    (A:ℕ)(D:s=heightB A)(g:0<μ)
    (U:∀ L:List (Cliplet m 1),Battalion M k w d p τ η μ C B L→ heels K.B (addgap K) q' A *Py.Rate.sites m ≤ (L.length:ℕ)→
       ‖X (probe L)‖≤ Real.exp (L.length*(3*μ)))
    (P:∀ L: List (Cliplet m 1),Battalion M k w d p τ η μ C B L → ‖X (probe L)- Y (probe L)‖≤ μ)
    (S: Finset Cover) (V:Buffered.Family K)(r:Between K T 0 (ruler K.B* (towerH s n:ℕ)) S)(x:Cover)(g₀:Transom T S x q')
    (p':Galop K V S (staveP n) I k M w d p τ η μ C B) : ‖X (Tapestry.arrange _ _ e.symm (V I))‖ ≤ Real.exp ((staveP n:ℕ)*(5*μ)):=by
 subst m; let m:=K.c I; subst s
 obtain ⟨L,l',s',u',f⟩:= p'.ticket; let D:=singleTick K A; let B':=q'; let C':=addgap K; let P':=staveP n
 have he: Between K T 0 (↑(D*P'):ℤ) S:=by rw [show (↑(D*P'):ℤ)=ruler K.B*(towerH (heightB A) n:ℕ) by unfold D P' towerH ruler singleTick; push_cast; ring]; exact r
 obtain ⟨h₁,v⟩:= rails rfl L V S T x B' (D*P') s' he g₀
 have hz:D*P'+ C'≤ m.val:=by
    have hx:(↑(D*P'+C'):ℤ)= heightB A*ruler K.B*(staveP n:ℕ)+(addgap K:ℤ):=by unfold D P' C' singleTick ruler; push_cast; ring
    exact_mod_cast (hx.trans_le a)
 obtain ⟨r,e,L',W,vL,vX,hV⟩:= prism h' p0 rfl T hz q L f h₁ v
 let Y₁:= Py.Rate.sites m; have ht: L'.length=r*P':= vL.trans (congrArg (r*·) l')
 have hv:0<P':=by unfold P' staveP; positivity
 let dK:= heel K.B C' q' A
 have hx: (More m).val^4 ≤ L'.length*dK:=by
    rw [ht]; refine hV.trans ?_
    have hh: D*P'+C' ≤ (D+C')*P':=by rw [add_mul]; apply Nat.add_le_add_left; exact Nat.le_mul_of_pos_right _ hv
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r (Nat.mul_le_mul_left 4 hh))).trans_eq; unfold dK heel; unfold D singleTick; ring
 have hC: ‖X (probe L')‖≤ Real.exp (L'.length*(3*μ)):=by
    apply U L' W; unfold heels; rw [mul_comm,←div_eq_mul_inv]; exact (div_le_iff₀ (by exact_mod_cast (heel_pos (S:=K.B) (L:=addgap K) (U:=q') (A:=A) addgap_pos))).2 (by unfold Py.Rate.sites; exact_mod_cast hx)
 have hτ:= P L' W; let M':=Real.exp ((P':ℝ)*(4*μ)); have he': ‖Y (probe L)‖≤ M':=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) ((Real.exp_pos _).le) e.ne').mp; apply vX.trans; apply (norm_le_norm_sub_add (Y (probe L')) (X (probe L'))).trans; rw [norm_sub_rev]; apply (add_le_add hτ hC).trans
    change μ+_≤M'^r; unfold M'; rw [← Real.exp_nat_mul]; rw [ht,Nat.cast_mul]; let x:ℝ:= (r:ℝ)* (P':ℝ); change μ+Real.exp (x*(3*μ))≤_; rw [show (r:ℝ)*( (P':ℝ)*(4*μ)) = x*(3*μ)+x*μ by unfold x; ring, Real.exp_add]; have hr: 1 ≤ x:=by unfold x; exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast e) (by exact_mod_cast hv)
    have hp:0<x:=zero_lt_one.trans_le hr; have hx:1 ≤ Real.exp (x*(3*μ)):= Real.one_le_exp (by positivity)
    have hz':1+ μ ≤ Real.exp (x*μ):=by nlinarith only [mul_le_mul_of_nonneg_right hr g.le,Real.add_one_le_exp (x*μ)]
    nlinarith
 change ‖X (V I)‖≤_; rw [←u']; apply (norm_le_norm_sub_add _ (Y (probe L))).trans; apply (add_le_add (P L f) he').trans
 change μ+M'≤_; rw [show (↑(staveP n):ℝ)*(5*μ)=(P':ℝ)*(4*μ)+P'*μ by unfold P'; ring,Real.exp_add]; change μ+M' ≤M'*_
 have ht':1 ≤ M':=Real.one_le_exp (by positivity); have hx':1+μ≤Real.exp (P'*μ):=by nlinarith only [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤↑P' by exact_mod_cast hv) g.le,Real.add_one_le_exp (P'*μ)]
 nlinarith
end YM.CF.Papyrus.Franc.Meshy
#print axioms YM.CF.Papyrus.Franc.Meshy.curr
