import YM.SU5.Fineness.Storey
/-!
# Pick a forest-free coordinate transversal to gauge roots, built on actual torus.
It doesn't need a LOCAL generation rule. Keeps *precise* determinant price valid
when measure proofs later pay out defects with only a subset of this transversal.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Matrix Lattice Wilson RG Exterior Precision Tree
open scoped Matrix BigOperators Classical
variable {I J K L : Type*}[Fintype I][Fintype J][Fintype K][DecidableEq I][DecidableEq J][DecidableEq K]
private lemma kept_cols (A:Tab I J)(D:Tab I K)(p:Injective (A *ᵥ ·)) (h:Surjective ((fromCols A D) *ᵥ ·)) : ∃ s:Finset K, let C:= D.submatrix id (fun i:s=> (i:K)); Bijective ((fromCols A C) *ᵥ ·) :=by
 let F:= fromCols A D; let z:= F.col; let T:=Set.range (Sum.inl: J→ J ⊕ K)
 let e (t:T) := (Equiv.ofInjective (Sum.inl: J→ J ⊕ K) (Sum.inl_injective)).symm t
 have ht (t:T) : (t:J⊕K)=Sum.inl (e t):= by obtain ⟨a,h,rfl⟩:=t; unfold e; exact congrArg Sum.inl (Equiv.symm_apply_apply _ h).symm
 have he : Injective e:=fun i j u=> Subtype.ext (by rw [ht,ht j,u])
 have hT: LinearIndepOn ℝ z T:=by
    have hv:= (mulVec_injective_iff.mp (show Injective A.mulVec from p)).comp e he
    rw [show A.col ∘ e= z ∘ Subtype.val by funext i; rw [Function.comp_apply, Function.comp_apply,ht]; rfl] at hv; exact hv
 let U:= hT.extend (Set.subset_univ _); let s := Finset.univ.filter fun (x:K)=>Sum.inr x∈U; refine ⟨s,?_⟩; intro C; let f (x:J ⊕ s) : J ⊕ K:= Sum.map id Subtype.val x
 have hm(x:J⊕s): f x∈ U:=by cases x with | inl a=> exact hT.subset_extend _ ⟨a,rfl⟩| inr b=> exact (Finset.mem_filter.mp b.property).2
 let z'(x):U:= ⟨f x,hm x⟩; have hZ: Injective z':= by
    intro i j h; exact (Sum.map_injective.mpr ⟨injective_id, Subtype.val_injective⟩) (congrArg Subtype.val h)
 let B:= fromCols A C; have hpC(x):B.col x=z (f x):=by cases x <;> rfl
 have hsT: Set.range B.col = z '' U:=by
    ext v; constructor
    · rintro ⟨w,rfl⟩; exact ⟨_,hm w,(hpC _).symm⟩
    rintro ⟨u,t,rfl⟩; cases u with
    | inl a=> exact ⟨Sum.inl a,rfl⟩
    | inr k=> exact ⟨Sum.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,t⟩⟩,rfl⟩
 have hv:LinearIndependent ℝ B.col:=by
    have hP:= (show LinearIndependent ℝ (z ∘ (Subtype.val : U → _)) from hT.linearIndepOn_extend _).comp z' hZ
    exact (show z∘ Subtype.val ∘ z'= B.col from funext fun i=> (hpC i).symm) ▸ hP -- comp notation associative parse?
 refine ⟨mulVec_injective_iff.mpr hv,?_⟩; change Surjective B.mulVecLin; apply LinearMap.range_eq_top.mp; rw [range_mulVecLin,hsT, show Submodule.span ℝ _ = _ from hT.span_image_extend_eq_span_image (Set.subset_univ _), Set.image_univ]; exact F.range_mulVecLin ▸ LinearMap.range_eq_top.mpr h

variable {c n : Side}{r: Ratio c n}
abbrev seatsF (T: Forest r)(b:Finset T.Free) := (branchesZ r T ℝ).submatrix id (fun i:b=> i.val)
def Buttress (T:Forest r)(b:Finset T.Free):= Bijective ((fromCols (sightZero n) (seatsF T b))*ᵥ ·)
private lemma lineX : Injective (sightZero n *ᵥ ·):=by intro v w p; exact sub_eq_zero.mp (no_ghost n ((mulVec_sub ..).trans (sub_eq_zero.mpr p)))
lemma buttress_uses (T:Forest r) : ∃ b:Finset T.Free, Buttress T b:=by
 apply kept_cols _ _ lineX; intro L
 obtain ⟨u,h⟩:= internal_split r T ℝ L; dsimp only at h; rw [fromCols_mulVec] at h
 obtain ⟨v,g⟩:= flecks (n:=n) (z:=tagsZ r ℝ*ᵥ (u∘ Sum.inl)) (by rw [←leaf_bright,mulVec_mulVec, ←Matrix.mul_assoc, closed 0 n, Matrix.zero_mul,zero_mulVec])
 exact ⟨Sum.elim v (u∘ Sum.inr),(fromCols_mulVec_sumElim ..).trans (g.symm ▸ h)⟩
private lemma torGrade (n:Side) : Fintype.card (Puncture n)= Fintype.card (Site n)-1:=by unfold Puncture; rw [Fintype.card_subtype_compl (fun x:Site n=> x=0), Fintype.card_subtype_eq]
lemma tierCard {T:Forest r}{b:Finset T.Free} (p:Buttress T b) : Fintype.card ((Puncture n⊕Axis)⊕ ↥b) = Fintype.card (Body 1 n):=by
 let A:=fromCols (sightZero n) (seatsF T b); let E:= LinearEquiv.ofBijective A.mulVecLin (show Bijective A.mulVecLin from p);
 simpa only [Module.finrank_pi] using E.finrank_eq
lemma Buttress.count {T:Forest r}{b:Finset T.Free} (p:Buttress T b): b.card=3*(Fintype.card (Site n)-1):=by
 have ht:= tierCard p; rw [Fintype.card_sum,Fintype.card_sum,torGrade,Fintype.card_coe,bond_count] at ht
 have he:= Fintype.card_pos (α:=Site n); rw [show Fintype.card Axis=4 from Fintype.card_fin _] at ht; omega
lemma Tallied.folio (n:Side) : Tallied (sightZero n):=by -- in Storey private
 refine Tallied.duo ?_ ?_
 · refine tallied fun ⟨x,i⟩ z=>?_ ; obtain ⟨b,rfl⟩:=axisEquiv.surjective i; rw [coord_map,blade]; split_ifs  <;> (first| (refine ⟨0,?_⟩; solve|norm_num) | (refine ⟨1,?_⟩; solve|norm_num) | (refine ⟨-1,?_⟩; solve|norm_num))
 refine tallied fun i k=>?_ ; unfold harmonic; rw [of_apply]; split <;> first| exact ⟨0,(Int.cast_zero).symm⟩ | exact ⟨1,(Int.cast_one).symm⟩
lemma Tallied.seatsF (T:Forest r)(b:Finset T.Free) : Tallied (seatsF T b):=by refine ⟨(branchesZ r T ℤ).submatrix id (fun x:b=>x.val),?_⟩; ext i j; unfold Fineness.seatsF branchesZ; rw [map_apply]; simp only [submatrix_apply,Matrix.of_apply]; split_ifs <;> simp
-- exact orientation and SPD proof for full block
lemma Buttress.precision {T:Forest r}{b:Finset T.Free}(q:Buttress T b){A:Sheet (Body 2 n)}(h:A.PosDef): let C:=seatsF T b; let B:= Cᵀ*Precision.K A*C; B.PosDef ∧ leasePart A ≤ B.det :=by
 intro C B; let D:= sightZero n; let T:= fromCols D C -- shadow T ok?
 let H:= lattice_null A ((q_iff A).1 h).1
 have p:Tᵀ*Precision.K A*T=fromBlocks 0 0 0 B :=by
    unfold T; rw [Matrix.mul_assoc, mul_fromCols,H.nullA, transpose_fromCols, fromRows_mul_fromCols, ← Matrix.mul_assoc, H.turnA]; simp [B,Matrix.mul_assoc] -- perhaps D not reducible
 let Z:= Puncture n⊕Axis; let Y:= fromRows (1:Sheet Z) (0:Tab b Z); have hf:T*Y=D:=by unfold T Y; rw [fromCols_mul_fromRows]; simp
 let E:((Puncture n⊕Axis) ⊕ ↥b)≃ Body 1 n := Fintype.equivOfCardEq (tierCard q)
 have hp: Rail T:=Rail_of_zero _ (fun u p=> q.1 (p.trans (mulVec_zero _).symm)); let R:=axes T; have hh:R*T=1:=axes_deck hp; have hx:=H.resize T R E hf ((Matrix.mul_eq_one_comm_of_equiv E).mp hh) hh
 have hg:B.PosDef:= by
    apply (q_iff B).2; refine ⟨?_,fun u v=>?_⟩
    · unfold B; rw [transpose_mul,transpose_mul, H.symmA,transpose_transpose,Matrix.mul_assoc]
    rw [show qpay B u=qpay (Precision.K A) (C*ᵥ u) from qgain ..,show qpay (Precision.K A) _=qpay A (d 1 n*ᵥ (C*ᵥ u)) from qgain ..]; apply q_at A h; intro Zf; obtain ⟨i,p⟩:=flecks Zf; have he:Sum.elim i (0:↥b→ℝ)= Sum.elim (0:Z→ℝ) u:= q.1 (show T*ᵥ _=T*ᵥ _ from (by unfold T; rw [fromCols_mulVec_sumElim,fromCols_mulVec_sumElim,mulVec_zero, mulVec_zero, zero_add,add_zero]; exact p)); exact v (funext fun j=>(congrFun he (.inr j)).symm)
 have ht:Tallied T:= (Tallied.folio n).duo (Tallied.seatsF _ _)
 refine ⟨hg,?_⟩; rw [p,(ZeroBasis.filled Z).right_bill B ((q_iff B).1 hg).1,ZeroBasis.paid,one_mul] at hx
 rw [hx]; exact le_mul_of_one_le_left (lattice_pos h).le ((ht.twisted.multi ht).at_least hp.gramPos.det_pos)
end YM.Fineness
#print axioms YM.Fineness.buttress_uses
#print axioms YM.Fineness.Buttress.precision
