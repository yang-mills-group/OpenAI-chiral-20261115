import YM.SU5.Relativistic.Yonder
import YM.SU5.Relativistic.Almanac
import YM.SU5.Relativistic.Yogurt
/-!
# numerator shadow, packed in strict time layout, on one pair of measures.

source wants retained boundary, now strengthen Euclidean nonfactor mean. keep real budget explicit
in delta. See next. All GDL. Orientation z Axis. U-memory homologue X price not Haar. Here algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open Afterglow.Tower (reflectedBox)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n k j w d u l:ℕ}{R C B τ γ γ' ε:ℝ}{M:Tulip.Male}
-- authorize on native m ash price and pay along all chart shapes. Ticker n=I.
variable {I m:Side}{K:Calibration}
private lemma rails (p:I=K.c m)(L:List (Cliplet I k))(F:Buffered.Family K)(S:Finset Cover)(T:Axis)(X:Cover)(a b:ℕ) (v:whereV L⊆ region S I)(H:Between K T 0 (b:ℤ) S)(u: Transom T S X a) : cows T (whereV L) b∧ ∀ i≠ T,cows i (whereV L) a:=by
 constructor
 · refine ⟨0,fun i o=>?_⟩; obtain ⟨z,h,rfl⟩:= mem_image.mp (v o); obtain ⟨u,w⟩:=H z h; exact ⟨z T, by omega,by omega,rfl⟩
 intro i g; refine ⟨X i,fun j x=>?_⟩; obtain ⟨z,h,rfl⟩:= mem_image.mp (v x); obtain ⟨p,v⟩:=u i g z h; exact ⟨z i,p,v,rfl⟩
-- vortices geometry coefficient = denominator expense times this ratio. height b=t*μ. static parameters.
abbrev heel (S:Side)(L U A:ℕ):ℕ:= 4*(16*S.val*heightB A+L)* (4*(U+L))^3
abbrev heels (S:Side)(L U A:ℕ):ℝ:= ((heel S L U A):ℝ)⁻¹
lemma heel_pos{S:Side}{L U A:ℕ}(p:0<L):0 < heel S L U A:=by unfold heel heightB; positivity
-- now pressure per length after apportionment
lemma cornice {γ γ' τ ε R R' :ℝ}{w u μ d j n q':ℕ}(X Y:Mark m→ℂ)(M:Tulip.Male)(T:Axis)(e:m=K.c I)
    (h': StageTw K Y j R d M)(p:0≤ R')(A:ℕ)
    (a:singleTick K A * staveP n + addgap K ≤ m.val)(q:q'+addgap K≤ m.val)
    (U:∀ L:List (Cliplet m 1),Company j M w d μ u γ γ' τ ε R' L→ heels K.B (addgap K) q' A *Py.Rate.sites m ≤ (L.length:ℕ)→
       ‖X (probe L)‖ ≤ Real.exp (-4*L.length))
    (P:∀ L: List (Cliplet m 1),Company j M w d μ u γ γ' τ ε R' L → ‖X (probe L)- Y (probe L)‖≤ Real.exp (-4*Py.Rate.sites m))
    (S: Finset Cover) (V:Buffered.Family K)(g:Between K T 0 (ruler K.B* (towerH (heightB A) n:ℕ)) S)(x:Cover)(g₀:Transom T S x (q'))
    (p':Batch K V S (staveP n) I j M 1 w d μ u γ γ' τ ε R') : ‖X (arrange _ _ e.symm (V I))‖ ≤ Real.exp (-2*staveP n):=by
 subst m; let m:=K.c I
 obtain ⟨L,l',s',u',f⟩:= p'.ticket; let D:=singleTick K A; let C:=q'; let B:=addgap K; let P':=staveP n
 have he: Between K T 0 (↑(D*P'):ℤ) S:=by
    rw [show (↑(D*P'):ℤ)=ruler K.B*(towerH (heightB A) n:ℕ) by unfold D P' towerH ruler singleTick; push_cast; ring]; exact g
 obtain ⟨h₁,v⟩:= rails rfl L V S T x C (D*P') s' he g₀
 obtain ⟨r,e,L',W,vL,vX,hV⟩:= prism h' rfl T a q L f h₁ v
 let Y₁:= Py.Rate.sites m
 have ht: L'.length=r*P':= vL.trans (congrArg (r*·) l')
 have hv:0<P':=by unfold P' staveP; positivity
 let dK:= heel K.B B q' A
 have hX:(↑(r*P':ℕ):ℝ) ≤ Py.Rate.sites m:=by have ht: (r*P')≤ (More m).val^4:=ht ▸ W.pcount Nat.zero_lt_one; unfold Py.Rate.sites; exact_mod_cast ht
 have hx: (More m).val^4 ≤ L'.length*dK:=by
    rw [ht]; refine hV.trans ?_
    have hh: D*P'+B ≤ (D+B)*P':=by rw [add_mul]; apply Nat.add_le_add_left; exact Nat.le_mul_of_pos_right _ hv
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r (Nat.mul_le_mul_left 4 hh))).trans_eq
    unfold dK heel; unfold D singleTick; ring
 have hC: ‖X (probe L')‖≤ Real.exp (-4*L'.length):=by
    apply U L' W; unfold heels; rw [mul_comm,←div_eq_mul_inv]; exact (div_le_iff₀ (by exact_mod_cast (heel_pos (S:=K.B) (L:=addgap K) (U:=q') (A:=A) addgap_pos))).2 (by unfold Py.Rate.sites; exact_mod_cast hx)
 -- compare Y both, roots
 have hτ:= P L' W
 let ℓ:= ((-4:ℝ)*Y₁)
 let α:= P'*(r:ℝ); have hR0: (1:ℝ) ≤ ↑r:=by exact_mod_cast (show 1 ≤ r from e)
 have hu: 1≤ (P':ℝ):=by exact_mod_cast (show 1 ≤ P' from hv)
 have hGα: 1 ≤ α:=by unfold α; nlinarith only [hR0,hu];
 have he':Py.Rate.sites m ≥ α:=by push_cast at hX; unfold α; rw [mul_comm]; exact hX
 let B₁:=(-3:ℝ)*P'; let D':=Real.exp B₁; have h': ‖Y (probe L)‖ ≤ D':=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le e.ne').mp; apply vX.trans; apply (norm_le_norm_sub_add (Y (probe L')) (X (probe L'))).trans; rw [norm_sub_rev,← Real.exp_nat_mul]; apply (add_le_add hτ hC).trans; change Real.exp ℓ+Real.exp (-4*L'.length) ≤ _; rw [show (r:ℝ)* B₁=(-4*α)+α by unfold α B₁; ring,Real.exp_add]
    have he:Real.exp ℓ ≤ Real.exp (-4*α):=Real.exp_le_exp_of_le (by unfold ℓ Y₁; linarith only [he']); have hp': (2:ℝ) ≤ Real.exp α:=by linarith only [Real.add_one_le_exp α,hGα]
    rw [ht,Nat.cast_mul, mul_comm (r:ℝ)]; change Real.exp ℓ+Real.exp (-4*α) ≤ _; nlinarith only [he,hp',Real.exp_pos (-4*α)]
 change ‖X (V I)‖ ≤ _; rw [←u']; apply (norm_le_norm_sub_add _ (Y (probe L))).trans; apply (add_le_add (P L f) h').trans
 have hQ: Py.Rate.sites (K.c I)≥ ↑P':= (le_trans (show (P':ℝ)≤ α from le_mul_of_one_le_right (by positivity) hR0) he');
 have hρ: -4*Py.Rate.sites (K.c I) ≤ B₁:=by unfold B₁; linarith only [hQ,hu]
 rw [show (-2:ℝ)* (staveP n:ℝ)=B₁+(P':ℝ) by unfold P' B₁; change _= (-3:ℝ)*↑(staveP n)+_; ring, Real.exp_add]; change _ ≤ D'*_
 have hx': Real.exp (-(4:ℝ)*Py.Rate.sites (K.c I)) ≤ D':= Real.exp_le_exp_of_le hρ; have hp: (2:ℝ) ≤ Real.exp (staveP n:ℝ):=by have g:=Real.add_one_le_exp (P':ℝ); apply le_trans _ g; linarith only [hu]
 nlinarith only [hx',hp,(show 0<D' from Real.exp_pos _)]
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.cornice
