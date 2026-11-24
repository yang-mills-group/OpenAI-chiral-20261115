import YM.CF.Cour.Thrush
import YM.CF.Cour.Tul
import YM.CF.Cour.EdgeC
import YM.CF.Levier.Hymn
import YM.CF.Hom.Sally
import YM.CF.Cour.Monet
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory
open Pec Reef Levier
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{p: Aim N}
variable {p': Aim (CSide X B)}{o: Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{M:Male}
variable {p d:ℝ}
lemma portY (n:ℕ)(p:1≤ C):∃ K:ℝ,C≤K∧∀ {m X B:Side}{e:ℝ}(G:Ratio (CSide m B) (CSide X B))(j:Sweep (CSide m B))(S: Seal (Site (More (CSide X B))))(W: Rent0 G e→ℂ)(v:ℝ), Flash (dressL G e) (LineE n G K e) n S W v→ Flash (dressL G e) (LineE n G C e) n (toRoar G j S) (fun y=>payZ j (W (male e G j y))) v:=by
 obtain ⟨K,h,H⟩:=Spire.tutor C n p; refine ⟨K,h,fun {m X B e} G j S W v ht=>?_⟩; let T:Rent0 G e→ℂ:=W ∘ male e G j
 have hp:Flash (dressL G e) (LineE n G C e) n (toRoar G j S) T v:=by
    refine Flash.hop (L:=male e G j) (Q:=LineE n G K e) ?_ (male_c ..) ht (fun v=>(prow _ _).plus (ht.travel v)) (fun x y=>male_r _ _ _ _ x y) (fun x y=> ⟨_,male_g ..⟩)
    intro A _ _ _ V v f t i hi; obtain ⟨hu,hv⟩:= t i hi; let F:=fun i:A=> (f i).val.1; let X:=fun i:A=> (f i).val.2; let D(N:Side)(_:A)(_:Site (More N)):=apex
    have he(N): Jet.seek (D N) n i C:=fun x=> allows_const i ((vote_unit apex).le.trans p)
    exact ⟨(H _ _ _ _ F i (D _) hu (he _)).1,(H _ _ _ _ X i (D _) hv (he _)).1⟩
 unfold payZ cSignX; split; swap; exact hp
 let P:=hp.linear Complex.conjCLE.toContinuousLinearMap (show ‖Complex.conjCLE.toContinuousLinearMap‖≤1 by simp); rw [one_mul] at P; exact P -- tune
abbrev tyke(G: Ratio (CSide m B) (CSide X B))(M:Msca m X B G e):Prop:=∀ j S y,M (toRoar G j⁻¹ S) (male e G j y)=payZ j (M S y)
def patina (M:Msca m X B G e)(S:Seal (Site (More (CSide X B))))(y:Rent0 G e):ℂ:=
 let f(j:Sweep (CSide m B)):=payZ j (M ((weaveS G j).symm S) (male e G j y)); (Fintype.card (Sweep (CSide m B)):ℝ)⁻¹ • ∑ i,f i
noncomputable def din (j:Sweep N): ℂ ≃L[ℝ]ℂ:= if wageZ j then Complex.conjCLE else ContinuousLinearEquiv.refl ..
lemma din_t(j:Sweep N)(x:ℂ): din j x=payZ j x:=by unfold din payZ cSignX; split <;> rfl
lemma izard(j:Sweep N)(x:ℂ): payZ j (payZ j x)=x:=by unfold payZ; rw [sign_seq]; simp; rfl
lemma patina_T (M:Msca m X B G e):tyke G (patina M):=by
 intro j S y; unfold patina; dsimp only; rw [← din_t,map_smul,map_sum]; apply congrArg; conv_rhs =>rw [← Equiv.sum_comp (Equiv.mulLeft j)]
 refine sum_congr rfl fun k _=>?_ ; change _=din j (payZ (j*k) (M _ _)); rw [din_t, male_m,show (weaveS G k).symm (toRoar G j⁻¹ S)=(weaveS G (j*k)).symm S from ?_,←warX,izard]
 rfl
 change toRoar G k⁻¹ (toRoar G j⁻¹ S)=toRoar G (j*k)⁻¹ S; rw [swept,mul_inv_rev]
lemma rumR (j:Sweep (CSide m B))(S):(weaveS G j S).card=S.card:= Finset.card_image_of_injective _ (Shape.anon_b _).1
lemma cityP(n:ℕ)(p:1≤C):∃ K:ℝ,C≤K ∧∀{m X B:Side}{e:ℝ}(G: Ratio (CSide m B) (CSide X B))(M:Msca m X B G e)(Φ:nomA m X B→ℂ)(s a h:ℝ), Tally M Φ s K a h n → (∀ j (x:Rent0 G e),Φ (male e G j x).val=payZ j (Φ x.val)) → Tally (patina M) Φ s C a h n:=by
 obtain ⟨K,h,H⟩:=portY n p
 refine ⟨K,h,fun {m X B e} G M Φ s a h t p=>?_⟩; obtain ⟨W,w,u⟩:= t.members
 let V:= (Sweep (CSide m B)); let f:= ((Fintype.card V:ℝ)⁻¹); have hh:0<f:=by unfold f; positivity
 let X'(i:Seal (Site (More (CSide X B)))):= f * ∑ j:Sweep (CSide m B), W ((weaveS G j).symm i)
 refine ⟨⟨X',fun i=> ?_,fun i=>?_⟩,fun v hp=>?_⟩
 · have hp'(j:Sweep (CSide m B)):Flash (dressL G e) (LineE n G C e) n i (fun x=> payZ j (M ((weaveS G j).symm i) (male e G j x))) (W ((weaveS G j).symm i)):=by
       have hQ:= H G j _ _ _ (w ((weaveS G j).symm i)); rwa [show toRoar G j ((weaveS G j).symm i)=i from (weaveS G j).apply_symm_apply i] at hQ
   let D:= Flash.collects Finset.univ _ _ fun j _=>hp' j
   exact D.linear (f • ContinuousLinearMap.id ℝ ℂ) (le_trans (le_of_eq (norm_smul f _)) (by rw [Real.norm_of_nonneg hh.le]; simp))
 · let P(j:Sweep (CSide m B)):= ∑ S∈hit0 i,Branch.rent a S* W ((weaveS G j).symm S); unfold hitE X'; 
   have he(S:Seal (Site (More (CSide X B)))):Branch.rent a S*(f*∑ j:Sweep (CSide m B),W ((weaveS G j).symm S))= f*∑ j:Sweep (CSide m B),Branch.rent a S *W ((weaveS G j).symm S):=by rw [←Finset.mul_sum,mul_left_comm]
   simp_rw [he,←Finset.mul_sum (s:=hit0 i) (a:=f)] -- fix
   rw [Finset.sum_comm]; have ht(j:Sweep (CSide m B)):P j≤h:=by
       obtain ⟨o,l⟩:= ((castX j).broad G).anon_b.2 i
       apply le_trans ?_ (u o); apply le_of_eq; unfold P hitE hit0; simp_rw [sum_filter]; conv_lhs=>rw [← Equiv.sum_comp (weaveS G j)]
       refine sum_congr rfl fun k _=>?_ ; rw [(weaveS G j).symm_apply_apply,show Branch.rent a (weaveS G j k)=Branch.rent a k from (by unfold Branch.rent; rw [rumR])]; have ht:i ∈ weaveS G j k ↔ o∈k:=by rw [←l]; change _∈ k.image ((Shape.broad G (castX j)).anon _) ↔_; simp [((castX j).broad G|>.anon_b.1.eq_iff)]
       simp [ht] -- wrong
   apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) fun j _=>ht j) hh.le); rw [sum_const,card_univ,nsmul_eq_mul]; unfold f; rw [←mul_assoc, inv_mul_cancel₀ (by positivity),one_mul] -- tune syntax
 let y:↑(Rent0 G e):=⟨v,hp⟩; unfold patina; dsimp only; simp_rw [←Finset.smul_sum]; rw [Finset.sum_comm (s:=(univ:Finset (Seal (Site (More (CSide X B))))))]
 have he(j:Sweep (CSide m B)): (∑ i,payZ j (M ((weaveS G j).symm i) (male e G j y)))= Φ v:=by simp_rw [←din_t, ← map_sum]; rw [Equiv.sum_comp (weaveS G j).symm (fun i=>M i (male e G j y)), ← t.even (male e G j y).val (male e G j y).property, din_t, p,izard] -- align
 change _=f • ∑ j,∑ i,payZ j (M ((weaveS G j).symm i) (male e G j y)); simp_rw [he]; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; unfold f; rw [inv_mul_cancel₀ (by positivity),one_smul] -- tune
end YM.CF.Cour
