import YM.SU5.Relativistic.Varro
/-!
# gauge and dirty licenses carry also. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
def Pea.mirrorU (X:Pea I)(U: UNI I):= (X.face 1).face U
def moveS(T:Shaft I)(U:UNI I): Shaft I:=⟨twist U T.sell,twist U T.buy,by rw [←map_mul,T.payment,map_one]⟩
private lemma mirrorT(T:Pea I)(U:UNI I): (T.mirrorU U).mint=moveS T.mint U:=by
 unfold Pea.mirrorU moveS Pea.mint; congr 1; all_goals unfold Pea.Φ Pea.face; dsimp only; simp only [map_add,map_smul,map_one]; congr 2 <;> simp [twist_formula]
lemma motz (S:Finset I)(U: UNI I) (B P: Op I) (u:IsStarProjection P)(v:IsStarProjection (twist U P))(x:twist U B=B)(z:twist U (cutM S)=cutM S)(F:FC I)(k:ℕ){η κ:ℝ} (e:Nought (Saber (B:=B) u k) F P η κ S): Nought (Saber (B:=B) v k) (twist (quantU U) F) (twist U P) η κ S:=by
 obtain ⟨T,h,b,w⟩:=e.slips; constructor; let Q:=T.mirrorU U; have he(X:Op I): twist (1:UNI I) X=X:=by simp [twist_formula]
 have hp: Shell (T.face 1) S:=h.turn (he _)
 refine ⟨Q,hp.turn z,?_ ,fun A t=>?_⟩
 · have hv:= (T.face 1).posture U (1-P); rw [show 1-twist U (1-P)=twist U P by simp only [map_sub,map_one,sub_sub_cancel]] at hv; unfold Q Pea.mirrorU; rw [hv,← he P,T.posture]; -- rewrite tune
   exact b
 let K:= (A.face (star U)).face (star (1:UNI I)); have hx:K.mirrorU U=A:=by
    unfold K Pea.mirrorU; have hl(X:Pea I)(P:UNI I): (X.face (star P)).face P=X:=by have hb:= face_step (star P) X; rw [star_star] at hb; exact hb
    rw [hl,hl] -- inverse pattern
 have ht:= (t.turnP (star U)).turnP (star (1:UNI I)); unfold Q Pea.mirrorU at ht; rw [face_step,face_step] at ht
 let W':= K.mint.foldC (Saber (B:=B) u k); let f:=twist (quantU U)
 have hj:twist (quantU U) T.hat=Q.hat:=by
    unfold hat; rw [twist_scalar,←quant_twist,show Q.candy=T.candy by unfold candy Pea.nodes Q Pea.mirrorU; rw [show ((T.face 1).face U).fill=twist U (twist 1 T.fill) from rfl,trace_twist, trace_twist],show Q.mint=moveS T.mint U from mirrorT ..]; rfl
 have hk:((A.mint.foldC (Saber (B:=B) v k)).glow (f F))= f (W'.glow F):=by
    have he:Saber (B:=B) v k=moveS (Saber (B:=B) u k) U:=by unfold Saber moveS; congr 1; rw [map_add,map_star,map_one,←je_twist,x]; rw [map_sub,map_star,map_one,←je_twist,x]
    nth_rw 1 [←hx]; rw [mirrorT,he]; unfold Shaft.glow Shaft.foldC moveS f; simp only [map_mul,←quant_twist]; unfold W' Shaft.foldC; simp
 rw [show twist _ _= _ from (show twist (quantU U) F=f F from rfl), hk, ←hj, ←map_mul f]; unfold f; rw [twist_norm]; exact w K ht
-- dirty reluctance
variable {P B: Op I}(p:IsStarProjection P)
def Price (i:Shaft I)(R:ℝ):Prop:= ‖i.sell‖ ≤ R∧ ‖i.buy‖ ≤ R
def BlankT (C R:ℝ)(X:FC I):Prop:=∀ i:Shaft I, Price i R→ ‖i.glow X‖≤C
variable {C R:ℝ}
lemma BlankT.thetaF (U:UNI I){X:FC I}{W:Finset I}(p:Sector W false X)(h:BlankT C R X): BlankT C R (theta U X):=by
 intro i v; let V:= moveS (Shaft.mirrorC i) (star U); have hp:Price V R:=by
    unfold V moveS Shaft.mirrorC; exact ⟨by rw [twist_norm,norm_star]; exact v.2,by rw [twist_norm,norm_star]; exact v.1⟩ -- Price unfold
 rw [←glow_theta U V i (show twist U V.sell=_ from ?_) p]; swap; · nth_rw 1 [←star_star U]; exact twist_inv ..
 unfold theta; rw [twist_norm, Scroll.norm_cc]; exact h _ hp
namespace Loaves
variable {N:Side}
lemma dinnerC (L:List Wine) {S:Finset Cover}{k:Bool}(h:AreaW k S L)(R:ℝ)(z:ℂ)(p:2≤R):∃ C>0,∀ n:Side,∀ F:Fields n,BlankT C R (whisper z (tallyW L) (motet n L F)):=by
 obtain ⟨C,g,v⟩:=tipPower R L (by linarith) h
 let y:= tallyW L; refine ⟨1+‖z‖*(C+‖y‖),by positivity,fun n F i V=>?_⟩
 let W:=onC n F.1
 let X(l:Bite) := l.loc n
 have he(L): motet n L F=tickTea X W L:=by induction L with| nil=> rfl | cons a L ih=> unfold motet tickTea at *; rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,ih]; rfl
 unfold whisper; rw [Shaft.glow_sum,Shaft.glow_nil,Shaft.glow_free,Shaft.glow_sum,i.glow_free (-_),Shaft.glow_nil]; apply (norm_add_le ..).trans; rw [norm_smul,norm_one]; apply add_le_add_right; apply mul_le_mul_of_nonneg_left _ (norm_nonneg z); apply (norm_add_le ..).trans
 rw [he,shiftTea,norm_smul,norm_neg,norm_one,mul_one]; apply add_le_add_left; apply v; intro j u; apply (Flare.opy ..).trans; rw [show ‖X j‖=(1:ℝ) from (j.normP n),mul_one]; split; next w=> exact (norm_star ..).trans_le V.2
 exact V.1
lemma glory (k:ℕ): ∃ Z:ℝ,2≤Z ∧∀ n:Side,∀ (P:Op (Single n))(p:IsStarProjection P)(A:Pea (Single n)), Price (A.mint.foldC (Saber (B:=tickA n) p k)) Z:=by
 obtain ⟨C,g,F⟩:=off_age (n:=k); refine ⟨2*(1+C),by linarith,fun n P p A=>?_⟩; let V:=Saber (B:=tickA n) p k; unfold Price Shaft.foldC Saber; refine ⟨?_,?_⟩
 · exact (norm_mul_le ..).trans (mul_le_mul A.signed.1 ((norm_add_le ..).trans (by rw [norm_one,norm_star]; exact add_le_add_right (F n _ p) 1)) (norm_nonneg _) zero_le_two)
 exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left A.signed.2 (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right ((norm_sub_le ..).trans (by rw [norm_one,norm_star]; exact add_le_add_right (F n P p) 1)) zero_le_two).trans_eq (mul_comm ..)))
end Loaves
end YM.CF.Papyrus.Franc
