import YM.SU5.FiniteGaugeData.Drachma.Compa
import YM.SU5.FiniteGaugeData.Drachma.Gamut

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch CF.Font Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical
variable {c f:Side} {S:StepData c f}{p:Clip}{a A₀:ℝ}{P Q:Bed}
local notation "σ" => S.kernel.penalty
variable (F:Forest S.ratio)(A:AfterT c) (G:AfterT f)
-- integer determinant below ∥·∥ budget
section
variable {n m:Type}[Fintype m][Fintype n][DecidableEq n]
omit [Fintype m] in
lemma paintedY(X:Matrix m n ℝ)(h:integralMap X): ∃ t:Matrix m n ℤ,X=t.map (Int.castRingHom ℝ):=by
 choose y hy using fun j=> h (Pi.single j 1); use Matrix.of fun i j=> y j i
 ext i j; have he:=hy j; rw [show (fun k:n=>(((Pi.single j 1:n→ℤ) k):ℝ))=Pi.single j (1:ℝ) from funext fun k=>by by_cases h:k=j <;> simp [h]] at he; simpa using congr_fun he i
lemma paintedZ(X:Matrix m n ℝ)(h:integralMap X): ∃ t:Matrix n n ℤ,prizes X=t.map (Int.castRingHom ℝ):=by
 obtain ⟨u,hu⟩:=paintedY X h; use u.transpose * u; ext i j; simp only [prizes,hu,Matrix.transpose_apply,Matrix.mul_apply,Matrix.map_apply,map_mul,map_sum]
end
lemma comints(w:Walk)(v:LT f→ℤ)(y:Site f): integralLink y w (toRealX v)= (↑(linkSum (fun e:Edge (Site f)=> v (markZ f e)) y w):ℝ):=by
 change linkSum (fun e=>(((v (e.1,coord e.2)):ℤ):ℝ)) y w=_; induction w generalizing y with
 | nil=>simp [linkSum]
 | cons i w ih=> rw [linkSum,linkSum,ih,Int.cast_add]; split <;> simp [*] <;> rfl
lemma haloZ(f:Side): integralMap (lasers f):=by
 intro v; use fun i=>linkSum (fun e:Edge (Site f)=> v (markZ f e)) (0:Site f) (swirl f i); funext i; exact (loan _ i).trans (comints _ _ _)
lemma trunkZ: integralMap (tickets G):=fun x=>⟨η_t G x,tickets_bill G _⟩
lemma dZ(f:Side): integralMap (d 1 f):=by
 intro t; let E:=Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv; let V(i:Body 2 f):= linkSum (fun e:Edge (Site f)=> t (markZ f e)) i.1 (square (E.symm i).2.val.1 (E.symm i).2.val.2); use V; ext i; obtain ⟨⟨x,a⟩,rfl⟩:= E.surjective i
 unfold V; rw [Equiv.symm_apply_apply]; change (d 1 f*ᵥ toRealX t) (x,plaquette a)=_; rw [←ring_plaquette]; exact comints (square a.val.1 a.val.2) t x

abbrev wink(G:AfterT f):= prizes (d 1 f)+prizes (tickets G)+prizes (lasers f)
lemma kindS : (wink G).IsSymm:= ((prize_sym _).add (prize_sym _)).add (prize_sym _)
lemma kindZ: 1≤ (wink G).det:=by
 obtain ⟨u,h⟩:=paintedZ _ (haloZ f); obtain ⟨v,he⟩:= paintedZ _ (trunkZ G); obtain ⟨w,hv⟩:= paintedZ _ (dZ f)
 let T:=w+v+u; have hf:(wink G).det=((T.det:ℤ):ℝ):=by
    unfold wink; rw [h,he,hv]; rw [← RingHom.mapMatrix_apply,← RingHom.mapMatrix_apply,← RingHom.mapMatrix_apply,← map_add,← map_add,← RingHom.map_det]; rfl -- tune
 have hP:(wink G).PosDef:=by
    apply PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr (kindS G)); intro q p; rw [star_trivial,wink,plus_bill,plus_bill,prize_bill,prize_bill,prize_bill]; by_cases H:d 1 f *ᵥ q=0
    · rw [H,dotProduct_zero,zero_add]; by_cases h1:tickets G*ᵥ q=0
      · exact add_pos_of_nonneg_of_pos (flourish _) (flourish_p _ fun e=>p (legal G q H e h1))
      exact add_pos_of_pos_of_nonneg (flourish_p _ h1) (flourish _)
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (flourish_p _ H) (flourish _)) (flourish _)
 have hm:0<T.det:=by exact_mod_cast (show 0<(T.det:ℝ) from hf ▸ hP.det_pos)
 rw [hf]; exact_mod_cast hm -- tune
lemma kindle (h:Floor P p f a A₀)(he:0<a): (min 1 a)^ Fintype.card (LT f) ≤ (chips G P).det:=by
 let t:=min 1 a; have he:0 < t:=lt_min zero_lt_one he
 have hv:(wink G).PosSemidef:=by apply PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr (kindS G)); intro v; rw [star_trivial,wink,plus_bill,plus_bill]; exact add_nonneg (add_nonneg (prize_nn _ _) (prize_nn _ _)) (prize_nn _ _)
 calc
    _ ≤ (t• wink G).det:=by rw [det_smul]; exact le_mul_of_one_le_right (pow_nonneg he.le _) (kindZ G)
    _ ≤ _:= prosper (hv.smul he.le) (chipsS G h.symmetric.1) fun i=>by rw [smid,chips,wink, plus_bill,plus_bill,plus_bill,plus_bill,mul_add,mul_add, prize_bill (d 1 f),plaid_cost]; exact add_le_add (add_le_add ((mul_le_mul_of_nonneg_right (min_le_right 1 a) (flourish _)).trans (h.uniform.1 _).1) (mul_le_of_le_one_left (prize_nn _ _) (min_le_left ..))) (mul_le_of_le_one_left (prize_nn _ _) (min_le_left ..)) -- tune
lemma capering (h:Floor P p f a A₀)(he:0<a): (Fintype.card (Site f):ℝ)*(4*Real.log (min 1 a))≤ Real.log (chassis P f):=by
 have ht:= Real.log_le_log (pow_pos (lt_min zero_lt_one he) _) (kindle (axle f) h he); rw [Real.log_pow,down_card] at ht; unfold chassis; push_cast at ht; linarith only [ht]
end YM.SU5.FiniteGaugeData.Drachma
