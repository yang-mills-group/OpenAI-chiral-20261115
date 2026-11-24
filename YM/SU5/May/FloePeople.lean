import YM.SU5.May.FloeCoins
import YM.SU5.Reconstruction.Hygrometry.Morph
import YM.SU5.Lamour.Glaze
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
-- rank formula etc
variable {N F:Side} {j:ℕ}(u:1≤j) (w:Even N.val)(M:Jill.Male) (r:ℝ) (p:0≤ r)
include u w in
lemma ledger_as_lake: ledger N j M= Dofu N (lakeP N j M) := by
 have he : Hygrometry.ascender N j M=Dofu N (lakeK N j M):=by unfold ascender; apply congrArg (Dofu N); funext i; rw [too_u]; rfl
 exact (congrArg (laneP (tickA N) 1) he).trans (Lamour.pitch M u w).2.symm
variable (x y:Cover)(z l:Slot){i k:SpinIdx} (hi:i∈payroll true)(hk:k∈payroll false)
include w
lemma bore_cash (b:Slot): Onyx.bore ((too N).u b) r (x-y) (trackF (too N) (lakeP N j M) b) i k=delta N j M r (x-y) i k:=by
 change Onyx.bore (zeroF N) _ _ _ _ _ = _; unfold bore delta coins liv; rw [Matrix.smul_apply]; simp_rw [Matrix.sum_apply,Matrix.smul_apply]; simp_rw [Lamour.align_b M w]; change ((↑(r^3/(N.val:ℝ)^4:ℝ):ℂ)*_) = _; push_cast; simp only [charK,show ∀ i:Site N,glen (zeroF N) i=pm i from fun i=> add_zero ..]; rfl
abbrev ice (j:ℕ)(N:Side)(M:Jill.Male)(r:ℝ)(x y:Cover)(s t: Personality):=rankG (ledger N j M) (player N x r s) (player N y r t)
include p u in
lemma basisPrice : ice j N M r x y (pureV true z i hi) (pureV false l k hk)=if z=l then delta N j M r (x-y) i k else 0:=by
 unfold ice; rw [player_pure,player_pure, Emu.cat _ _ _ _ _ _ _ _ p]; rw [ down_here hi,down_here hk]; simp only [Bool.true_eq_false,ite_false,ite_true, ledger_as_lake u w M]; unfold hopF; rw [mist (too N),bore_cash w]
omit w
lemma downPrice (s t: Personality)(h:s.down=true)(e:t.down=false) : ice j N M r x y s t= inner ℂ (pitch N x r s.color s.voice) (acts (ledger N j M) (pitch N y r t.color t.voice)):=by simp [ice, rankG, player,h,e]
include w p u
lemma personPrice (s t:Personality)(h:s.down=true)(e:t.down=false): ice j N M r x y s t=
     ∑ i∈ payroll true,∑ k∈payroll false,star (s.voice i) * t.voice k * (if s.color=t.color then delta N j M r (x-y) i k else 0):=by
 rw [downPrice M r x y s t h e,pitch_sum s,sum_inner,h]; apply sum_congr rfl; intro i hi; rw [pitch_sum t,e,map_sum,inner_sum]; apply sum_congr rfl; intro k hk; rw [map_smul,inner_smul_left,inner_smul_right, ←basisPrice u w M r p x y _ _ hi hk]; rw [downPrice M r x y (pureV true _ _ hi) (pureV false _ _ hk) rfl rfl]; exact (mul_assoc ..).symm -- orientation check
omit p w u
variable (G:Ratio N F)(H:Odd G.count.val)(a:Even N.val)(b:Even F.val)
local notation "M₀"=> hail G.count H
local notation "L"=>G.count
local notation "Z"=> Trace j L
local notation "D" x:max a:max=> point L x (traces L j a)
include a b H u
private lemma person_peak(s t:Personality)(h:s.down=true)(e:t.down=false): ice j N M₀ 1 x y s t= expected (fun c:Z=> expected fun d:Z=> ice j F white G.count.val (D x c) (D y d) s t) := by
 simp_rw [personPrice u a M₀ _ zero_le_one x y s t h e,personPrice u b white _ (show 0≤(G.count.val:ℝ) by positivity) _ _ s t h e,expected_sum,expected_mul]; refine sum_congr rfl fun i hi=>?_ ; apply sum_congr rfl; intro k hk; by_cases g:s.color=t.color <;> simp only [if_pos,if_neg,g]
 · exact congrArg _ (rocking G H j x y i k)
 simp
lemma person_coarse(s t:Personality) : ice j N M₀ 1 x y s t= expected (fun c:Z=> expected fun d:Z=> ice j F white G.count.val (D x c) (D y d) s t):=by
 by_cases k:s.down=t.down; · simp [ice,rankG,k,player]; -- synth Nonempty Flap
 cases h:s.down
 · have e:t.down=true:=by cases w:t.down <;> simp_all
   rw [show ice j N M₀ 1 x y s t=_ from rank_flip _ _ (player N y 1 t)]; change -ice j N M₀ 1 y x t s= _; simp_rw [show ∀ v z R, ice j F white R v z s t= -ice j F white R z v t s from fun v z R=>rank_flip .., expected_neg]; rw [habit,person_peak u y x G H a b t s e h] -- tune
 have e:t.down=false:=by cases w:t.down <;>simp_all
 exact person_peak u x y G H a b s t h e
namespace Hearth
open Buffered.Lifted
-- bound all these lattice actors robust (R=1). tangent schedule anywhere. Pierce aperture
noncomputable def lump(s:Personality):ℝ:=∑ i:SpinIdx, ‖s.voice i‖
omit a b u H
lemma lump_nonneg(s:Personality):0 ≤ lump s:= Finset.sum_nonneg fun _ _=> norm_nonneg _
variable (C:ℝ)(f:Buffered.Glaze.Billow C (Lamour.lake N j M))
lemma heave_p(k:Slot)(i:SpinIdx) : ‖basisC N x i k‖≤1:=by rw [basisC,norm_smul,Buffered.Lifted.winding, fee_norm]; simp --Buffered.Lifted.winding,basisC, fee_norm] -- tune
lemma sphere (s:Personality) : ‖pitch N x 1 s.color s.voice‖≤ lump s:=by
 unfold pitch Hygrometry.cantor; simp only [Emu.gain,one_pow,Real.sqrt_one,Complex.ofReal_one,one_smul]; exact le_trans (norm_sum_le ..) (sum_le_sum fun i _=> by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (heave_p ..))
include f u w
private lemma fare_s (s:Personality): ‖acts (ledger N j M) (pitch N x 1 s.color s.voice)‖≤ C* lump s:=by
 unfold pitch Hygrometry.cantor; rw [map_smul,map_sum]; simp_rw [map_smul]; simp only [Emu.gain,one_pow,Real.sqrt_one,Complex.ofReal_one,one_smul]; unfold lump; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw [basisC,map_smul,norm_smul,norm_smul,show ‖Buffered.Lifted.winding _ _‖=(1:ℝ) from fee_norm _,one_mul,mul_comm C]; exact mul_le_mul_of_nonneg_left (ledger_as_lake u w M ▸ (f _).1) (norm_nonneg _)
lemma ice_pres (s t:Personality): ‖ice j N M 1 x y s t‖ ≤ C*lump s*lump t:=by
 have hp:0≤C:=(norm_nonneg _).trans (f (index N x 0 s.color)).1
 by_cases h:s.down=t.down
 · simp only [ice,rankG, player,h,if_true,norm_zero]; exact mul_nonneg (mul_nonneg hp (lump_nonneg _)) (lump_nonneg _)
 cases x':s.down
 · cases y':t.down; exact (h (x'.trans y'.symm)).elim
   rw [show ice j N M 1 x y s t= -ice j N M 1 y x t s from rank_flip ..,norm_neg,downPrice M 1 y x t s y' x']; exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans ((mul_le_mul (sphere _ t) (fare_s u w M x _ f s) (norm_nonneg _) (lump_nonneg _)).trans_eq (mul_comm ..)) -- args
 cases y':t.down; swap; exact (h (x'.trans y'.symm)).elim
 rw [downPrice M 1 x y s t x' y']; exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans ((mul_le_mul (sphere _ s) (fare_s u w M y _ f t) (norm_nonneg _) (lump_nonneg _)).trans_eq (by ring))
omit f w
lemma reimburse : ∃ C:ℝ,0<C ∧ ∀ N:Side,Even N.val→∀ M:Jill.Male,∀ (x y:Cover)(s t:Personality), ‖ice j N M 1 x y s t‖ ≤ C*lump s*lump t:=by obtain ⟨C,p,h⟩:=Lamour.lake_local u; exact ⟨C,p,fun _ x M t l s u'=>ice_pres u x M _ _ _ (h x M) _ _⟩
end Hearth
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.person_coarse
