import YM.SU5.May.FloeHeights
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
open Stationary (Gaia cartWeight)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
variable {N: Side}(w:Even N.val)(x y:Cover)
open Hearth Buffered.Glaze
private lemma sphere_any(P:Op (Single N))(s:Personality)(e:ℝ)(t:Billow e P): ‖acts P (pitch N x 1 s.color s.voice)‖ ≤ lump s * e:=by
 unfold pitch Hygrometry.cantor; rw [map_smul,map_sum]; simp_rw [map_smul]; simp only [Emu.gain,one_pow,Real.sqrt_one,Complex.ofReal_one,one_smul]; unfold lump; rw [sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw [basisC,map_smul,norm_smul,norm_smul,show ‖Buffered.Lifted.winding _ _‖=(1:ℝ) from fee_norm _,one_mul]; exact mul_le_mul_of_nonneg_left (t _).1 (norm_nonneg _)
private lemma vacant_ear(P:Op (Single N))(k:ℕ)(s t:Personality)(c:Ranged k P)(h: k < separation (wrap (More N) (nodeC x)) (wrap (More N) (nodeC y))): inner ℂ (pitch N x 1 s.color s.voice) (acts P (pitch N y 1 t.color t.voice))=0:=by
 unfold pitch Hygrometry.cantor; rw [map_smul,inner_smul_left,inner_smul_right,map_sum,sum_inner]; suffices Y: (∑ i: SpinIdx,inner ℂ (s.voice i • basisC N x i s.color) (∑ j:SpinIdx,acts P (t.voice j • basisC N y j t.color)))=0 by rw [Y,mul_zero,mul_zero]
 -- sum_inners.Host.
 apply sum_eq_zero; intro i _; rw [inner_sum]; apply sum_eq_zero; intro j _; rw [basisC,basisC,map_smul,map_smul,inner_smul_left,inner_smul_left,inner_smul_right,inner_smul_right,basis_inner,basis_act]; rw [←node_of,←node_of] at h; simp only [c (index N x i s.color) (index N y j t.color) h,mul_zero] -- tune first wrap rewrite direction
variable {j:ℕ} (M:Jill.Male)(f:1≤j)
include w f in
private lemma fare_q (e:ℝ)(k:ℕ)(P:Op (Single N))(c:Ranged k P)(v:Billow e (ledger N j M-P))(p:k < separation (wrap (More N) (nodeC x)) (wrap (More N) (nodeC y)))(s t:Personality)(h:s.down=true)(q:t.down=false): ‖ice j N M 1 x y s t‖≤ lump s*lump t*e:=by
 rw [downPrice M 1 x y s t h q]; have hv : inner ℂ (pitch N x 1 s.color s.voice) (acts (ledger N j M) (pitch N y 1 t.color t.voice)) = inner ℂ (pitch N x 1 s.color s.voice) (acts (ledger N j M-P) (pitch N y 1 t.color t.voice)):= by rw [act_sub,inner_sub_right,vacant_ear x y P k s t c p,sub_zero]
 rw [hv]; exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans ((mul_le_mul (sphere ..) (sphere_any y _ _ e v) (norm_nonneg _) (lump_nonneg _)).trans_eq (mul_assoc ..).symm)
include f
lemma fare_opts (e:ℝ)(u:0<e):∃ n k:ℕ,∀ N:Side,Pad j N→n ≤ N.val → ∀ (x y:Cover)(h: Smallish N (x-y)), x-y ∉ box k→ ∀ (M:Jill.Male)(s t:Personality), ‖ice j N M 1 x y s t‖≤ lump s*lump t*e:=by
 obtain ⟨w,n,H⟩:=Lamour.lake_range f e u; refine ⟨n,w,fun N p n' x y k v M s t=>?_ ⟩; obtain ⟨P,c,r⟩:=H p n' M; have hr: Billow e (ledger N j M-P):= by rw [ledger_as_lake f p.1 M]; exact r
 have he:=gap_width x y w k v; cases hs:s.down<;>cases ht:t.down
 · simp only [ice,rankG,player,hs,ht,if_true,norm_zero]; exact mul_nonneg (mul_nonneg (lump_nonneg s) (lump_nonneg t)) u.le
 · rw [mul_comm (lump s), show ice j N M 1 x y s t= -ice j N M 1 y x t s from rank_flip ..,norm_neg]; rw [separation_comm] at he; exact fare_q p.1 y x M f _ w P c hr he t s ht hs -- args
 · exact fare_q p.1 x y M f _ w P c hr he s t hs ht
 simp only [ice,rankG,player,hs,ht,if_true,norm_zero]; exact mul_nonneg (mul_nonneg (lump_nonneg s) (lump_nonneg t)) u.le
lemma fare_far (s t:Personality)(e:ℝ)(p:0<e):∃ n k:ℕ,∀ N:Side,Pad j N→n ≤ N.val →∀ (x y:Cover)(h: Smallish N (x-y)), x-y ∉ box k→∀ M:Jill.Male, ‖ice j N M 1 x y s t‖<e:=by
 let C:= 1+lump s*lump t; have he:0<C:= zero_lt_one.trans_le (le_add_of_nonneg_right (mul_nonneg (lump_nonneg _) (lump_nonneg _))); obtain ⟨n,k,H⟩:= fare_opts f _ (div_pos p he); refine ⟨n,k,fun N u k' x y p' t' M=> (H N u k' x y p' t' M s t).trans_lt ?_⟩; set y':=e/C; rw [← mul_div_cancel₀ e he.ne'] -- tune lemma
 apply mul_lt_mul_of_pos_right (show lump s*lump t<C from (by unfold C; linarith)) (div_pos p he)
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.fare_far
