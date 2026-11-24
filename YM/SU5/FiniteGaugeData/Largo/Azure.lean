import YM.SU5.FiniteGaugeData.Largo.Cornish
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N X: Side} {σ C ξ K:ℝ}{M:Tulip.Male}{d r l D n:ℕ}{Q:Finset (Stereo N)}{b:Bool}
open Manifest Curtain
-- ℒ rank transports with error controlled for purchase via Ream.gains. `harmonies` = fields of both sorts approx & cost. Stages
structure Concert {Y:Type}[Fintype Y][DecidableEq Y] (N:Side)(P:Op (Mini N))(U A:Finset Cover)(S T W:Ruler (Mini N) Y)(g f x:ℝ): Prop where
 leftU : cutM (WalU N U) * S=S
 rightU : cutM (WalL N A) * T=T
 orth : Sᴴ*S=1
 asset : Sᴴ*W=1
 tier : cutM (scel N) * W=T
 budget : ‖T‖ ≤ g
 cost : ‖W‖ ≤ f
 hurdle : ‖P*W‖ ≤ x
variable (H:σ≥0)(h:0≤C)(P:∀ i:Stereo N,i∈Q→ Ream (shineF (stairF 4 (badge i) M)) σ C)
variable (e:l+D≤r) (q:Q≠∅) (z:boxSeats l D M N b Q n) (g:Hired Q)
local notation "L"=> LodgeP 0 N.val (r+d)
local notation "T"=> ReadT z
local notation "U"=> ReadU z
local notation "Y"=> Core Q n
local notation "V"=> cutM (scel N)
local notation "T₀"=> cutM (ruddy N)
local notation "J"=> cutM (Aeons N (r+d))
local notation "K₁"=> cutM (Aeons N r)
local notation "Ξ"=> reedsK M N
local notation "ι"=>FrameP Q
local notation "R"=> flatH M N
def Lyra (r d:ℕ):=cutM (Aeons N (r+d)) *(1+Ξ)*U
include e H h P g
lemma ferment (p:l+D+l+D<N.val) : Concert N (flatH M N) (Opera l D N.val b) (Opera l D N.val (!b)) (ReadT z) (ReadU z) (Lyra z r d) D ((1+C)*D) (Real.exp (-σ*d)*C*D):=by
 let B:= Lyra z r d; have he: V*U=U:=cutM_patch _ _ Finset.inter_subset_right U (dnSeat p z)
 have hf: K₁*U=U:= cutM_patch _ _ (terraceE.trans (aeons_mono _ _ e)) _ (dnSeat p z) -- remove
 have hb:J*U=U:=cutM_patch _ _ (aeons_mono _ _ (by omega)) _ hf; have hp:cutM (Aeons N r)*T=T:=cutM_patch _ _ (PavilionE.trans (aeons_mono _ _ e)) _ (upSeat p z)
 have hv:T₀*Ξ*U=Ξ*U:=by rw [reeds_s, Matrix.mul_assoc, he]
 have hw:T₀*T=T:=cutM_patch _ _ Finset.inter_subset_right _ (upSeat p z); have hz:Tᴴ*U=0:= coast T U hw (scel N) he disjoint_compl_right -- tune
 have hm:V*T₀=0:=cutP_com _ _ (subset_refl _)
 have hL:B=U+J*Ξ*U:=by unfold B Lyra; rw [mul_add,mul_one,Matrix.add_mul,hb]
 have hO:J*T=T:=cutM_patch _ _ (aeons_mono _ _ (by omega)) _ hp
 have hV: V*B=U := by rw [hL,Matrix.mul_add,he,← Matrix.mul_assoc _ (J*Ξ),←mul_assoc, (cutM_com ..).eq, Matrix.mul_assoc J V,Matrix.mul_assoc]; rw [Matrix.mul_assoc V Ξ, ←hv,←Matrix.mul_assoc V, ←Matrix.mul_assoc V,hm,zero_mul,Matrix.zero_mul,Matrix.mul_zero,add_zero]
 have hz' : Lyra z r d=J*(U+Ξ*U):=by unfold Lyra; rw [Matrix.mul_assoc,Matrix.add_mul,Matrix.one_mul]
 have hb':‖Ξ*U‖ ≤ C*D:=by
    nth_rw 1 [←booth z]; rw [←Matrix.mul_assoc]; exact (Matrix.l2_opNorm_mul ..).trans (mul_le_mul (tenure M H h P g) (read_pay p z) (norm_nonneg _) h)
 refine ⟨?_,?_,readIn p z,?_,hV,read_pay p z, hz' ▸ cutBudL.trans ((norm_add_le ..).trans ((add_le_add (read_pay p z) hb').trans_eq (by ring))),?_⟩
 · rw [←Wal_species.1]; exact upSeat p z
 · rw [←Wal_species.2]; exact dnSeat p z
 · change Tᴴ*B=_; rw [hL,Matrix.mul_add,hz,zero_add,←Matrix.mul_assoc, ←Matrix.mul_assoc, show Tᴴ*J=Tᴴ from (by nth_rw 1 [←cutM_adj (Aeons _ _)]; rw [←Matrix.conjTranspose_mul,hO]), boothLoan p z]
 let k:=cutM (Aeons N (r+d))ᶜ; have hw': (1+Ξ)*U=B+k*Ξ*U:=by
    rw [Matrix.add_mul,Matrix.one_mul,hL,add_assoc,←Matrix.add_mul,←add_mul,cutM_read',one_mul] -- uuid
 have ht: R*(B+k*Ξ*U)=0:=by rw [←hw', ←Matrix.mul_assoc]; nth_rw 1 [←he]; rw [←Matrix.mul_assoc, flatH_loan, Matrix.zero_mul]
 have hk: ‖k*Ξ*U‖ ≤ Real.exp (-σ*d)*C*D:=by
    nth_rw 1 [←booth z]; -- `k*Ξ* (ι*U)`
    rw [←Matrix.mul_assoc]; nth_rw 1 [←hf]; rw [←Matrix.mul_assoc]; exact (Matrix.l2_opNorm_mul ..).trans (mul_le_mul (vacuum M r d H h P g) (read_pay p z) (norm_nonneg _) (by positivity))
 change ‖R*B‖≤_; rw [Matrix.mul_add] at ht; rw [eq_neg_of_add_eq_zero_left ht,norm_neg]; exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((flatH_pro ..).norm_le _)).trans hk)
omit e H h P g
lemma wing : cutM (wal N (LodgeP 0 N.val (r+d)))*Lyra z r d= Lyra z r d:=by
 unfold Lyra; rw [Lodge_timeB]; simp_rw [←Matrix.mul_assoc,cutM_hold,inter_self]
namespace Concert
variable {l d u v w:ℕ}{Y' Y₀:Type} [DecidableEq Y'][Fintype Y'][DecidableEq Y₀][Fintype Y₀]{M':Tulip.Male}
variable {P:Op (Mini N)} {Lft Rgt Basis: Finset Cover}{S₃ S₂ S₁:Ruler (Mini N) Y'}{f q θ r τ ν:ℝ}
local notation "Γ"=> Concert N P Lft Rgt S₃ S₂ S₁ f q θ
variable (H₁:Concert N P Lft Rgt S₃ S₂ S₁ f q θ)
include H₁
lemma rightM (O:Ruler Y' Y₀)(h: Oᴴ*O=1) : Concert N P Lft Rgt (S₃*O) (S₂*O) (S₁*O) f q θ:=by
 let Lh:= H₁; refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw [←Matrix.mul_assoc,Lh.leftU];
 · rw [←Matrix.mul_assoc,Lh.rightU];
 · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ←Matrix.mul_assoc S₃ᴴ, Lh.orth, Matrix.one_mul,h]
 · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ←Matrix.mul_assoc S₃ᴴ, Lh.asset, Matrix.one_mul,h]
 · rw [←Matrix.mul_assoc,Lh.tier]
 · exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (grip_pay O h)).trans H₁.budget)
 · exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (grip_pay O h)).trans H₁.cost)
 rw [←Matrix.mul_assoc]; exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (grip_pay O h)).trans H₁.hurdle)
lemma bill' {f₁ q₁ θ₁:ℝ}(x₁:f≤f₁)(x₂:q≤q₁)(x₃:θ≤θ₁) : Concert N P Lft Rgt S₃ S₂ S₁ f₁ q₁ θ₁:= {H₁ with budget:=H₁.budget.trans x₁,cost:=H₁.cost.trans x₂,hurdle:=H₁.hurdle.trans x₃}
local notation "TΨ"=> Waltz.TauP N X Basis
lemma press' (A:Momentum→Op SpinIdx)(i:P=E₁ A N)(p:Waltz N Basis)(t:Waltz X Basis) (h:σ≥0)(z:ξ≥0) (d:ℕ) (δ:ℝ)(g: Ream A σ ξ) (ν:Finset Cover)(Qν:cutM (wal N ν)* S₁=S₁) (Pν:ν⊆ Basis) (tν:∀ v':Cover,v'∈ν→∀ i:Cover, i∈ box d→ v'-i∈Basis) (w: Real.exp (-σ*d)*ξ ≤ δ): ‖E₁ A X*(TΨ*S₁)‖ ≤ θ+2*δ*q:=by
 let Φ:= plateH A N d; let Ψ:=plateH A X d
 have ht: Ψ*TΨ*S₁=TΨ*Φ*S₁:=by rw [← Qν, ←Matrix.mul_assoc, p.plateHEq t Pν tν,←Matrix.mul_assoc]; -- tune occurrences
 let R':=E₁ A X; let YB:=p.tauBudget t; have hR: ‖R'-Ψ‖ ≤ δ:= (g.tollT X h d).trans w
 have hK:‖P-Φ‖ ≤ δ:=by rw [i]; exact (g.tollT N h d).trans w
 have ht': ‖TΨ*(P*S₁)‖ ≤ θ:= (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) YB).trans H₁.hurdle)
 have h0:0≤δ:= le_trans (norm_nonneg _) hR; have hq:‖TΨ*S₁‖≤q:= (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) YB).trans H₁.cost)
 have hp:‖TΨ*((P-Φ)* S₁)‖ ≤ δ*q:= (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) YB).trans ((Matrix.l2_opNorm_mul ..).trans (mul_le_mul hK H₁.cost (norm_nonneg _) h0)))
 have he:‖(R'-Ψ)*(TΨ* S₁)‖ ≤ δ*q:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul hR hq (norm_nonneg _) h0)
 rw [show E₁ A X * (TΨ*S₁)= (R'-Ψ)*(TΨ* S₁)+(TΨ*(P*S₁)- TΨ*((P-Φ)*S₁)) from (by rw [Matrix.sub_mul,Matrix.sub_mul,Matrix.mul_sub,←Matrix.mul_assoc Ψ,ht,Matrix.mul_assoc]; unfold R'; abel)]
 linarith only [show ‖(R'-Ψ)*(TΨ*S₁)+(TΨ*(P*S₁)-TΨ*((P-Φ)*S₁))‖ ≤ _ from (norm_add_le ..).trans (add_le_add he ((norm_sub_le ..).trans (add_le_add ht' hp)))] -- syntax placeholder inequality
lemma sailing (A:Momentum→Op SpinIdx)(i:P=E₁ A N)(p:Waltz N Basis)(t:Waltz X Basis) (l:Lft⊆ Basis)(r:Rgt⊆Basis) (h:σ≥0)(z:ξ≥0) (d:ℕ) (δ:ℝ)(g: Ream A σ ξ) (ν:Finset Cover)(Qν:cutM (wal N ν)* S₁=S₁) (Pν:ν⊆ Basis) (tν:∀ v':Cover,v'∈ν→∀ i:Cover, i∈ box d→ v'-i∈Basis) (w: Real.exp (-σ*d)*ξ ≤ δ): Concert X (E₁ A X) Lft Rgt (TΨ*S₃) (TΨ*S₂) (TΨ*S₁) f q (θ+2*δ*q):=by
 let YΒ:=p.tauBudget t; have hU: cutM (wal N Basis)* S₃=S₃:= cutM_patch _ _ (product_subset_product (image_mono _ l) (subset_univ _)) _ H₁.leftU
 have hr:S₃ᴴ*(cutM (wal N Basis))=S₃ᴴ:=by nth_rw 1 [←cutM_adj (wal N Basis)]; rw [←Matrix.conjTranspose_mul,hU];
 refine ⟨?_,?_,?_,?_,?_,?_,?_,H₁.press' A i p t h z d δ g ν Qν Pν tν w⟩
 · rw [←Matrix.mul_assoc, p.tauCut t l, Matrix.mul_assoc,H₁.leftU] -- tune powers
 · rw [←Matrix.mul_assoc,p.tauCut t r,Matrix.mul_assoc,H₁.rightU]
 · rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc TΨᴴ,p.tauIs t,←Matrix.mul_assoc,hr,H₁.orth]
 · rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc TΨᴴ,p.tauIs t,←Matrix.mul_assoc,hr,H₁.asset]
 · rw [←Matrix.mul_assoc]; have hv (N:Side):scel N=(univ ×ˢ plusHalfᶜ):=by ext; simp [scel,ruddy]
   rw [hv,Waltz.tauSpin .., Matrix.mul_assoc,←hv,H₁.tier]
 · exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) YΒ).trans H₁.budget)
 exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) YΒ).trans H₁.cost)
omit H₁
lemma hull' {U₁:Finset Cover} (p:Waltz N Basis)(t:Waltz X Basis)(g:U₁⊆Basis)(H:cutM (wal N U₁)*S₁=S₁): cutM (wal X U₁)*(TΨ*S₁)=TΨ*S₁:=by rw [←Matrix.mul_assoc,p.tauCut t g,Matrix.mul_assoc,H]
end Concert
end YM.CF.Window.Largo
