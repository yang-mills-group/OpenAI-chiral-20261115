import YM.CF.Tale.Nook
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open Heir AnalyticBridge.SectorAffine.Offset AnalyticBridge.VerifiedReset
open Pressure Tube Siete
variable {c f:Side} 
variable{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{x C M A a η δ α γ Ω:ℝ}{J:S.Choices}{n m:ℕ}
local notation "G5"=> SU.group
abbrev lumeK := SU.group.Color -- tune
open StressFlux
variable (k:ℝ)(j t:ℕ)(h:0<k)(pM:4≤j)(v:4≤t)(P:Flight j t)(w:f.val=c.val*P.L.val)
local notation "L"=> (P.L)
local notation "G_"=> (deckY j t P w)
-- use receipt quantified over any trajectory. constants projection.M
structure Thy (j t:ℕ)(k A C:ℝ):Prop where
 cube:∀ (c:Side)(o:Site c)(K:PlaqAxes)(v:townX c),‖v‖≤1→Through 2 (fun x:townX c=> petals (increment 1 x) o K) v C
 need(P:Flight j t)(c f:Side)(w:f.val=c.val * P.L.val)(o:Site c)(Q K:PlaqAxes)(x:SU.group.Color) (r m:ℕ)(q:m ≤ r)(hk:2*m<c.val)(hL:5≤P.L.val): ‖curl_P K ((deckY j t P w).embed o) (trade_u k j t P w (upper_F r Q x o))-((P.L.val:ℝ)⁻¹)^2 • (if Q=K then x else 0)‖≤ C*‖x‖*((P.L.val:ℝ)⁻¹)^2 * Real.exp (-A*m)
include h pM v in
lemma faith_S:∃ A C:ℝ,0<A∧1≤C∧ Thy j t k A C:=by
 obtain ⟨C,a,h',ha,hp⟩:=need_K k j t h pM v; obtain ⟨B,p,H⟩:=ν_p
 refine ⟨a,max B C,ha,p.trans (le_max_left ..),⟨fun c o K v p=>(H c o K v p).mono (le_max_left ..),fun P c f w o U V Q x y ht hL hs=> ?_⟩⟩; apply (hp P c f w o U V Q x y ht hL hs).trans; gcongr; exact le_max_right ..
variable (o:Site c)(p:BudgetPoint)(r l:ℕ)(q:l≤ r)(he:2*l<c.val)(hL:5≤ P.L.val)
local notation "θ"=> (p.threshold)
local notation "Π"=> (((P.L.val:ℝ)⁻¹)^2)
local notation "Xq"=> (deckY j t P w).embed o
abbrev trade_L : townX c →L[ℝ] townX f:= Heir.shaped (G:=SU.group) (installed (deckY j t P w) (Lt k j t P)) ∘L curt r o
local notation "V"=> (trade_L k j t P w o r) -- order
variable (s b:PlaqAxes)
variable (TH:Thy j t k a C)
local notation "Aη"=> (θ • AnalyticBridge.VerifiedReset.spike SU.group)
local notation "Zt"=> clipT p o
local notation "Qτ"=> (1+ θ)
include q he hL TH
lemma cue_v : let X:=V; let f:=fun x:townX f=>petals (increment 1 x) Xq b; ‖(fderiv ℝ f 0) (X (clipT p o s))- Π • (if s=b then Aη else 0)‖ ≤ C*θ*Π*Real.exp (-a*l):=by
 intro U f; have ht:= TH.need P _ _ w o s b Aη r l q he hL
 rw [ring_l b _ _ p]; simp_rw [norm_smul,spike_norm Thera.yet_one,mul_one,Real.norm_of_nonneg p.threshold_pos.le] at ht; exact ht
variable {X:townX c→ townX f}(hx: Guide (townX c) (p.dirBound o) 0 X m γ)(hg:Guide (townX c) (p.dirBound o) 0 (X- ⇑(trade_L k j t P w o r)) m δ)(h2: δ ≤1)(hM:2 ≤ m) -- tune
include hx hg hM
lemma train_D : ‖X 0‖≤δ ∧ ‖fderiv ℝ X 0 (Zt s)- V (Zt s)‖≤ δ∧ ‖fderiv ℝ X 0 (Zt s)‖ ≤γ∧ ‖iteratedFDeriv ℝ 2 X 0 ![Zt s,Zt b]‖ ≤ δ:=by
 let x:= Zt s; let u:= V; have he:= p.order_ge; have h₁:ContDiffAt ℝ 2 X 0:=hx.1.of_le (Nat.cast_le.mpr hM); have hT : DifferentiableAt ℝ X 0:= h₁.differentiableAt (by decide)
 have hf:ContDiffAt ℝ ((↑(2:ℕ)):WithTop ℕ∞) u 0:= u.contDiff.contDiffAt; have hv':‖(X-(⇑u)) 0‖ ≤ δ:=hg.size -- tune ascii
 change _ ∧ ‖fderiv ℝ X 0 x-u x‖≤ δ∧‖fderiv ℝ X 0 x‖≤ γ∧ _
 refine ⟨?_,?_,?_,?_⟩
 · simpa only [Pi.sub_apply,map_zero,sub_zero] using hv'
 · let A':=hg.2 1 (by omega) ![x] (fun i=>by fin_cases i; exact fore_l p o s) -- order p o tune
   rw [iteratedFDeriv_one_apply,fderiv_sub hT u.differentiableAt,u.fderiv] at A'; exact A'
 · have H:=hx.2 1 (by omega) ![x] (fun i=>by fin_cases i; exact fore_l p o s); rw [iteratedFDeriv_one_apply] at H; exact H
 have hp:=hg.2 2 hM ![Zt s,Zt b] (fun i=>by fin_cases i; exact fore_l p o s; exact fore_l p o b) -- tune finCases
 rw [iteratedFDeriv_sub_apply h₁ hf, sterile (trade_L k j t P w o r) 0 (show 1 < (2:ℕ) from (by norm_num)),sub_zero] at hp; exact hp
local notation "fy" Q:max=> (fun z:townX f=> petals (increment 1 z) Xq Q) -- hygiene Q s
abbrev lens_k (M:Side) (p:BudgetPoint)(s b:PlaqAxes):group.Color:= ((M.val:ℝ)⁻¹)^2 • (if s=b then p.threshold • AnalyticBridge.VerifiedReset.spike SU.group else 0)
local notation "Λ"=>lens_k L p
local notation "Qt"=> (C*δ*γ+C*δ+C*θ*Π*Real.exp (-a*l))
include h2
lemma leo_P (K:PlaqAxes): let f:= (fy K)∘X; ‖f 0‖≤C*δ ∧ ‖fderiv ℝ f 0 (Zt s)-lens_k P.L p s K‖ ≤ Qt ∧ ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) f 0 ∧‖iteratedFDeriv ℝ 2 f 0 ![Zt s,Zt b]‖ ≤ C*(γ^2+δ):=by
 intro f' -- Shadow f.Aug
 obtain ⟨u,v,hQ,hV⟩:=train_D k j t P w o p r l q he hL s b TH hx hg hM -- ABI check hL h2 omit
 have hp:=train_D k j t P w o p r l q he hL b s TH hx hg hM; let g:= (fy K)
 have ht:ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) X 0:= hx.1.of_le (Nat.cast_le.mpr hM)
 obtain ⟨v0,v1,v2⟩:=payload g X (Zt s) (Zt b) (TH.cube f Xq K) (u.trans h2) (by unfold g; simp) ht u hQ hp.2.2.1 hV (V (Zt s)) δ v
 refine ⟨v0,(norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ g 0 (V (Zt s))) _).trans ((add_le_add v1 (cue_v k j t P w o p r l q he hL s K TH))), ((TH.cube f Xq K _ (u.trans h2)).smooth).comp (f:=X) 0 ht,v2⟩
end YM.CF.Tale
