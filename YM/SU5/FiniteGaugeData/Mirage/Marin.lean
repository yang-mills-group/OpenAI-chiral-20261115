import YM.SU5.FiniteGaugeData.Mirage.Sheet
import YM.SU5.FiniteGaugeData.Brique.Vesta
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
-- buying knots, print projection independently of shape. same cost for any phase and spotlight.
open SU Scree Cascade Dial
local notation "Υ"=> Tset N
structure Marble {N:Side}(A: Op (Single N))(T: Support (More N))(n:ℕ) (B:FC (Single N))(δ:ℝ): Prop where
  prize: ∃ P: Op (Single N), Cellar (modesIn N T) P ∧ IsStarProjection P ∧ P.trace=n ∧ TapFn false P (acts (star B) (mateK N)) ∧ ‖P*A‖ ≤ δ
variable {X:Type*}[LinearOrder X][Fintype X][Nonempty X] (x: Finset X) (Q:Op X)
lemma quantifier (A:Finset X)(t:A⊆x) : starMark0 x Q A= quant (1+cutM xᶜ*Q*cutM A):=by
 apply quant_unique; · clear t; induction A using induction_on_min with
                             | empty => simp [starMark0,Scree.column]
                             | insert i s z ih=>
                                let U:=starMark0 x Q s; rw [starMark0, Scree.column,sort_insert _ (fun i h=> (z i h).le) (fun p=>lt_irrefl _ (z i p)),List.map_cons,List.prod_cons,act_mul]; change acts (starBoost x Q i) (acts (starMark0 x Q s) (vacuum X))=_; rw [ih]; unfold starBoost; rw [act_add,act_one,act_mul,←remove_take,vacuum_take,map_zero,add_zero]
 intro i; rw [act_add,act_one, starM_weave x A Q t, create_put] -- use sugar
section
local notation "o"=> Ruler (Single N) (Fin r)
variable {F1 F2 G1 G2 W1 W2: Ruler (Mini N) (Fin r)} -- F= ReadT (upper); G=lower. W interpolated full wave
variable {M:Tulip.Male}{U1 U2 L1 L2 : Finset Cover}{θ:Tulip.Male}{c1 c2 t:ℝ}
-- run: Upper maps. Y1 color ALL, Y2 color some/h single. α→β on U1, β→α on U2. L1 and L2 locations are for G1 and G2 respectively, opposite side.
variable (p: Concert N (flatH M N) U1 L1 F1 G1 W1 c1 c2 t)
variable (q: Concert N (flatH M N) U2 L2 F2 G2 W2 c1 c2 t) -- generalized later costs?
variable (α β: Fin 3) (v:α≠β)
variable (Y1 Y2: Finset Sheet) (u:Sheet) (u1:u∈Y1)(u2:u∈Y2) (z:ℂ)
local notation "Ψ₁"=> Channel N (αslot u α)
local notation "Ψ₂"=> Channel N (αslot u β)
abbrev inkL (F G:Ruler (Mini N) (Fin r)) (x y:Fin 3)(V: Finset Sheet)(c:ℂ):= star c • cibe (G*Fᴴ) x y V
private abbrev JetL(z:ℂ):= (Channel N (αslot u α))*W1 + star z • ((Channel N (αslot u β))* W2)
local notation "Ζ"=> Ψ₁ * W1 + star z • (Ψ₂*W2)
local notation "Γ₁"=> inkL F1 G2 α β Y1 z
local notation "Γ₂"=> inkL F2 G1 β α Y2 (star z)
include p q v
lemma assetJet : (Ψ₁*F1)ᴴ * (Ψ₁*W1+star z • (Ψ₂*W2))=1:=by
 rw [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.mul_smul]; let x:= exhibit_n α β u v; rw [Matrix.mul_assoc F1ᴴ, ←Matrix.mul_assoc Ψ₁ᴴ Ψ₁, Channelθ, Matrix.one_mul, p.asset, Matrix.mul_assoc F1ᴴ, ←Matrix.mul_assoc Ψ₁ᴴ Ψ₂, Channel_z _ _ x, Matrix.zero_mul,Matrix.mul_zero,smul_zero,add_zero]
local notation "P₀"=> cutM (Tset N)
local notation "P'"=> cutM (Tset N)ᶜ
local notation "M₁"=> piggy (WalU N U1) Y1 α
local notation "M₂"=> piggy (WalU N U2) Y2 β
lemma valJ (z':ℂ) : let R:=inkL F1 G2 α β Y1 z'; R*cutM (piggy (WalU N U1) Y1 α)=R ∧ cutM (piggy (WalL N L2) Y1 β)*R=R:=by
 intro J; refine ⟨?_,?_⟩; · unfold J inkL; rw [Matrix.smul_mul, pig_cutT]; rw [Matrix.mul_assoc, show F1ᴴ*cutM (WalU N U1)=F1ᴴ from (by nth_rw 1 [←cutM_adj (WalU N U1)]; rw [←Matrix.conjTranspose_mul,p.leftU])]; -- tune
 unfold J inkL; rw [Matrix.mul_smul,pig_cutV]; rw [←Matrix.mul_assoc, q.rightU] -- there may only one goal
lemma uneSeul : inkL F1 G2 α β Y1 z * cutM (Tset N)=inkL F1 G2 α β Y1 z ∧ cutM (Tset N)ᶜ* inkL F1 G2 α β Y1 z= inkL F1 G2 α β Y1 z:=by
 obtain ⟨h,h1⟩:= (show Γ₁ * cutM (piggy (WalU N U1) Y1 α)= Γ₁ ∧ _ from valJ p q α β v Y1 z)
 constructor; · nth_rw 1 [←h]; rw [mul_assoc,cut_meet,inter_eq_left.mpr (pigU α Y1),h]
 exact cutM_patch _ _ (pigL β Y1) _ h1
include u1 u2
lemma rightSeat (lamb':star z*z=1) : (1+Γ₂)*(1+Γ₁)*P₀*(Ζ)=(Ζ):=by
 obtain ⟨t,t₁⟩:= uneSeul p q α β v Y1 z; obtain ⟨t',t₂⟩:= uneSeul q p β α v.symm Y2 (star z)
 let u₀:= Exhibit Y1 α β; let U:= Ψ₁*W1; let V:=Ψ₂*W2; let A:= (Γ₁); let B:= (Γ₂)
 have he: V= Ψ₂*W2:= rfl
 have hx: A*U= star z • (Ψ₂ * G2):=by
    unfold A U inkL; rw [Matrix.smul_mul, ←Matrix.mul_assoc, Channel_s α β Y1 u u1,Matrix.mul_assoc, Matrix.mul_assoc G2, p.asset,Matrix.mul_one]
 have hu:B*V=z • (Ψ₁*G1):=by
    unfold B V inkL; rw [Matrix.smul_mul, ←Matrix.mul_assoc, Channel_s β α Y2 u u2,Matrix.mul_assoc, Matrix.mul_assoc G1,q.asset,Matrix.mul_one,star_star]
 have hg: A*V=0:=by unfold A V inkL; rw [Matrix.smul_mul, ←Matrix.mul_assoc, Channel_v α β Y1 v,Matrix.zero_mul,smul_zero]
 have hz': B*U=0:=by unfold B U inkL; rw [Matrix.smul_mul, ←Matrix.mul_assoc, Channel_v β α Y2 v.symm, Matrix.zero_mul,smul_zero]
 have hl:P'* U= Ψ₁*G1∧ P'* V= Ψ₂*G2:=by
    unfold U V; constructor <;> rw [←Matrix.mul_assoc,Channelι,Matrix.mul_assoc]; rw [p.tier]; rw [q.tier]
 have he:B*A=0:=by unfold B A; nth_rw 1 [←t',←t₁]; rw [mul_assoc,←mul_assoc (cutM (Tset N)),cut_air _ _ disjoint_compl_right,zero_mul,mul_zero] -- cutPCom direction reorder
 change (1+B)*(1+A)*P₀*(U+ star z • V)=U+ star z • V
 let Y':=U+ star z • V; rw [add_mul,one_mul,mul_add,mul_one,he,add_zero,add_mul,add_mul,one_mul,t, t',Matrix.add_mul,Matrix.add_mul, Matrix.mul_add A, Matrix.mul_add B,Matrix.mul_smul A,Matrix.mul_smul B,hx,hg,hz',hu, ←hl.1, ←hl.2]; -- t syntax
 rw [smul_smul, lamb',one_smul,smul_zero,add_zero,zero_add]; -- tune
 -- combine by add_assoc
 rw [add_assoc,add_comm (star z • _), ← Matrix.mul_smul P',← Matrix.mul_add P',← Matrix.add_mul, cutM_read', Matrix.one_mul]
omit u1 u2
/-- native argument orientation. not field. uses same affine motion. -/
def eMark (F G:Ruler (Mini N) (Fin r))(Y:Finset Sheet) (α β:Fin 3)(z:ℂ): FC (Single N):= star (quant (1+inkL F G α β Y z))
local notation "B₁"=> eMark F1 G2 Y1 α β z
local notation "B₂"=> eMark F2 G1 Y2 β α (star z)
-- cost from .Support counts & WtPrice intrinsic. also plot representation for holom. .Tight need card? not necessary. q.
lemma plot : eMark F1 G2 Y1 α β z= star (starMark0 (Tset N) Γ₁ M₁):=by
 rw [quantifier _ (Γ₁) M₁ (pigU α _), (uneSeul p q α β v Y1 z).2,(valJ p q α β v Y1 z).1]; -- exact
 rfl
lemma E_zero : eMark F1 G2 Y1 α β 0=1:=by simp [eMark,inkL,quant_one]
lemma E_cost (e:‖z‖=1): ‖eMark F1 G2 Y1 α β z‖ ≤ (1+c1)^(piggy (WalU N U1) Y1 α).card := by
 let Q:= (cibe (G2* F1ᴴ) α β Y1); have hp:‖Q‖ ≤ c1:= by exact (breathe ..).trans ((Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((Matrix.l2_opNorm_conjTranspose ..).trans_le (grip_pay _ p.orth))).trans q.budget))
 have hx:‖inkL F1 G2 α β Y1 z‖ ≤ c1:=by unfold inkL; rw [norm_smul,norm_star,e,one_mul]; exact hp
 rw [plot p q α β v Y1 z, norm_star]; exact starM_cost _ _ _ ((norm_nonneg _).trans hx) hx -- argument
omit p q v
lemma pMount(x:SU.E): orbitB (eMark F1 G2 (genre σ) α β z) x=eMark F1 G2 (genre σ) α β z:=by
 unfold orbitB flipsP eMark; rw [map_star, twist_formula, quantU]; simp only [←quant_star,←quant_mul]; rw [←twist_formula, map_add, map_one, inkL,twist_scalar, matterSpin];
include p q v u1 u2
lemma sunSat (lamb':‖z‖=1)(ω':star z*z=1) (T:Support (More N))(RT: (S.image (wrap N)).image node ⊆ T) (Zl:cutM (wal N S)*W1=W1) (Zr:cutM (wal N S)*W2=W2): Marble (funde 4 M N 1) T r ((B₁)*(B₂)) (2*t):=by
 let A:=Ψ₁*F1; let X:= Ζ; let K:=X*Aᴴ; let D:=A*Aᴴ; let Y:=Fock.Brique.Ortho K; have he: Aᴴ*X=1:= assetJet p q α β v u z; have hv:Aᴴ*A=1:=by unfold A; rw [Matrix.conjTranspose_mul,Matrix.mul_assoc, ←Matrix.mul_assoc Ψ₁ᴴ, Channelθ, Matrix.one_mul,p.orth]
 have hp: K*D=K:=by unfold D K; rw [←Matrix.mul_assoc _ _ Aᴴ,Matrix.mul_assoc X Aᴴ A,hv,Matrix.mul_one]
 have hk:D*K=D:=by unfold D K; rw [←Matrix.mul_assoc _ _ Aᴴ,Matrix.mul_assoc A Aᴴ X,he,Matrix.mul_one]
 have hw:IsStarProjection Y:= ortho_project K
 -- helper cinema transfers with proof
 have hS(B:Sheet)(α:Fin 3):cutM (modesIn N T)*(Channel N (αslot B α))*cutM (wal N S)=(Channel N (αslot B α))*cutM (wal N S):=by
    ext i j; rw [Largo.compass',Largo.compass',Largo.compass]; by_cases h:j∈ wal N S <;> by_cases v:i=(j,αslot B α) <;> first| (subst i;simp [h,RT (mem_image_of_mem node (mem_product.mp h).1)])| simp [Channel,grip,h,v]
 have hx : cutM (modesIn N T)*K=K:=by
    unfold K; rw [←Matrix.mul_assoc]; unfold X; rw [Matrix.mul_add, Matrix.mul_smul]; nth_rw 1 [←Zl,←Zr]; rw [←Matrix.mul_assoc _ (Ψ₁),←Matrix.mul_assoc _ Ψ₂,←Matrix.mul_assoc _ _ W1,←Matrix.mul_assoc _ _ W2, hS u α,hS u β, Matrix.mul_assoc Ψ₁,Matrix.mul_assoc Ψ₂,Zl,Zr]
 refine ⟨Y,ortho_cellar _ hx,hw,(tankL_trace _ _ hp hk).trans (by unfold D; rw [Matrix.trace_mul_comm,hv,Matrix.trace_one, Fintype.card_fin]),?_,?_⟩
 · let L:=(1+Γ₂)*(1+Γ₁); have h : L*P₀*X=X:=rightSeat p q α β v Y1 Y2 u u1 u2 z ω'
   change Full Y (acts (star _) (mateK N)); intro i g; obtain ⟨j,hj⟩:= refill K i; rw [g] at hj; let i':= acts P₀ i; have t:acts L i'=i:=by unfold i'; rw [←act_mul, ←hj, ←act_mul, show L*P₀*K=K from (by unfold K; rw [←Matrix.mul_assoc,h]) ]
   rw [← t,star_mul,eMark,eMark, star_star,star_star, ←quant_mul,←act_mul, ←quant_create,act_mul, (wore _ (mateK N) (cutM_idp _) (touchP _ ▸ tickB _) i' (Cellar.stanch (Tset N) _)),map_zero] -- rw precedence
 let U:= flatH M N; let D:= funde 4 M N 1; have hD:IsStarProjection D:= (by unfold D; rw [fFlat]; constructor; unfold IsIdempotentElem; rw [op_kron_mul, one_mul, (show U*U=U from (flatH_pro ..).1)]; unfold IsSelfAdjoint; rw [op_star_kron, star_one, (show star U=U from (flatH_pro ..).2)])
 have ht': ‖D*X‖ ≤ 2*t:=by
    have hx(a:Slot)(B:Ruler (Mini N) (Fin r))(p:‖U*B‖≤ t):‖D*(Channel N a*B)‖ ≤ t:=by unfold D; rw [fFlat, ←Matrix.mul_assoc,ChannelGl,Matrix.mul_assoc]; exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (grip_pay _ (Channelθ _))).trans p)
    unfold X; rw [Matrix.mul_add,Matrix.mul_smul]; exact (norm_add_le ..).trans ((add_le_add (hx _ _ p.hurdle) (by rw [norm_smul, norm_star, lamb',one_mul]; exact hx _ _ q.hurdle)).trans_eq (two_mul t).symm)
 change ‖Y * D‖ ≤ _; rw [←norm_star,star_mul,hw.2.star_eq,hD.2.star_eq]; rw [← show K*Y=Y from tankL_quad K (A*Aᴴ) hp hk]
 rw [←mul_assoc]; refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (hw.norm_le _)).trans ?_); unfold K; rw [←Matrix.mul_assoc]; exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((Matrix.l2_opNorm_conjTranspose ..).trans_le (grip_pay _ hv))).trans ht')
end
end YM.CF.Window.Mirage
