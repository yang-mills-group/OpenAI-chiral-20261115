import Anomaly.Gab.Pithy
/-!
 Proportionate transport & receipt after KEY regrouping. Includes actual physical transfers. Q is fine, q is parent.
 Z frame is relative to MARK coords, not assuming orthonormal basis T.
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T δ W:ℝ}{z:ℂ}
namespace SketchA
variable {P:ArmorK}{u p f q:ℝ}
local notation "ι"=> Sum I Unit
local notation "ΣS"=> ρZee B
local notation "Θ"=> pκ.coin_Z L Q
local notation "κρ"=> κprobe mintR L H (A*Q) w z
local notation "Lν"=> ((L.val:ℝ)⁻¹)
local notation "ΠV"=> E × ℂ
-- diagonal scale using Lo.Sum basis. proof by basis_ext
variable (B':Basis I ℂ E)
def Heat_r (v:I→ ℂ): E→ₗ[ℂ]E:= B'.constr ℂ fun i=> v i • B' i
lemma heat_comp (a b:I→ℂ)(h:∀ i,a i*b i=1): (Heat_r B' a).comp (Heat_r B' b)=LinearMap.id:=by
 apply B'.ext; intro i; change Heat_r B' a ((B'.constr ℂ _) (B' i))=_; rw [Basis.constr_basis,map_smul,Heat_r,Basis.constr_basis,smul_smul,mul_comm,h,one_smul]; rfl
lemma heat_up (a:I→ℂ)(h:∀ i,a i≠0): ∃ D:E≃ₗ[ℂ] E,D.toLinearMap=Heat_r B' a∧ D.symm.toLinearMap= Heat_r B' (a⁻¹):=by
 let G:= Heat_r B' (a⁻¹)
 have ht: (Heat_r B' a).comp G=LinearMap.id:=heat_comp _ _ _ fun i=>mul_inv_cancel₀ (h i)
 have hv:G.comp (Heat_r B' a)=LinearMap.id:=heat_comp _ _ _ fun i=> inv_mul_cancel₀ (h i)
 exact ⟨LinearEquiv.ofLinear (Heat_r B' a) G ht hv,rfl,rfl⟩
variable (t:Melon L X Y z H Q A w)
variable (F:Sum I Unit→ ArcΦ × ℂ) -- output FULL
variable {Z:Sum I Unit→ArcΦ × ℂ}
variable (M:(E × ℂ)≃ₗ[ℂ](E × ℂ))(U: M.toLinearMap=τFrame pκ L Q H F) (x:∀ v:(E × ℂ),‖M.symm v‖≤ T *‖v‖)
variable (h:∀ i,Markup L X Y z H Q A w K C v0 v1 v2 (Z i).1 (F i).1 (Z i).2 (F i).2)
variable (y:∀ i,pκ.winA H (Z i)= (Q:ℂ) • (ρZee B i))
variable (v:∀ i, |κprobe mintR L H (A*Q) w z (Z i).1| ≤ u*pκ.coin_Z L Q i) (J:far_C A* |C| * ((L.val:ℝ)⁻¹) ≤ 1/2) (pᵤ: ∀ i: Unit,|κprobe mintR L H (A*Q) w z (Z (Sum.inr i)).1| ≤ far_C A* (((L.val:ℝ)⁻¹)*Q))
variable (fA:T>0) (hg:0≤u)
variable (p0:0<q)(p1:q≤ 2*Q)(p2:Q≤ 2*q)
-- Includes price with $K_⁣$ decided. q/T. forward inverse lower weight bound.
abbrev rimK (B:Basis I ℂ E)(T:ℝ):= ρθ (ρZee B)* T
-- choose C_shadow.Dual costs independent h.B.A!
abbrev shadowY (u K C:ℝ):= 2+paceY*|K| * u + |C| * u + 1
structure Tiara (A: Sum I Unit→ ArcΦ × ℂ) (F: Sum I Unit→ ArcΦ × ℂ) (z:ℂ)(H Q w K W T u B':ℝ)(q:ℝ)(L:Side)(D:ΠV≃ₗ[ℂ]ΠV) : Prop where
 -- `W`:A input efficiently
 bead :∀ i:Sum I Unit, pκ.winA H (F i)=(q:ℂ) • (D.symm ((ρZee B) i))
 garb :∀ i, |κprobe mintR L H (W*Q) w z (A i).1| ≤ u*pκ.coin_Z L Q i
 seat(x:ΠV):∀ i, ‖(ρZee B).coord i (D x)‖ ≤ q/pκ.coin_Z L Q i * (T*‖x‖)
 pose :∀ i, ‖D.symm (ρZee B i)‖ ≤ B'*(pκ.coin_Z L Q i/q)
 ivory :∀ i: Unit, Q/(2*q)≤ ‖(D.symm (ρZee B (.inr i))).2‖
include t h M y v pᵤ J hg U x fA p0
lemma calyx : ∃ D:ΠV≃ₗ[ℂ]ΠV,Tiara pκ Z F z H Q w K A (ρθ (ρZee B)*T) u (shadowY u K C) q L D:=by
 let G:= τFrame pκ L Q H F; have H₀:= t.rank; have hp:=pκ.coin_pos L Q H₀
 have hS(i):0<Θ i/q:=div_pos (hp i) p0
 let Cφ(i):= (↑(Θ i/q):ℂ); have hv(i):Cφ i≠0:=Complex.ofReal_ne_zero.mpr (hS i).ne'
 obtain ⟨Bθ,r,g⟩:=heat_up (ρZee B) Cφ hv -- shadow
 let D:= (Bθ.trans M).symm
 have he(i:Sum I Unit):pκ.winA H (F i)=(q:ℂ) • (D.symm ((ρZee B) i)):=by
    change _=(q:ℂ) • M (Bθ.toLinearMap ((ρZee B) i)); rw [r,Heat_r,Basis.constr_basis,map_smul]
    rw [show M ((ρZee B) i)= G ((ρZee B) i) from DFunLike.congr_fun U _,show G ((ρZee B) i)=_ from (show _= (↑(Θ i):ℂ)⁻¹ • pκ.winA H (F i) from Basis.constr_basis ..), smul_smul,smul_smul, show (q:ℂ)*Cφ i * (↑(Θ i):ℂ)⁻¹=1 from ?_, one_smul] -- order
    unfold Cφ; push_cast; have hz:(q:ℂ)≠0:= Complex.ofReal_ne_zero.mpr p0.ne'; have hn:(↑(Θ i):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (hp i).ne'; field_simp
 have hu(i y):(ρZee B).coord i (D y)=(Cφ i)⁻¹ • ((ρZee B).coord i (M.symm y)):=by
    let z:=M.symm y; let G':ΠV→ₗ[ℂ]ΠV:= Bθ.symm.toLinearMap; have ht:G'=Heat_r (ρZee B) (Cφ⁻¹):=g
    change _=((Cφ i)⁻¹) • ((ρZee B).coord i z)
    have hx: ((ρZee B).coord i).comp G'= ((Cφ i)⁻¹) • ((ρZee B).coord i):=by
       apply (ρZee B).ext; intro j
       simp only [ht, Heat_r,LinearMap.comp_apply,Basis.constr_basis,map_smul]; by_cases v:i=j; · subst j; rfl
       simp only [LinearMap.smul_apply,Basis.coord_apply,Basis.repr_self, Finsupp.single_eq_of_ne v,smul_zero]
    exact DFunLike.congr_fun hx z
 refine ⟨D,he,v,fun a i=>?_,fun i=>?_,fun i=>?_⟩
 · have ht: ‖(ρZee B).coord i (M.symm a)‖≤ ρθ (ρZee B)*(T*‖a‖):= (pagan (ρZee B) i _).trans (mul_le_mul_of_nonneg_left (x a) (μp_pos _).le)
   rw [hu,norm_smul,norm_inv,show ‖Cφ i‖ = _ from (Complex.norm_real (Θ i/q)).trans (Real.norm_of_nonneg (hS i).le),inv_div,mul_assoc (ρθ _)]
   exact mul_le_mul_of_nonneg_left ht (div_nonneg p0.le (hp i).le)
 · let z:= (F i); let Q':= Θ i; have hm:Q' >0:= hp i
   have hs:‖pκ.winA H z‖≤ shadowY u K C * Q':=by
      have hf:= pκ.pace H z.1; have hv':= Markup.pay_Y t (h i) (v i); let U':=‖(F i).2‖; have hko:= Markup.offset_pay t (h i) (v i); have hz :‖(F i).2‖≤ ‖(Z i).2‖+ |C| * (u*Q'):= by linarith only [hko,norm_sub_norm_le (F i).2 (Z i).2]
      have hb: ‖(Z i).2‖≤ Q':=by
         unfold Q'; have hθ:(Z i).2= (Q:ℂ) • (ΣS i).2:= congrArg Prod.snd (y i)
         cases i with
         | inl j=> rw [hθ,zee₀,smul_zero,norm_zero]; exact (hp _).le
         | inr j=> rw [hθ,zee₁]; exact le_of_eq (Eq.trans (congrArg norm (mul_one (Q:ℂ))) ((Complex.norm_real _).trans (Real.norm_of_nonneg H₀.le)))
      rw [Prod.norm_def]; have ha: 0 ≤ paceY:= zero_le_one.trans paceY_paid
      refine max_le ((hf.trans hv').trans ?_) (hz.trans ?_); unfold shadowY <;> first| (change paceY*(_*(u* Q')) ≤ _; nlinarith only [hm,mul_nonneg (mul_nonneg (abs_nonneg C) hg) hm.le])|nlinarith only [hm,hb,mul_nonneg (mul_nonneg (mul_nonneg ha (abs_nonneg K)) hg) hm.le] -- bullets
      unfold shadowY; nlinarith only [hm,hb,mul_nonneg (mul_nonneg (mul_nonneg ha (abs_nonneg K)) hg) hm.le]
   unfold z at hs; rw [he,norm_smul,Complex.norm_real,Real.norm_of_nonneg p0.le] at hs
   rw [←mul_div_assoc,le_div_iff₀ p0,mul_comm _ q]; exact hs
 let j:= Sum.inr (α:=I) i; have ht:=Markup.offset_pay t (h j) (pᵤ i)
 have hz : ‖(Z j).2‖=Q:=by rw [show _ = _ from (show (Z j).2=(Q:ℂ) • (ΣS j).2 from congrArg Prod.snd (y j)),zee₁]; exact (congrArg norm (mul_one (Q:ℂ))).trans ((Complex.norm_real _).trans (Real.norm_of_nonneg H₀.le))
 have hv': ‖(Z j).2‖-‖(F j).2‖ ≤ (1/2:ℝ)*Q:= ((norm_sub_norm_le (Z j).2 _).trans_eq (norm_sub_rev ..)).trans (ht.trans ?_)
 swap; · exact (Eq.le (show |C| * (far_C A * ((L.val:ℝ)⁻¹ * Q))=(far_C A * |C| * Lν)*Q from by ring)).trans (mul_le_mul_of_nonneg_right J H₀.le)
 have hx:(F j).2=(q:ℂ) • (D.symm ((ρZee B) j)).2:= congrArg Prod.snd (he j)
 set S:= (D.symm ((ρZee B) j)).2 with p; have he: ‖(F j).2‖=(q:ℝ)*‖S‖:= by rw [hx,norm_smul,Complex.norm_real, Real.norm_of_nonneg p0.le]
 rw [he,hz] at hv'; change Q/(2*q)≤ ‖S‖; rw [div_le_iff₀ (by positivity)]; nlinarith only [hv']
end SketchA
end YM.CF.Py
