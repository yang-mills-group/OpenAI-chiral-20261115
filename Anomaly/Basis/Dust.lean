import Anomaly.Basis.Grid
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon Pressure Sault Hest
variable {N B n':Side} {P:BudgetPoint} {h v u z w s:ℝ} {q k L':ℕ}
local notation "θ" => mid N B
local notation "I"=> Single θ
open Buffered
-- director.K.T requests conditions for Sanctimony seeding
variable {K:Scree.Loom (mid N B)}{t d a b φ f g₀ x₀:ℝ} {c m n:ℕ}{o:Site (mid N B)}{δ C:ℝ}
section Extras
variable (T:DockPulse P K t d a h s m q)(W:Sonar.mintQ φ f d P.order) (l:k+q+10 ≤ P.B)(v₀:1 ≤ m)
variable (R:Next.Rank.Spindle.Rules SU.group) (L:4*(k:ℝ)*P.threshold≤R.c) (c':2*(k+1)<(More (mid N B)).val) (hv:8*(k:ℝ)*P.threshold < φ)
variable (H:HopeT d g₀ x₀ P.order) (w':P.threshold ≤ x₀) (ht:P.supportExponent+8/(P.B:ℝ)≤ s)
-- price Dust Earnings.end. Post. Keeping precise inputs to certify polynomial / Quench.
abbrev frostδ(k:ℕ)(a:ℝ):ℝ:= Real.exp (-a*(k:ℝ))
abbrev frostV (B:BudgetPoint):ℝ:= 8*(B.B:ℝ) -- remove
abbrev seam_m (m:ℕ)(C:BudgetPoint)(x:Seat n'):ℝ:= fareX C.B C (grooveB m C x) -- shadow n
variable {F:SOp (mid N B)} (χ:Soak (node o) F (a+a) b d)
local notation "SΨ"=> temple m P (node o)
local notation "e★" => (frostδ k a*b)
local notation "F₀"=> (vaporB P h b)
local notation "KΨ" => seam_m m P (node o)
abbrev spill_F (p:BudgetPoint)(k m:ℕ)(b a s h:ℝ) :ℝ:= reefCost m p s h*(frostδ k a*b)
local notation "uΨ"=> spill_F P k m b a s h
local notation "u_Ψ"=> cashPoncho (F₀) s m
local notation "tΨ"=> (Nor.reserveT P.power P.order P.B (P.B:ℝ)⁻¹*|uΨ|)
local notation "Aσ"=> AxStamp.Ρpost P
local notation "oz"=> Cube.node o
include T W R χ L l hv c' v₀ ht H w'
lemma extra_core (g: F (profile 1)=0){J:Op (Single (mid N B))→FC (Dwell (mid N B))}{Z: Single (mid N B)→ Single (mid N B)→FC (Dwell (mid N B))}(p:Glyph J Z h):
 let Ft:= (haloSites k:ℝ)^2 * ((P.order+1:ℝ)*(e★+Φσ P f b k+P.threshold/x₀*b)*h^2); let W:= cashPoncho (KΨ * Ft) P.supportExponent m;
 ∃ A:Bag θ,Drill P q m L' o h s A 0 (u_Ψ+uΨ) (W+tΨ) (Aσ W + Aσ tΨ)∧ giveB A=shipInc K F J:=by
 obtain ⟨X,Y,t₁,p₁,v₁⟩:=cut_tr k χ T.hint; let W₀:=shipInc K X J; let M:=pozV oz P m W₀; intro Vq V; let E :=unroll_core t₁ T l v₀ p
 have hx: ‖X (profile 1)‖≤e★:=by
    have ht':=norm_U p₁ T.hint.le (x:=⟨profile 1,1,guard0 T.pos.le,by simpa using T.pos⟩)
    rw [show X (profile 1)= -Y (profile 1) from (eq_neg_of_add_eq_zero_left (g ▸ (v₁ (⟨profile 1,1,guard0 T.pos.le,by simpa using T.pos⟩:Openc (More θ) d)).symm)) , norm_neg]; exact ht'
 have hr:= seminar t₁ T l v₀ p W R L c' hv H w' hx
 have hδ:Drill P q m L' o h s M 0 u_Ψ V (Aσ V):=debitExtra E T.high T.most T.hood hr
 let H:= Mortgage T true Y p₁ J Z p (by simp); obtain ⟨P',q',x'⟩:= H.ticket
 have hv': Drill P q m L' o h s P' 0 uΨ tΨ (Aσ tΨ):=Drill.stampS (by simpa only [ite_true] using q') le_rfl T.high ht T.most le_rfl
 refine ⟨M+P',zero_add (0:ArcΦ) ▸ (hδ.gain hv' T.high),?_⟩
 rw [show giveB (M+P')=giveB M+giveB P' from by simp only [giveB,Pi.add_apply,sum_add_distrib],←x',offset_P]; funext i; change J _+J _= J (F (profile (K i))); rw [show F (profile (K i))=_ from v₁ (roller T.pos T.roof i)]; simp_rw [p.whirl,Matrix.add_apply,add_smul,sum_add_distrib]; rfl
-- subtract trace of full here. restore at point mark or lift
lemma extra_trace (x:ℂ)(g:Matrix.trace (F (profile 1))=x):
 let Ft:= (P.order+1:ℝ)*(e★+Φσ P f b k +P.threshold/x₀*(b+‖x‖)); let W:= cashPoncho (KΨ * Ft) P.supportExponent m; let Fν:=cashPoncho ((F₀)+‖x‖) s m;
 ∃ A:Bag θ,Drill P q m L' o h s A 0 (Fν+uΨ) (W+tΨ) (Aσ W + Aσ tΨ)∧ giveB A=shipInc K F (fun A=>Matrix.trace A • 1)-x • 1:=by
 obtain ⟨X,Y,t₁,p₁,v₁⟩:=cut_tr k χ T.hint; let J(M:Op I):FC (Dwell θ):= Matrix.trace M •1; let S:= shipInc K X J - x • 1; let M:=pozV oz P m S; intro Vq V u; have hx:Herb P q SΨ h S ((F₀)+‖x‖):=by unfold S; rw [sub_eq_add_neg]; exact (unroll_core t₁ T l v₀ (oreV h T.high (mid N B))).addR ((Herb.scalar x).negR)
 let U:Openc (More θ) d:=⟨profile 1,1,guard0 T.pos.le,by simpa using T.pos⟩
 have hg: ‖Matrix.trace (X (profile 1))-x‖≤e★:=by
    rw [←g,v₁ U|>.symm.symm, Matrix.trace_add]; -- might need profile defeq.
    have ht:=Soak.siteCost p₁ T.hint.le U; rw [sub_add_eq_sub_sub, sub_self,zero_sub,norm_neg]; exact (norm_sum_le ..).trans (le_trans (sum_le_sum (fun i _=>single_le_sum (f:=fun j=>‖Y U.val i j‖) (fun j _=>norm_nonneg _) (mem_univ i))) ht)
 have hx': AuraOp P SΨ ∅ S h Vq:=by
    rw [show S=(fun i=>(Matrix.trace (X (profile (K i)))-x) • (1:FC (Dwell θ))) from funext (fun i=>by rw [sub_smul]; rfl)]; exact traceSeat t₁ T l v₀ W R L c' hv H w' x hg
 have hδ:Drill P q m L' o h s M 0 u V (Aσ V):=debitExtra hx T.high T.most T.hood hx'
 obtain ⟨P',q',x'⟩:= (Mortgage T true Y p₁ J _ (oreV h T.high _) (by simp)).ticket
 have hv':Drill P q m L' o h s P' 0 uΨ tΨ (Aσ tΨ):= Drill.stampS (by simpa only [ite_true] using q') le_rfl T.high ht T.most le_rfl
 refine ⟨M+P',zero_add (0:ArcΦ) ▸ (hδ.gain hv' T.high),?_⟩
 rw [show giveB (M+P')=giveB M+giveB P' from by simp only [giveB,Pi.add_apply,sum_add_distrib],←x',offset_P]
 funext i; change J _-x • 1+J _= J (F (profile (K i))) - x • 1
 rw [show F (profile (K i))=_ from v₁ (roller T.pos T.roof i)]; rw [show profile (K i)=(roller T.pos T.roof i).val from rfl]; unfold J; rw [Matrix.trace_add, add_smul]; abel
omit W R L l c' hv H w' v₀ χ
lemma dead_core {F:SOp (mid N B)} (χ:Soak (node o) F a b d){J:Op (Single (mid N B))→FC (Dwell (mid N B))}{Z: Single (mid N B)→ Single (mid N B)→FC (Dwell (mid N B))}(p:Glyph J Z h)(z:∀ F:Op (Single (mid N B)),acts (J F) (vacuum (Dwell θ))=0):
 ∃ A:Bag (mid N B),Drill P q m L' o h s A 0 (reefCost m P s h*b) 0 0 ∧ giveB A=shipInc K F J:=by
 obtain ⟨A,H,K⟩:= (Mortgage T false F χ J Z p (fun _=> z)).ticket
 have hx := (Real.exp_pos (s*Fief.tileN m)); have ht':0≤b:=soakCostNN χ; have hv: 0≤reefCost m P s h*b:=by unfold reefCost; positivity
 have h:Drill P q m L' o h s A 0 (reefCost m P s h*b) 0 (Aσ 0):= Drill.stampS (by simpa only [Bool.false_eq_true,ite_false] using H) hv T.high ht T.most (by simp)
 exact ⟨A,by simpa only [AxStamp.Ρpost,mul_zero] using h,K.symm⟩
end Extras
end YM.CF.Vow.TreasuryFog
