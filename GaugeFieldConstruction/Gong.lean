/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Hock
import GaugeFieldConstruction.Wand
/-!
# PH Taylor at the very Pane values
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
open Lenten Lenten.ModuleB
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove
open MultiNext.SignedSource PhysicalNext.JointLoad Analysis Siete Banjo
namespace Axon
variable {n:Side}{P: BudgetPoint} {Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c s r b:ℝ}{g:Finset (Dwell n) → ℝ}{m:ℕ}
local notation "αₚ"=> X.val.1
local notation "C'"=> X.val.2
variable (v:PressB P X Q h c)(p:∀ U,BedP P U Q X g) {x:tangD n}
abbrev porch (Q:InkD n)(i j:Single n)(V:Pane n):ℂ:=orbitPH (Q V) i j
private lemma scale_left {F:tangD n→ℂ}(h:Signs P o F c)(i:ℂ)(hy:‖i‖=1): Signs P o (fun v=>i*F v) c:=by
 let L:ℂ →L[ℝ] ℂ:= i • ContinuousLinearMap.id ℝ ℂ
 refine ⟨h.grade,L.contDiff.contDiffAt.comp 0 h.paid,fun j hj y w=>?_⟩
 change ‖iteratedFDeriv ℝ j (L ∘ F) 0 y‖≤_; rw [L.iteratedFDeriv_comp_left (f:=F) h.paid (Nat.cast_le.mpr hj)]; change ‖i* iteratedFDeriv ℝ j F 0 y‖ ≤ _; rw [norm_mul,hy,one_mul]; exact h.token _ hj _ w
include p
lemma TollJ (x y:Single n)(U:Pane n)(hU:pingS P.threshold C' U): Signs P X.val.1 (porch Q x y∘ increment U) (g (Haro.tray x y)):=by
 let b:Dwell n:= (true,x); let a:Dwell n:= (false,y); let V:= Fock.parity b {a}
 have he:b≠a:=by simp [b,a]
 have hx(i:tangD n): (porch Q x y∘ increment U) i= V * Pastry.crumb (Q (increment U i)).val (Haro.tray x y):= by unfold porch orbitPH; rw [Function.comp_apply,Matrix.of_apply,Prism.port_eq,if_neg he]
 rw [funext hx]; exact scale_left (p U hU _) _ (by simp [V,Fock.parity])
include v
lemma PortProof (x:tangD n)(e:pingS P.threshold X.val.2 (increment 1 x))(i j:Single n):ContDiffAt ℝ (6:WithTop ℕ∞) (portE Q i j) x:= (stirring 1 x (fun U V h=>congrArg (fun x=> orbitPH x i j) (v.term U V h)) _ (TollJ p _ _ _ e)).of_le (Nat.cast_le.mpr P.order_ge)
lemma cumulus_cost (e:Chamber X P x)(t:ℝ)(w:t∈ Set.Icc 0 1)(b':0 ≤ b)(y:b ≤ 1)(s':1 ≤ s)(l:3 ≤ m)(k:m ≤6)(F: Fin m → tangD n)(f:∀ i,Footmark P X s b (F i))(i j:Single n): ‖iteratedFDeriv ℝ m (portE Q i j) (t • x) F‖≤ ((xHoch 6) * (4*s)^6* b^3) * g (tray i j) :=by
 have hg:= TollJ p i j _ (e.2 t w); apply ((multip 6).choose_spec.2 n X.val.2 1 P αₚ (t • x) (porch Q i j) (fun i' j' h=> congrArg (fun x=> orbitPH x i j) (v.term i' j' h)) (g (tray i j)) hg (tile_c e t w) m k (k.trans P.order_ge) F (fun _=>4*s*b) (fun i=>payφ _ b' y s' (f i))).trans
 have hu: 0 ≤ xHoch 6:= zero_le_one.trans (multip 6).choose_spec.1
 rw [prod_const,card_univ,Fintype.card_fin,mul_pow (4*s)]; -- tune
 apply mul_le_mul_of_nonneg_right _ hg.grade; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ (by linarith) k) (pow_le_pow_of_le_one b' y l) (by positivity) (by positivity)) hu
-- flat directional pencil for mixed cost; ley using order two signs
omit v p
def mastX (Q:InkD n) {m:ℕ}(x:tangD n)(F: Fin m → tangD n): Op (Single n):= Matrix.of fun i j=> iteratedFDeriv ℝ m (portE Q i j) x F
lemma mastØ (F:Fin 0→ tangD n): mastX Q x F=orbitPH (Q (increment 1 x)):= by ext i j; simp only [mastX, Matrix.of_apply, iteratedFDeriv_zero_apply] -- tune simp
lemma mast_flat (F:Fin 0→ tangD n): mastX Q 0 F=orbitPH (Q 1):= by rw [mastØ,Work.G07.at_zero_increment]
lemma mast_Ψ (F:Fin 1→ tangD n): mastX Q 0 F=Paint Q (F 0):= by ext i j; rw [mastX, Matrix.of_apply,iteratedFDeriv_one_apply]; rfl
-- recursive via FiN cases
private abbrev join {j:ℕ} (x:tangD n)(y: Fin j→tangD n):Fin (j+1)→tangD n:=Fin.cons x y
def Axis_Price (Q:InkD n){m:ℕ}(x:tangD n)(F:Fin m→ tangD n)(t:ℝ):Op (Single n):= match m with
| 0 => mastX Q 0 F+t • mastX Q 0 (join x F)+(t^2/2) • mastX Q 0 (join x (join x F))
| 1 => mastX Q 0 F+t • mastX Q 0 (join x F)
| 2 => mastX Q 0 F
| _+3 => 0
lemma CoinØ (F:Fin m→ tangD n)(l:m ≤2): Axis_Price Q x F 0= mastX Q 0 F:=by interval_cases m <;> simp [Axis_Price]
lemma axis_turn (F:Fin m→ tangD n)(w:m ≤ 2)(t:ℝ)(i j:Single n):HasDerivAt (fun t=> Axis_Price Q x F t i j) (Axis_Price Q x (join x F) t i j) t:=by
 interval_cases m
 · let A:=mastX Q 0 (join x F); let B:= mastX Q 0 (join x (join x F));
   change HasDerivAt (fun t:ℝ=> mastX Q 0 F i j+t • A i j+(t^2/2) • B i j) ((A i j)+(t • (B i j))) t
   have hz(C:ℂ):HasDerivAt (fun z:ℝ=>z • C) C t:=by simpa using (hasDerivAt_id' t).smul_const (C:ℂ)
   have hx:HasDerivAt (fun t:ℝ=> t^2/2) t t:=by simpa using ((hasDerivAt_id' t).pow 2).div_const 2 -- tune mul_div
   simpa only [zero_add] using ((hasDerivAt_const _ _).fun_add (hz (A i j))).fun_add (hx.smul_const (B i j)) -- tune map types
 · change HasDerivAt (fun t=> mastX Q 0 F i j+t • (mastX Q 0 (join x F) i j)) (mastX Q 0 (join x F) i j) t
   simpa only [Pi.add_apply,one_smul,zero_add] using (hasDerivAt_const t _).fun_add ((hasDerivAt_id' t).smul_const (mastX Q 0 (join x F) i j)) -- tune
 change HasDerivAt (fun _=>_) (0:ℂ) t; exact hasDerivAt_const ..
include v p
lemma Axis_Pay (t:ℝ) (u:0 ≤ b)(y:b ≤ 1)(s':1 ≤ s)(i j:Single n)(e:t∈ Set.Icc 0 1)(F: Fin m→ tangD n)(k:m≤6)(f:∀ a,Footmark P X s b (F a))(g₀:Footmark P X s b x)(w:Chamber X P x): ‖(mastX Q (t • x) F - Axis_Price Q x F t) i j‖≤ ((xHoch 6) * (4*s)^6* b^3)*g (tray i j):=by
 induction k using Nat.decreasingInduction generalizing t with
 | self=> rw [show Axis_Price Q x F t=0 from rfl, sub_zero]; exact cumulus_cost v p w t e u y s' (by omega) le_rfl F f i j
 | of_succ j' h' ih=>
   by_cases hl:j' ≤2; swap
   · rw [show Axis_Price Q x F t=0 from (by have hl : 3≤j':=(by omega); interval_cases j' <;> rfl),sub_zero]; exact cumulus_cost v p w t e u y s' (by omega) (by omega) F f i j
   let Y:=join x F
   have ha (z:ℝ)(l:z∈Set.Icc (0:ℝ) 1): HasDerivAt (fun z:ℝ=> mastX Q (z • x) F i j- Axis_Price Q x F z i j) ((mastX Q (z • x) Y - Axis_Price Q x Y z) i j) z:= (Heir.along_deriv x F z ((PortProof v p (z • x) (w.2 z l) i j).of_le (Nat.cast_le.mpr h'))).sub (axis_turn F hl z i j)
   have hx:∀ k,Footmark P X s b (Y k):=Fin.cases (by simpa [Y] using g₀) fun i=> by simpa [Y] using f i
   have hg:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun z:ℝ=>mastX Q (z • x) F i j-Axis_Price Q x F z i j) (fun i h=>(ha i h).hasDerivWithinAt) (fun k u=> ih k u Y hx) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 from (by simp)) e
   rw [zero_smul,CoinØ F hl,sub_self,sub_zero,sub_zero,Real.norm_of_nonneg e.1] at hg
   have hp:0 ≤ g (tray i j):=(TollJ p i j 1 (ping_f P C')).grade; have hl:0 ≤ xHoch 6:=zero_le_one.trans (multip 6).choose_spec.1
   exact hg.trans (mul_le_of_le_one_right (by positivity) e.2)
-- OrderedFinpartition derivative in this curve; preserve remainder count
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev fieldBlock (F:E→tangD n)(V:Fin m→ E) (p:OrderedFinpartition m)(i:Fin p.length) := iteratedFDeriv ℝ (p.partSize i) F 0 (V ∘ p.emb i)
lemma carve_axis (F:E→ tangD n)(V: Fin m→ E)(u:0≤b)(z:b≤1)(s':1 ≤ s)(G:Set E)(k:m ≤6)(y:∀i,V i∈ G)(l: LocalCurve P X F G s b): (∀ i j:Single n, ContDiffAt ℝ (6:WithTop ℕ∞) (portE Q i j ∘ F) 0) ∧ ∃ f:OrderedFinpartition m→ Op (Single n), (Matrix.of fun (i j:Single n)=> iteratedFDeriv ℝ m (portE Q i j ∘ F) 0 V) = ∑ d:OrderedFinpartition m,(Axis_Price Q (F 0) (fieldBlock F V d) 1+f d) ∧ ∀ d i j, ‖f d i j‖≤ ((xHoch 6) * (4*s)^6* b^3)*g (tray i j):=by
 let T:=F 0; let x(d:OrderedFinpartition m):=fieldBlock F V (d:OrderedFinpartition m) -- syntax := fix
 let v'(d):=mastX Q T (x d); let H(d):=Axis_Price Q T (x d) 1; have hp:pingS P.threshold X.val.2 (increment 1 T):=by simpa only [T,one_smul] using l.home.2 1 (by simp)
 have ht(i j:Single n):= PortProof v p T hp i j
 refine ⟨fun i j=> (ht i j).comp 0 l.smooth, fun d=>v' d-H d,?_,?_⟩
 · simp_rw [show ∀ i, Axis_Price Q (F 0) (fieldBlock F V i) 1+(v' i-H i)=v' i from fun i=> add_sub_cancel ..]; ext i j; rw [Matrix.of_apply,iteratedFDeriv_comp (ht i j) l.smooth (by exact_mod_cast k),FormalMultilinearSeries.taylorComp,_root_.sum_apply, Matrix.sum_apply]; rfl -- tune
 intro d i j; have he(a):Footmark P X s b (x d a):= l.releases _ ((d.partSize_le a).trans k) _ (fun i=> y (d.emb _ _)); have hh:=Axis_Pay v p 1 u z s' i j (by simp) (x d) (d.length_le.trans k) he l.truck l.home; rw [one_smul] at hh; exact hh
end Axon
end YM.CF.TableF
end
