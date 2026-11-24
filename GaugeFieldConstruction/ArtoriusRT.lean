import GaugeFieldConstruction.CompartiRT
import GaugeFieldConstruction.GantryRT
/-!
 # Contour branch calculus: interior FHol test with fixed supports in v∈ℝ^3. Integral full alt variants. Signs ∂ analytic.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface PortRT
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)(g:Bool)
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "Nx"=> τNearRT k
local notation "Railf"=> Full (n+1)
abbrev ZSideRt (n:ℕ):= ℂ × Full n
local notation "ΨXY" => ZSideRt n
noncomputable def WingRT := NameΛShellRT k g ∘L (((τBoostXRt k) ∘L (ContinuousLinearMap.snd ℂ ℂ (Full n))) + ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℂ ℂ (Full n)) (realDirΛ ιᵢ timeAxis))
noncomputable def BarcoRT : Space3 →L[ℝ] Full (n+1):=LinearMap.toContinuousLinearMap {
 toFun v:= NameΛShellRT k g (BurstIRt ιᵢ (position v 0))
 map_add' a b:=by
    rw[← map_add]; apply congrArg; unfold BurstIRt; rw [← map_add]; congr 1; ext1 i; by_cases h:i=ιᵢ; · simp[h]; apply ext_by <;> simp
    simp [h]
 map_smul' c a:=by
    change _=c • NameΛShellRT k g (BurstIRt k.castSucc (position a 0)); rw [show c • ((NameΛShellRT k g) _)=(c:ℂ) • _ from Complex.coe_smul _ _|>.symm,←map_smul,show (c:ℂ) • BurstIRt _ _= c • _ from Complex.coe_smul _ _]; apply congrArg; unfold BurstIRt; rw [← map_smul]; congr 1; ext1 i; by_cases h:i=ιᵢ; · simp[h]; apply ext_by <;>simp
    simp [h] }
lemma analyticBarRT (v:Space3)(w:ΨXY): QchIRt k g w v= WingRT k g w + BarcoRT k g v:=by
 unfold QchIRt; rw [shellPaintRt]; change _=(NameΛShellRT k g) (τBoostXRt k w.2 + w.1 • _) + NameΛShellRT k g _; rw [← map_add]; congr 1; abel
lemma χTintRt : Continuous (fun q:ΨXY × Space3 => QchIRt k g q.1 q.2):=by
 simp_rw [analyticBarRT]; fun_prop
lemma χUpwardRT (i:Fin 3): BarcoRT k g (skyIRT i)= realDirΛ (dayRT k g) i.castSucc:=by change NameΛShellRT k g _=_; rw [posIRt]; exact shellDirRt ..
lemma χAccountRt : WingRT k g ((1:ℂ),0)= realDirΛ (dayRT k g) timeAxis:=by
 change NameΛShellRT k g ((τBoostXRt k) 0+(1:ℂ) • _)=_; rw[one_smul,map_zero,zero_add,shellDirRt]
variable (f: Space3→ℂ)(hf:Continuous f)
variable (G: Full (n+1)→ℂ)(T:Set (Full (n+1))) (eT:IsOpen T)(hG:AnalyticOnNhd ℂ G T)
noncomputable abbrev StemRailRt (p:ZSideRt n)(x:Space3):= f x*G (QchIRt k g p x)
local notation "A_φ"=> StemRailRt k g f G
variable {A:Set (ZSideRt n)}{K S:Set Space3}(hK:IsCompact K)(hS:MeasurableSet S)(p:S⊆K)
variable (u:MapsTo (fun z:ZSideRt n × Space3=>QchIRt k g z.1 z.2) (A ×ˢ K) T)
local notation "D_s"=> StemRailRt k g f G
include u eT hG hf p hK
local notation "K_μ" => QchIRt k g
lemma TownGlassRT (a:ZSideRt n)(v:a∈A): IntegrableOn (D_s a) S:= IntaRT (A:=A) hK p _ v
 (show ContinuousOn (fun z:ZSideRt n × Space3 => D_s z.1 z.2) (A ×ˢ K) from (hf.comp continuous_snd).continuousOn.mul (hG.continuousOn.comp (χTintRt k g).continuousOn u))
noncomputable abbrev CrestRailRt (p:ZSideRt n)(x:Space3): ZSideRt n →L[ℂ] ℂ:= f x • (fderiv ℂ G (QchIRt k g p x) ∘L WingRT k g)
local notation "D_1"=> CrestRailRt k g f G
variable {a:ZSideRt n}(r:a∈A)
include r
lemma TactΓRt : ContinuousOn (fun z:ΨXY × Space3=> CrestRailRt k g f G z.1 z.2) (A ×ˢ K):=by
 refine fun z hz=> ContinuousAt.continuousWithinAt ( (hf.comp continuous_snd).continuousAt.smul (f:=fun z:ΨXY × Space3=>f z.2) ?_)
 let M:=fun z:ΨXY × Space3=> QchIRt k g z.1 z.2
 exact ((((hG _ (u hz)).fderiv).continuousAt).comp (f:=M) (χTintRt k g).continuousAt).clm_comp continuousAt_const
lemma TeaseTwistRt : IntegrableOn (CrestRailRt k g f G a) S:=IntaRT (A:=A) hK p _ r (TactΓRt k g f hf G T eT hG hK p u r)
include hS
lemma TαDerivRT (q:IsOpen A): HasFDerivAt (fun z=>∫ y in S,A_φ z y) (∫ y in S, D_1 a y) a:=by
 refine SwellDerivativeRt q hK hS p _ _ ?_ (TactΓRt k g f hf G T eT hG hK p u r) (fun x hx y hy=>?_) a r
 · exact (hf.comp continuous_snd).continuousOn.mul (hG.continuousOn.comp (χTintRt k g).continuousOn u)
 have h:= (hG _ (@u (x,y) ⟨hx,hy⟩)).differentiableAt; change HasFDerivAt (fun z=> f _*G (K_μ z _)) (f _ • (_ ∘L _)) x
 exact (h.hasFDerivAt.comp x (show HasFDerivAt (fun x=>QchIRt k g x y) (WingRT k g) x from by simp_rw [analyticBarRT]; exact (WingRT k g).hasFDerivAt.add_const _)).const_mul _ -- tune
omit r
lemma TαNormalRT (q:IsOpen A): AnalyticOnNhd ℂ (fun z=>∫ y in S,A_φ z y) A:=by
 intro a i; apply PolyDisc.finiteD; filter_upwards [q.mem_nhds i] with a r; exact (TαDerivRT k g f hf G T eT hG hK hS p u r q).differentiableAt
#print axioms TαNormalRT
end YM.NSF.Boundary
end
