import GaugeFieldConstruction.Nomar
import YM.CF.Prism.Homic
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 45000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open FlightFlux Fluxim
open Labels Source Source.Drops Analysis MultiNext.SignedSource Mom Pattern
open Cube
namespace Axon
local notation "GS"=> SU.group
open AnalyticBridge VerifiedReset Next.Foundations Taxi Lenten Flot
variable {n:Side} {P: BudgetPoint}{X:Scree.Hub n}{Q:InkD n}{T:tangD n}{a c:ℝ}{p w m:ℕ}
-- EXACT version of H2 valuation (the scalar errors would also suffice).
variable (p₀:PressB P X Q a c)(z:0≤a)(uX:Nonwrapping X.val.2 X.val.1)(uH:10 ≤ (More n).val)(H:VanishGE Q P X.val.1 w)(w':w ≤5)
include p₀ z uX uH H w'
local notation "Xₚ"=> X.val.2
local notation "aₚ"=> X.val.1
set_option maxHeartbeats 400000 in
lemma extinction (L:ℂ→L[ℝ]ℝ) : Mediator.valence (fun i=> (Mom.Maps aₚ Xₚ i (G:=GS):Set _)) w (L ∘ term Q):=by
 let K(i):=(Mom.Sites aₚ Xₚ i (G:= SU.group) (d:=5):Set (Mom.Slate SU.group (More n) 5)) -- tune (More n)
 let D(i):=(Mom.Maps aₚ Xₚ i (G:= SU.group):Set (RG.Directions SU.group (More n)))
 let f:= lifeH Q; let q:= optic Xₚ aₚ (d:=5) (G:=SU.group); let g:= L ∘ f; let F:=g ∘ increment 1
 have hn:2 ≤ (More n).val:= (by omega)
 have ht:= (cashR Q X p₀ z L _ le_rfl).regular
 have hq : (pintK P).Regular Xₚ g:= ht
 have hc : ContDiffAt ℝ (w:ℕ∞ω) F 0:= (hq.smooth 1 (flat_ok ..)).of_le (Nat.cast_le.mpr (w'.trans ((by decide:5≤6).trans P.order_ge)))
 obtain ⟨hv,hp⟩:= Mom.osmotic Xₚ aₚ (G:=SU.group) (d:=5); have hC : Mediator.curry K D w q:= along aₚ Xₚ hn uX
 apply Mediator.attenuation K D q F (hv.of_le le_top) hp hc (fun i hi h=> covers aₚ Xₚ uX hn i hi (h.trans w')) hC
 let e:=hol SU.group; letI:NormedAddCommGroup (Mom.Slate SU.group (More n) 5):=inferInstanceAs (NormedAddCommGroup ((Skye.Seat n→ SU.group.Color) × Snap SU.group 5)); letI:NormedSpace ℝ (Mom.Slate SU.group (More n) 5):= inferInstanceAs (NormedSpace ℝ ((Skye.Seat n→ SU.group.Color) × Snap SU.group 5))
 have hx: ((fun x=>(g x:ℂ)) ∘ increment 1) ∘ q=ᶠ[𝓝 (0:Mom.Slate SU.group (More n) 5)] (fun v=> (g (e.testLinks 5 aₚ (expand 5 v.2) 1):ℂ)):= Mom.appears (fun u v h=>congrArg Complex.ofReal (hq.sites u v h)) (fun t x=> congrArg Complex.ofReal (hq.symmetry t x)) _
 let π: Mom.Slate SU.group (More n) 5 →L[ℝ] Mom.Slate SU.group (More n) 5:= (ContinuousLinearMap.inr ..).comp (ContinuousLinearMap.snd ..)
 have hP: F ∘ q=ᶠ[𝓝 0] (F ∘ q) ∘ π:=by filter_upwards [hx,hx.comp_tendsto (show Tendsto π (𝓝 0) (𝓝 0) from (by simpa using π.continuous.tendsto 0))] with v hv hj; exact Complex.ofReal_inj.mp (hv.trans hj.symm)
 have hD:ContDiffAt ℝ (w:ℕ∞ω) (F ∘ q) 0:= (show ContDiffAt ℝ (w:ℕ∞ω) F (q 0) from (by rw [show q 0=0 from hp]; exact hc)).comp 0 (hv.of_le le_top)
 have hJ := Work.F03.hessian_comp hp (germ_diff hq) (hv.of_le le_top) (flat_critical Thera.yet_one hq)
 intro m a u hA
 by_cases h:∃ i,a i≤1
 · obtain ⟨i,w⟩:= h; have hy: π (u i) = 0:=Prod.ext rfl (funext fun j=> ((hA.1 i).2.2 j (by omega)))
   have hm : m≤ _:=le_trans (by simpa using (Finset.sum_le_sum (s:=Finset.univ) (f:=fun _=> 1) (fun j _=> (hA.1 j).1))) hA.2
   rw [(hP.iteratedFDeriv (𝕜:=ℝ) m).eq_of_nhds,jets_linear π (hD.of_le (Nat.cast_le.mpr hm)),ContinuousMultilinearMap.compContinuousLinearMap_apply]; exact ContinuousMultilinearMap.map_coord_zero _ i hy
 have hU(i): 2 ≤ a i := by have h:=not_exists.mp h i; omega
 have hm : m*2 ≤ w:= le_trans (by simpa using Finset.sum_le_sum (s:=univ) (f:=fun _=> 2) (fun j _=>hU j)) hA.2
 have hV(i:Fin m): fderiv ℝ q 0 (u i)∈Maps aₚ Xₚ (a i):=by
    have he:a i≤w:=(single_le_sum (s:=univ) (f:=a) (fun i _=> Nat.zero_le _) (mem_univ i)).trans hA.2
    let j:= (fun _: Fin 1=>a i); have hx:∑ i:Fin 1,j i=a i:=by simp [j]; -- cyclic binder tune
    have hy:= hC 1 one_pos j (fun _=>u i) ⟨fun _=>hA.1 i,hx.le.trans he⟩; rw [hx,iteratedFDeriv_one_apply] at hy; exact hy
 cases m with
 |zero=>rw [iteratedFDeriv_zero_apply]; change F (q 0)=0; rw [show q 0=0 from hp]; unfold F; rw [Function.comp_apply,at_zero]; exact (congrArg L H.unit).trans (map_zero _)
 |succ m=>
    by_cases he:m=0; · subst m; rw [iteratedFDeriv_one_apply,show fderiv ℝ (F ∘ q) 0=0 from hJ.1]; rfl
    have hg : m=1:=by omega
    subst m
    rw [show u= ![u 0,u 1] from funext (fun i=>by fin_cases i<;>rfl),show iteratedFDeriv ℝ 2 _ _ _= _ from hJ.2 (u 0) (u 1)];
    change logHessian (L ∘ lifeH Q) (fderiv ℝ q 0 (u 0)) (fderiv ℝ q 0 (u 1))=0; rw [←ploy_value p₀ z,perch p₀ z uX uH H _ _ (a 0) (a 1) (hU 0) (hU 1) _ w' (hV 0) (hV 1), map_zero]; exact (Fin.sum_univ_two a).symm.le.trans hA.2
lemma flat_fossil(a: Fin m→ℕ)(x:Fin m→ tangD n)(h:∀ i,0<a i∧ Mom.screen Xₚ (x i)∈ Mom.Maps aₚ Xₚ (a i))(v:∑ i,a i≤w): iteratedFDeriv ℝ m (term Q) 0 x=0:=by
 have hm: m ≤P.order:= (le_trans (by simpa using Finset.sum_le_sum (s:=univ) (f:=fun _=>1) (fun j _=> (show 1 ≤ a j from (h j).1))) v).trans (w'.trans ((by decide: 5≤6).trans P.order_ge))
 have ht:= (eraF Q X p₀ z 1 (ping_f P Xₚ)).paid; let Y:=Mom.screen (G:=SU.group) Xₚ; have he : term Q = term Q ∘ Y:= funext (fun x=> congrArg Pastry.pane (p₀.term _ _ (fun i p v=> by change _=SU.group.lieExp _* _; rw [show Y x i=x i from (by unfold Y; rw [screen_at]; exact if_pos (show needed _ _ from ⟨p,v⟩))]; rfl))) -- tune portD
 have hx(L:ℂ→L[ℝ]ℝ) : L (iteratedFDeriv ℝ m (term Q) 0 x)= L (0:ℂ):=by
    have hy: L ∘ term Q=(L ∘ term Q) ∘ Y:=by
       conv_lhs=> rw [he]
       rfl
    calc _=iteratedFDeriv ℝ m (L ∘ term Q) 0 x:=by rw [L.iteratedFDeriv_comp_left (f:=term Q) ht (Nat.cast_le.mpr hm)]; rfl
         _=iteratedFDeriv ℝ m (L ∘ term Q) 0 (Y ∘ x):=by nth_rw 1 [hy]; rw [jets_linear Y (L.contDiff.contDiffAt.comp (f:=term Q) _ (ht.of_le (Nat.cast_le.mpr hm)))]; rfl
         _=_:=by rw [extinction p₀ z uX uH H w' L _ a (Y ∘ x) ⟨h,v⟩, map_zero]
 exact Complex.ext (hx Complex.reCLM) (hx Complex.imCLM)
-- arbitrary fourth-weight case ≤5 comes with only one other arg. gradient against any second by first order. 
set_option maxHeartbeats 70000 in
lemma fossilP (k:Fin m→ℕ)(x:Fin m→ tangD n)(u:∀ i,1≤k i)(h:∀ i,k i ≤3→Blade (k i) X (x i))(v:∑ i,k i ≤ w): iteratedFDeriv ℝ m (term Q) 0 x=0:=by
 by_cases p: ∃ i,3 < k i; swap
 · exact flat_fossil p₀ z uX uH H w' k x (fun i=> ⟨u _,let p':=le_of_not_gt (not_exists.mp p i); blade_pay p' (u _) (h i p')⟩) v
 obtain ⟨i,q⟩:=p
 have hp : 3 + m ≤w:=by
    have he:=Finset.card_erase_add_one (mem_univ i); have ht:=(Finset.sum_le_sum (s:=univ.erase i) (f:=fun _=> 1) (fun j _=> u j)); rw [←Finset.add_sum_erase _ _ (mem_univ i)] at v
    simp only [Fintype.card_fin,Finset.card_univ] at he; simp only [sum_const, smul_eq_mul,mul_one] at ht
    omega
 have hL : 0 < m:= i.pos -- parser
 match m with
 | 0 => omega
 | 1=>
    have h(L:ℂ→L[ℝ]ℝ): L (iteratedFDeriv ℝ 1 (term Q) 0 x)= L (0:ℂ):=by
       rw [show L _= _ from (show L (iteratedFDeriv ℝ 1 (term Q) 0 x)= iteratedFDeriv ℝ 1 (L ∘ term Q) 0 x from (by rw [L.iteratedFDeriv_comp_left (f:=term Q) (eraF _ _ p₀ z 1 (ping_f P _)).paid (Nat.cast_le.mpr ((by decide:1≤6).trans P.order_ge))]; rfl)), iteratedFDeriv_one_apply,show fderiv ℝ (L ∘ term Q) 0=0 from flat_critical Thera.yet_one ((cashR _ X p₀ z L _ le_rfl).regular), map_zero]; rfl
    exact Complex.ext (h Complex.reCLM) (h Complex.imCLM)
 | 2=>
    have hm: k 0+k 1 ≤w:=by simpa only [Fin.sum_univ_two] using v
    rcases show k 0=1∨k 1=1 by fin_cases i <;> dsimp at q <;> have h₀:= u 0 <;> have h₁:=u 1 <;> omega with e|e
    · exact (congrArg (iteratedFDeriv ℝ 2 (term Q) 0) (show x = ![x 0,x 1] from funext fun i=>by fin_cases i<;>rfl)).trans ((ploy_iter Q (x 0) (x 1)).symm.trans (ζball p₀ z uX uH _ (by have ht:=h 0 (show k 0≤3 from by omega); change Blade 1 X (x 0); apply Eq.mp _ ht; exact congrArg (fun i=> Blade i X (x 0)) e) _))
    exact (congrArg (iteratedFDeriv ℝ 2 (term Q) 0) (show x = ![x 0,x 1] from funext fun i=>by fin_cases i <;> rfl)).trans ((ploy_iter Q (x 0) (x 1)).symm.trans ((ploy_herm p₀ z (x 0) (x 1)).trans (ζball p₀ z uX uH _ (by have ht:=h 1 (show k 1≤3 from by omega); change Blade 1 X (x 1); apply Eq.mp _ ht; exact congrArg (fun i=>Blade i X (x 1)) e) _)))
 | m+3=> omega
end Axon
end YM.CF.TableF
end
