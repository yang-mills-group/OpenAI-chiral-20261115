import GaugeFieldConstruction.Ablated
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 70000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi Lenten Flot
open Bank Laurent Bloch Tap Hove Spire Haro
namespace Boom
open TableF.Axon Siete Lenten.ModuleB MultiNext.SignedSource Lyre Banjo Analysis
variable {f:Side}{Z:Scree.Hub f}{P:BudgetPoint}{h c s δ v ξ:ℝ}{Q:InkD f}{g:Finset (Dwell f)→ℝ}{U:tangD f}{X:Scree.Hub f}{m:ℕ}
variable (t: Chamber X P U)(P₀:PressB P X Q h c)(W:Nonwrapping X.val.2 X.val.1)(V:∀ U,BedP P U Q X g)(D:∀ i,0≤ g i)
include t P₀ W V D
lemma elder_d (F:Fin m→ tangD f)(p:m < 6)(e:‖U‖≤ξ*P.threshold)(v:∀ i,Sized s (F i) P X.val.1): Rode X.val.1 (xHoch 6*(ξ*s^m)) (Zinc g) (mastX Q U F-mastX Q 0 F):=by
 have hp: ∀ (r : ℝ), r∈Set.Icc (0:ℝ) 1 → pingS P.threshold X.val.2 (increment 1 (r • U)):=t.2
 refine ⟨fun i j u=>?_, fun ⟨i,j⟩=>?_⟩
 · by_cases h:mastX Q U F i j=0; · exact mast_support (x:=0) P₀ W _ _ _ (fun e=> u (by rw [Matrix.sub_apply,h,e,sub_zero]))
   exact mast_support P₀ W _ _ _ h
 rw [Matrix.sub_apply]; have hb:= chamber_B (F:=fun V=>orbitPH (Q V) i j) U t F (fun _=>s) p (fun i' e=> Prism.sent _ _ i.1 j.1 (V _) (hp i' e) D i.2 j.2) (fun u v h=> congrArg (fun x=>orbitPH x i j) (P₀.term u v h)) e v; -- tune
 rw [prod_const,card_univ,Fintype.card_fin] at hb; exact hb
omit t V D
include V D
lemma cull_D (F Y:tangD f)(e:0 ≤ δ)(p:∀ j, Mom.needed X.val.2 j→ ‖F j-Y j‖≤δ*P.threshold):Rode X.val.1 δ (Zinc g) (Paint Q F-Paint Q Y):=by
 let S:=Mom.screen X.val.2 (F-Y); have ht:Paint Q F-Paint Q Y=Paint Q S:=by
    rw [show Paint Q F-Paint Q Y=Paint Q (F-Y) from ((panLinear Q).map_sub F Y).symm]; ext i j; apply (booth_grad P₀ i.1 j.1 i.2 j.2 _ _ _); intro i p u; exact (Mom.screen_at ..).trans (if_pos (And.intro p u))|>.symm
 rw [ht]; have hp:=mast_hunt P₀ W D V ![S] (t:=fun _=>δ) (fun i=> by fin_cases i; exact local_veil _ e (F-Y) p) ((by omega:1≤6).trans P.order_ge); rw [mast_Ψ,Fin.prod_univ_one] at hp; exact hp
omit V D W P₀
lemma hull_P (F:tangD f)(u:0 ≤ s)(q:Blade 1 X F)(h:∀ i,Mom.needed X.val.2 i→ ‖F i‖≤ s*P.threshold): PollenG P X s F 1:=by
 obtain ⟨L,f',p⟩:=q; let Q(i:Axis):Prop:=∃ j:Lattice.Edge (Site (More f)), Mom.needed X.val.2 j ∧ j.2=i -- tune f shadow
 choose C hC using fun i:Axis=>(paper_firm ..).1 (f' i)
 let U(i):= if Q i then C i else 0; let F'(i:Axis)(_:Cover):=U i
 refine ⟨F',⟨fun j l u=> ?_,fun j=>?_⟩,fun i=>paper_const _,fun i j=>?_⟩
 · rw [← p j l u]; unfold camW F' U; rw [hC, if_pos]; exact ⟨j,⟨l,u⟩,rfl⟩
 · unfold F' U; split; next g=>
       obtain ⟨l,w,v⟩:=g; rw [←v]; apply le_trans _ (h l w); apply le_of_eq; rw [← p _ w.1 w.2]; unfold camW; rw [hC];
   rw [norm_zero]; exact mul_nonneg u P.threshold_pos.le
 rw [show advance i (F' j)=0 from advance_const ..,Pi.zero_apply,norm_zero]; exact mul_nonneg u P.threshold_pos.le
include t P₀ V
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma Port_map {K:E→tangD f} {y:E} (l: ContDiffAt ℝ (6:ℕ∞ω) K y)(v:U=K y) : ContDiffAt ℝ (6:ℕ∞ω) (fun x=>orbitPH (Q (increment 1 (K x)))) y:=by
 let X:=fun i=> orbitPH (Q (increment 1 (K i)))
 have ht:=t.2 1 (by simp); rw [one_smul,v] at ht; let A:=Nacre.coordL (k:=Single f)
 have hz:ContDiffAt ℝ (6:ℕ∞ω) (A ∘ X) y:= contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr fun j=> (PortProof P₀ V (K y) ht i j).comp y l
 simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using (A.symm.contDiff.contDiffAt.comp y hz)
lemma Port_diff {K:E→tangD f} {y:E}(l: ContDiffAt ℝ (6:ℕ∞ω) K y)(v:U=K y) (z:E): fderiv ℝ (fun x=>orbitPH (Q (increment 1 (K x)))) y z=mastX Q U ![fderiv ℝ K y z]:=by
 have hv:= Port_map t P₀ V l v; ext i j; let P':= (show Op (Single f)→ₗ[ℝ]ℂ from ⟨⟨fun x=> x i j,fun i j=>rfl⟩,fun _ _=>rfl⟩).toContinuousLinearMap
 have ht:= (PortProof P₀ V _ (show pingS P.threshold X.val.2 (increment 1 U) from (by simpa only [one_smul] using t.2 1 (by simp))) i j).differentiableAt (by norm_num)
 let F:=fun i=> orbitPH (Q (increment 1 (K i)))
 have hp: P' (fderiv ℝ F y z)= fderiv ℝ (portE Q i j ∘ K) y z:=by
    exact ((show fderiv ℝ (portE Q i j ∘ K) y= P'.comp (fderiv ℝ F y) from (fderiv_comp (f:=F) (g:=P') y P'.differentiableAt (hv.differentiableAt (by norm_num)))|>.trans (congrArg (fun x=>ContinuousLinearMap.comp x (fderiv ℝ F y)) P'.fderiv)).symm ▸ rfl) -- tune
 change P' ((fderiv ℝ F y) z)=_; rw [hp, mastX, Matrix.of_apply, fderiv_comp y (v ▸ ht) (l.differentiableAt (by norm_num)), iteratedFDeriv_one_apply,v]; rfl
end Boom
end YM.CF.TableF
end
