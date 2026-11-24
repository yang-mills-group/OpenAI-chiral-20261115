import GaugeFieldConstruction.SupremeΑppN
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}{p:BudgetPoint}{u h t:ℝ}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
open Buffered.Afterglow.Tower.VacuumSelection Buffered.Afterglow Buffered.Afterglow.Six Buffered.Afterglow.Tower Tapestry RG Satin
variable {K:Calibration} {X Y:Finset Cover}{F:Dome K}{E: Dome K→ₗ[ℂ]ℂ}
-- direct raw illumination, point-support diagnosis. Works through any measurement that keeps EXACT endpoint disjointness on native cover at resolution in use. Need not be pin-apart internally! Not use for higher advancements beyond that in issuing.
include F in
lemma matterszeroN {mB:ℂ}{g:Cover→SU.E}(u:Factors K E)(v:MatterWard K E)(p: F∈ illuminated K g mB)(w:mB≠1) : E F=0:=by
 refine Submodule.span_induction (p:=fun f _=> E f=0) (fun f i=>?_) (map_zero E) (fun _ _ _ _ x y=>by rw [map_add,x,y,add_zero]) (fun i _ _ x=>by rw [map_smul,x,smul_zero]) p; obtain ⟨f,x,y,h,t,a⟩:=i; subst_vars; have ht:= v g x h; rw [t,map_smul,smul_eq_mul] at ht; have he:E x=0:=Classical.byContradiction (fun e=> w (mul_right_cancel₀ e (ht.trans (one_mul _|>.symm)))); rw [u _ _ y h,he,mul_zero]
variable {x:Cover}{d:ℕ}
-- any separated PH leg (species or generations not equal, works basiswise without single-term enclave proof). kill by center gauge on removal endpoint. split prices require MatterWard only.
lemma pocketingN (w:jungle x d)(A:PairsC→ℂ)(p:Coeff true X A)(e:w≠none)(h:inkB w)(q:cartO x d⊆ X):∃ (f:Dome K)(g:Cover→SU.E)(B:ℂ),B≠1 ∧ (∀ z,z∉X → g z=1) ∧ f.val = scalar K A * showroom K w ∧ f∈ illuminated K g B:=by
 let G:Dome K:= ⟨scalar K A, broadCompile K X (InTest.seed p)⟩
 rcases w with _|⟨b,i,j⟩; · contradiction
 obtain ⟨p0,h0,v⟩:=h
 have hx(i:mort x d):nodeC i.1.val∈ X:=q ((ridge_spec _).1 i.1.property)
 have hz:nodeC i.1.val ≠ nodeC j.1.val:= fun p=> v (nsmul_right_injective two_ne_zero (add_right_cancel p)) -- tune
 cases b
 · let g:Cover→ SU.E:=fun x=> if x=nodeC i.1.val then SU.central else 1; let A':=removal K i.1.val i.2.1 i.2.2; let B:=creation K j.1.val j.2.1 j.2.2; let θ:= phaseName (family i.2.2).2
   have hr:=pocket_removal K (family i.2.2).2 X (hx i) rfl (fun v=>Bool.noConfusion (p0.mpr v))
   have hc:=pocket_creation K (family j.2.2).2 X (hx j) rfl (h0.mp rfl)
   obtain ⟨e,f⟩:= pocket_test _ _ _ _ hr
   obtain ⟨l,w⟩:= pocket_test _ _ _ _ hc
   let F:Dome K:= ⟨A'*B,broadCompile K X (.mul e l)⟩
   have hM:= creation_fixed K _ ({nodeC j.1.val}:Finset Cover) g (fun i z=>by rw [mem_singleton.mp z]; exact if_neg (Ne.symm hz)) (pocket_creation _ (family j.2.2).2 _ (mem_singleton_self _) rfl (h0.mp rfl)) -- tune
   have hf:= removal_center K _ ({nodeC i.1.val}:Finset Cover) g (fun i z=>if_pos (mem_singleton.mp z)) (pocket_removal _ (family i.2.2).2 _ (mem_singleton_self _) rfl (fun u=> Bool.noConfusion (p0.mpr u)))
   have hh: Circular X g (A'*B) (θ • (A'*B)):=by rw [←Algebra.smul_mul_assoc]; exact Circular.mul g X (largerGauge (singleton_subset_iff.mpr (hx i)) hf) (largerGauge (singleton_subset_iff.mpr (hx j)) hM)
   exact ⟨G*F,g,θ,pname_ne _,fun z u=> by unfold g; rw [if_neg fun (v:z=nodeC i.1.val)=> u (v ▸ hx i)],rfl,Submodule.subset_span (show _∈_ from ⟨G,F,⟨X,A,p,rfl⟩,LinkIndependent.mul' f w, appointed K X g _ _ hh (show InTest K true X false (θ • (A'*B)) from .smul θ (.mul e l)),rfl⟩)⟩
 let g:Cover→ SU.E:=fun x=> if x=nodeC j.1.val then SU.central else 1; let A':=removal K j.1.val j.2.1 j.2.2; let B:=creation K i.1.val i.2.1 i.2.2; let θ:= phaseName (family j.2.2).2
 have hr:=pocket_removal K (family j.2.2).2 X (hx j) rfl (fun t=>Bool.noConfusion (h0.mpr t))
 have hc:=pocket_creation K (family i.2.2).2 X (hx i) rfl (p0.mp rfl)
 obtain ⟨e,f⟩:= pocket_test _ _ _ _ hr
 obtain ⟨l,w⟩:= pocket_test _ _ _ _ hc
 let F:Dome K:= ⟨B*A',broadCompile K X (.mul l e)⟩
 have hM:= creation_fixed K _ ({nodeC i.1.val}:Finset Cover) g (fun i z=>by rw [mem_singleton.mp z]; exact if_neg hz) (pocket_creation _ (family i.2.2).2 _ (mem_singleton_self _) rfl (p0.mp rfl))
 have hf:= removal_center K _ ({nodeC j.1.val}:Finset Cover) g (fun i z=>if_pos (mem_singleton.mp z)) (pocket_removal _ (family j.2.2).2 _ (mem_singleton_self _) rfl (fun u=> Bool.noConfusion (h0.mpr u)))
 have hh: Circular X g (B*A') (θ • (B*A')):=by rw [←Algebra.mul_smul_comm]; exact Circular.mul g X (largerGauge (singleton_subset_iff.mpr (hx i)) hM) (largerGauge (singleton_subset_iff.mpr (hx j)) hf)
 exact ⟨G*F,g,θ,pname_ne _,fun z u=> by unfold g; rw [if_neg fun (v:z=nodeC j.1.val)=> u (v ▸ hx j)],rfl,Submodule.subset_span (show _∈_ from ⟨G,F,⟨X,A,p,rfl⟩,LinkIndependent.mul' w f, appointed K X g _ _ hh (show InTest K true X false (θ • (B*A')) from .smul θ (.mul l e)),rfl⟩)⟩
#print axioms matterszeroN
#print axioms pocketingN
end ArtCart
end MastTin
end YM.CF.XGarden
end
