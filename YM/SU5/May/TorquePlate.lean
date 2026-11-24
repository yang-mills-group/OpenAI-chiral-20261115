import YM.SU5.May.FloeLaps
import YM.SU5.May.TorqueCarry
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
local notation "T" n:max => Therapies.paceFloor Y H G n
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
private lemma gauge_anchor (n : Side)(x:Cover)(i:SpinIdx)(b:SU.Slot)(p:nodeC x∈ U): withinM (modesIn n (U.image (wrap (More n)))) (basisC n x i b) := by
 have he : Lifted.index n x i b ∈ modesIn n (U.image (wrap (More n))) := by rw [modes_at]; change node (wrap n x) ∈_; rw [node_of]; exact mem_image_of_mem _ p
 unfold withinM basisC; rw [map_smul,within_basis _ _ he]
open Whorl Flare
variable {P:Ramp} {N P': Side}
private lemma legroom (x:Cover)(i:SpinIdx)(b:SU.Slot):‖basisC N x i b‖=1:=by unfold basisC; rw [norm_smul]; simp [basisKet,Lifted.winding,Rush.fee_norm]
variable {c:ℝ}
private lemma roomone {S:Finset (Single N)}{w:ℂ} (h:‖w‖≤c): w • (1:FC (Single N))∈ Capital (Tset N) S false 0 1 c:= capitalNil h where
 capitalNil(h:‖w‖≤c):=Capital.oneWord (C:=[]) (show Headboard (Tset N) S false 0 1 [] from ⟨by simp,le_rfl,rfl⟩) h
private lemma roomtiny {S: Finset (Single N)}{v:Reader0 (Single N)}(h:Worth (Tset N) S 1 v): ton v∈ Capital (Tset N) S true 1 1 1:=by simpa only [one_smul,rollC,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using Capital.oneWord (w:=1) (show Headboard (Tset N) S true 1 1 [v] from ⟨by simpa,le_rfl,rfl⟩) (le_of_eq (by simp))
lemma faresL {C:Calibration}{k r:Bool}{f:Family C} (p: InTest C r U k f): ∃ (κ:ℕ)(c:ℝ),0≤c ∧ ∀ (m:Side) x,f m x ∈ Capital (Tset (C.c m)) (modesIn (C.c m) (Satin.region U (C.c m))) k κ 1 c:=by
 induction p with
 | @seed f p=>obtain ⟨C,hC⟩:=p.env.cost; exact ⟨0,|C|,abs_nonneg _, fun _ x=> roomone ((hC _).trans (le_abs_self _))⟩
 | @creator x i b p v=>
    refine ⟨1,1,zero_le_one,fun m y=> roomtiny (v:=(false,basisC _ x i b)) ⟨?_,gauge_anchor (C.c m) x i b v,(legroom x i b).le⟩⟩; change withinM (Tset _) _; unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index _ x i b) ((mem_Tset ..).mpr p)]
 | @remover x i b p v=>
    refine ⟨1,1,zero_le_one,fun m y=> roomtiny (v:=(true,basisC _ x i b)) ⟨?_,gauge_anchor (C.c m) x i b v,(legroom x i b).le⟩⟩; change withinM (Tset _)ᶜ _; unfold withinM basisC; rw [map_smul, within_basis (Tset _)ᶜ (Lifted.index _ x i b) (Finset.mem_compl.mpr fun h=> p ((mem_Tset ..).mp h))]
 | one=> exact ⟨0,1,zero_le_one,fun m y=>by simpa only [Pi.one_apply,one_smul] using roomone (N:=C.c m) (S:=modesIn (C.c m) (Satin.region U (C.c m))) (le_of_eq (norm_one (α:=ℂ)))⟩
 | zero=>exact ⟨0,0,le_rfl,fun m y=> capital_zero le_rfl⟩
 | add _ _ ih il=> obtain ⟨v,a,g,h⟩:= ih; obtain ⟨t,b,q,l⟩:=il; exact ⟨v+t,a+b,add_nonneg g q,fun m z=> capital_add (capital_le (Finset.Subset.refl _) le_rfl le_rfl (by omega) (h m z)) (capital_le (Finset.Subset.refl _) le_rfl le_rfl (by omega) (l m z))⟩
 | mul _ _ ih il=> obtain ⟨v,a,g,h⟩:=ih; obtain ⟨t,b,q,l⟩:=il; exact ⟨v+t,a*b,mul_nonneg g q,fun m y=> capital_mul (h m y) (l m y)⟩
 | smul a _ ih=> obtain ⟨v,b,q,h⟩:=ih; exact ⟨v,‖a‖*b,mul_nonneg (norm_nonneg _) q,fun m y=> capital_smul (h m y) _⟩
private lemma capTransport {κ:ℕ} {ρ A:ℝ}{m n:Side}(p:m=n){f:Mark m}{b:Bool} (h:Maintain m b κ ρ A (Satin.region U m) f): Maintain n b κ ρ A (Satin.region U n) (arrange m n p f):= by subst n; exact h
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (s m t:ℕ) {U V': Finset Cover}
lemma startingFees {g:Family (tent Y H)}{b:Bool} (h:InTest (tent Y H) true U b g): ∃ (κ:ℕ)(A:ℝ),0 ≤ A ∧∀ (s m:ℕ), Maintain (Journey.side Y m s) b κ 1 A (Satin.region U (Journey.side Y m s)) (exhibit Y H s m g):= by
 obtain ⟨k,t,u,g'⟩:=faresL h
 exact ⟨k,t,u, fun s i=> capTransport (terrain Y H (Y.ir i) s) (fun x=>subset_closure (g' (momentm Y i s) x))⟩
#print axioms startingFees
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
