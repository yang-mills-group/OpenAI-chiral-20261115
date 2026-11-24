import GaugeFieldConstruction.MarinStockNX
-- permanent charges. reads even after issuing, all heights.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Ballad Six Glaze
variable (P:Spine){n:ℕ}(A:Lead n)(k:VFlavorNX)(j w:Fin 2)
local notation "K"=> P.calibration
open Lamour.Bridge.Celeste
lemma familySNX (p:SU.Slot): (family p).2=YM.GaugeFieldConstruction.Flavor.tagged p.2:=by rcases p with ⟨x,u|l⟩ <;> exact rfl -- casing
private lemma vc_rayNX {p q:SU.Slot}(h:bookColorNX k p q≠0): p∈colors (k.2.1,k.1) ∧ q∈colors (k.2.2,k.1):=by
 rw [bookColorNX,YM.GaugeFieldConstruction.Flavor.wear] at h
 split at h; swap; · contradiction
 next u=>
   have hp: (YM.GaugeFieldConstruction.Flavor.tagged p.2,p.1,q.1)=k:= Classical.byContradiction fun t=> h (Pi.single_eq_of_ne t _)
   refine ⟨Finset.mem_filter.mpr ⟨mem_univ _,Prod.ext (congrArg (Prod.fst ∘ Prod.snd) hp) ((familySNX _).trans (congrArg Prod.fst hp))⟩,Finset.mem_filter.mpr ⟨mem_univ _,Prod.ext (congrArg (Prod.snd ∘ Prod.snd) hp) ((familySNX _).trans ((congrArg YM.GaugeFieldConstruction.Flavor.tagged u.symm).trans (congrArg Prod.fst hp)))⟩⟩
-- Matter second multiplication commutes its sector.Natural.
lemma VLead_PNX {p q:SU.Slot}{X:SU.E}(h:Lead.VLeadNX k X p q≠0): p∈colors (k.2.1,k.1) ∧ q ∈colors (k.2.2,k.1):=by
 constructor
 · by_contra! v; apply h; unfold Lead.VLeadNX; rw[Matrix.mul_apply]; apply sum_eq_zero; intro j _; apply mul_eq_zero_of_left _ _; exact not_ne_iff.mp fun V=> v (vc_rayNX k V).1
 by_contra! v
 apply h
 unfold Lead.VLeadNX; rw [←show (matter X).val * bookColorNX k= _ from YM.GaugeFieldConstruction.Matter.coeff_ok (Pi.single k 1) X]
 rw [Matrix.mul_apply]; apply sum_eq_zero; intro i _; apply mul_eq_zero_of_right _ (not_ne_iff.mp fun q=> v (vc_rayNX k q).2)
lemma flipsPNX(N:Side)(p q:SU.Slot): create (A.highlightNX j N p)* Fock.remove (A.lowlightNX w N q)= -(Fock.remove (A.lowlightNX w N q)*create (A.highlightNX j N p)) :=by
 unfold Lead.highlightNX Lead.lowlightNX basisC Fock.remove; simp only [map_smul,create_put,star_smul,Matrix.smul_mul,Matrix.mul_smul]
 have he: Lifted.index N A.death (dnSpin w) q≠Lifted.index N A.birth (upSpin j) p:=fun h=> dn_half w ((show dnSpin w=upSpin j from congrArg (fun t:Single N=> t.1.2) h).symm ▸ up_half j)
 rw [show star (Fock.put _)*Fock.put _= _ from eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg he)),smul_neg,smul_neg,smul_comm]; simp
abbrev integralPostNX (p q:SU.Slot): LinksC→ℂ:= fun x=> Lead.VLeadNX k (travel x (nodeC A.birth) A.traceV) p q
lemma conductorNX(p q: SU.Slot):Coeff false A.patio (integralPostNX A k p q∘Prod.fst):=Coeff.fromC _ _ ((continuous_const (y:=bookColorNX k)).mul (matter_cont.comp (Wilson.continuous_travel A.traceV (nodeC A.birth)))|>.matrix_elem p q) (fun X Y h=> congrArg (fun t:SU.E=>Lead.VLeadNX k t p q) (travel_local _ _ X Y (fun e u v=> h e (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v))))
abbrev glyphFNX(p q:SU.Slot): Buffered.Family P.calibration:= scalar P.calibration (integralPostNX A k p q∘Prod.fst)*(removal P.calibration A.death (dnSpin w) q * creation P.calibration A.birth (upSpin j) p)
local notation "S"=> Finset.singleton (nodeC A.birth)
local notation "T"=> Finset.singleton (nodeC A.death)
lemma bookFlareNX (N:Side)(V:Fields N): A.rollNX k j w N V=
  -∑ i∈colors (k.2.1,k.1),∑ l∈colors (k.2.2,k.1),(integralPostNX A k i l (onC N V.1)) • (Fock.remove (A.lowlightNX w N l)*create (A.highlightNX j N i)) :=by
 unfold Lead.rollNX; simp_rw[flipsPNX A j w,smul_neg,sum_neg_distrib]
 let f(i l:SU.Slot):= Lead.VLeadNX k (A.laps V.1) i l • (Fock.remove (A.lowlightNX w N l)* create (A.highlightNX j N i)); change -(∑ i:SU.Slot,∑ l:SU.Slot, f i l)= -(∑ i∈ colors (k.2.1,k.1),∑ l∈ colors (k.2.2,k.1),f i l)
 congr 1; symm
 apply Eq.trans _ (sum_subset (f:=fun i=>∑ l,f i l) (subset_univ (colors (k.2.1,k.1))) ?_)
 · apply sum_congr rfl; intro i u; apply sum_subset (subset_univ _); intro l _ v; unfold f; rw [not_ne_iff.mp (fun q=>v (VLead_PNX k q|>.2)),zero_smul] -- type needs specif
 intro i _ p; apply sum_eq_zero; intro l _; unfold f; rw [not_ne_iff.mp (fun q=>p (VLead_PNX k q|>.1)),zero_smul]
lemma forecastBornNX : Papal.household P.calibration (A.rollNX k j w)= - ∑ p∈colors (k.2.1,k.1),∑ q∈colors (k.2.2,k.1), P.glyphFNX A k j w p q:=by
 funext m x
 have h(p q:SU.Slot): (P.glyphFNX A k j w p q) m x=integralPostNX A k p q (onC _ x.1) • (Fock.remove (A.lowlightNX w _ q)*create (A.highlightNX j _ p)):=by
    -- multiplicative costs
    let s:= integralPostNX A k p q (onC _ x.1)
    let Y:=Fock.remove (A.lowlightNX w (P.calibration.c m) q)*create (A.highlightNX j (P.calibration.c m) p)
    change (s • (1:FC (Single (P.calibration.c m)))) * Y=s • Y
    rw[Algebra.smul_mul_assoc,one_mul]
 rw [show Papal.household K (A.rollNX k j w) m x= A.rollNX k j w (P.calibration.c m) x from rfl]
 simp only [Pi.neg_apply, Finset.sum_apply,h]; exact bookFlareNX A k j w _ x -- explicit?
lemma dressPNX : Papal.household P.calibration (A.rollNX k j w) ∈ DressedPair P.calibration k.1 {nodeC A.birth} {nodeC A.death} A.patio:= by
 rw[P.forecastBornNX]; apply Submodule.neg_mem
 refine Submodule.sum_mem _ (fun i p=> Submodule.sum_mem _ (fun l u=> Submodule.subset_span (show _∈_ from ?_)))
 have hu:=conductorNX A k i l
 have hr:=pocket_removal K k.1 {nodeC A.death} (x:=A.death) (mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp u).2) (dn_half w)
 have hc:=pocket_creation K k.1 {nodeC A.birth} (x:=A.birth) (mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp p).2) (up_half j)
 exact ⟨_,⟨fun v=>by contradiction, hu.env,hu.locus⟩,_, Submodule.subset_span (show (removal K A.death (dnSpin w) l* creation K A.birth (upSpin j) i) ∈ _ from ⟨_,hr,_,hc,rfl⟩),rfl⟩ -- implicit
lemma baysPNX : InTest K true A.patio false (Papal.household K (A.rollNX k j w)):=dressed_test K k.1 _ _ _ (Finset.union_subset (Finset.singleton_subset_iff.mpr (porchBorn A)) (Finset.singleton_subset_iff.mpr (porchGone A))) (P.dressPNX A k j w)
noncomputable def dressPuffNX: P.Test:= ⟨_,broadCompile K A.patio (P.baysPNX A k j w)⟩
lemma useFootPNX : P.dressPuffNX A k j w ∈bay K A.patio true:= (locates K A.patio true).mpr (P.baysPNX ..)
lemma nativePNX : P.dressPuffNX A k j w∈enclave K:= (enclave_spec K).mpr fun m=> (A.lawNX k j w (N:=P.calibration.c m))
lemma flashPNX{n:ℕ}(h:P.calibration.ℓ < n)(s:ℕ) : P.dressPuffNX (P.flash n) k j w∈ P.sensing (P.flash n).patio s k.1:=
    Submodule.subset_span (show _∈_ from ⟨_,_,_,Finset.union_subset (Finset.singleton_subset_iff.mpr (porchBorn (P.flash n))) (Finset.singleton_subset_iff.mpr (porchGone _)),le_refl _,P.pocket_gap s n h,P.dressPNX (P.flash n) k j w, P.nativePNX _ k j w⟩)
#print axioms flashPNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
