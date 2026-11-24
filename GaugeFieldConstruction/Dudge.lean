import GaugeFieldConstruction.Ohu
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
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
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
abbrev Incζ (y: Vulcan I n):Prop:=y.keys.toFinset=t∧ψS σ y.keys
-- parity with validity. metadata support carries proof.Algebra$_D.M.U.S`
def skimQ (U:List (Vulcan I n)):Boke n I:= U.filter (fun y=> decide (Incζ I σ t y)) -- \
abbrev pre_g (Q:Boke n I): Boke n I:= Q.filter fun e=> decide (e.seat=S)
def cacheS : InkD n:= Lee (pre_g I S (skimQ I σ t Q)) PinInk
#print cacheS
abbrev sC (U:List (Vulcan I n)) (x:Pane n):Cipher n:= (Lee U PinInk) x
variable (l:List I)
lemma Disk_version (p:ψS σ l): tipI (disks I V A Q) l= ∑ X∈ V.powerset, cacheS I σ l.toFinset X Q A:=by
 induction Q with
 | nil=> simp only [cacheS,skimQ,pre_g,List.filter_nil]; change tipI _ _=∑ x∈_, (Lee ([]:Boke n I) PinInk) A
         simp_rw [show (Lee ([]:Boke n I) PinInk) A=0 from rfl, Finset.sum_const_zero];
         rw [show disks I V A ([]:Boke n I)= fun _=> (0: Cipher n) from funext (fun x=>map_zero _), tip_0]
 | cons i L h=>
    let L_:Key I→ Cipher n:=fun x=>RiseW (egest i V x A • (Pi.single i.val 1:PairLog (FinV n))); let D':= l.toFinset
    have he:River L_:=by
       apply (sc_V (f:=fun x:Key I=> egest i V x A • (Pi.single i.val 1:PairLog (FinV n))) (prodR (ContinuousLinearMap.lsmul ℂ ℂ) (eg_R ..) (zeroR _)) (LinearMap.toContinuousLinearMap (RiseW (G:=FinV n))))
    have ph: tipI (disks I V A (i::L)) l=tipI L_ l+tipI (disks I V A L) l:=by
       change _=_; rw [show disks I V A (i::L)=(fun z=> L_ z+disks I V A L z) from funext fun z=>by unfold disks Bore0 cryY; rw [consA,map_add]]
       exact tip_A he (γRise_P _ _ _) l
    have hx: ∑ X∈V.powerset,cacheS I σ D' X (i::L) A= (if Incζ I σ D' i ∧ i.seat ⊆ V then PinInk i A else 0)+ ∑ X∈V.powerset,cacheS I σ D' X L A:=by
       by_cases v:Incζ I σ D' i
       · rw [show (if Incζ I σ D' i ∧ i.seat⊆ V then PinInk i A else (0:Cipher n))=(if i.seat⊆V then PinInk i A else 0) from (by split_ifs <;> first|rfl|tauto),show (if i.seat⊆V then PinInk i A else (0:Cipher n))=∑ x∈V.powerset,(if i.seat=x then PinInk i A else 0) from by simp, ←sum_add_distrib]; refine sum_congr rfl fun x u=>?_
         unfold cacheS skimQ pre_g
         by_cases g:i.seat=x
         · rw [List.filter_cons,if_pos (decide_eq_true v),List.filter_cons, if_pos ?_,consA, Pi.add_apply,if_pos g]; simpa -- tune
         rw [List.filter_cons,if_pos (decide_eq_true v),List.filter_cons,if_neg ?_,if_neg g,zero_add]; simpa

       unfold cacheS skimQ; simp_rw [List.filter_cons]; simp only [v,and_false,false_and, decide_false, Bool.false_eq_true,↓reduceIte,zero_add]
    rw [ph,h,hx]; apply congrArg (·+_)
    by_cases s:i.seat⊆ V; swap; · rw [if_neg (by simp [s]),show L_=(fun _=>0) from funext fun k=>by unfold L_ egest; rw [if_neg s,zero_smul,map_zero],tip_0]
    let T:= PinInk i A; let P:= i.keys
    have hV:L_=GJ.stalk i.keys T:=by
       funext k; unfold L_ egest; rw [if_pos s,map_smul]; rw [show RiseW (Pi.single i.val 1)=upperW i.val from ?_]; change ((P.map k).prod • i.amt A) • _= (P.map k).prod • (i.amt A • _); simp only [smul_eq_mul,mul_smul]
       change ∑ j,(Pi.single _ _) _ • _ = _; rw [sum_eq_single i.val]; simp; intro k _ h; simp [h]; simp
    by_cases y:ψS σ P
    · have hy:GJ.stalk i.keys T=(fun z=>pine i.keys.toFinset z • T):=funext (fun z=> congrArg (· • T) (List.prod_toFinset _ (List.Nodup.of_map σ y)).symm) -- tune
      rw [hV,hy,tip_tape l (List.Nodup.of_map σ p)]; change _= if _ then T else _; unfold Incζ; simp only [show ψS σ i.keys from y,s,and_true,true_and]; simp only [D',eq_comm]; try congr 1
    rw [hV,noStem σ i.keys l y p T,if_neg fun h=> y h.1.2]

-- inject over cuts. whenever result intertwines linear sum. compare transformed supports W=cut, requirement over incidence. Use linear add.
lemma cache_H (X:Support (More n)) (f:Finset (Seat n)→Cipher n)(h:∀x⊆X,∑ i∈x.powerset,f i=0): f X=0:=by
 induction X using Finset.strongInductionOn with| _ X ih=> have he:= h X (Finset.Subset.refl _); rw [Finset.sum_eq_single X] at he; exact he; intro i t p; exact ih i (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp t,p⟩) (fun i' t'=>h i' (Subset.trans t' (mem_powerset.mp t))); intro g; exact False.elim (g (mem_powerset.mpr (Finset.Subset.refl _)))
variable (W: Equiv (Seat n) (Seat n))(σ':I→Seat n)(Q':Boke n I)(A':Pane n) (G: Cipher n→+Cipher n)
local notation "ℓW" X:max=> Finset.map W.toEmbedding X
lemma basic_gain (p:ψS σ l)(v:ψS σ' l)(h:∀ X:Support (More n),tipI (disks I (ℓW X) A' Q') l=G (tipI (disks I X A Q) l)):cacheS I σ' l.toFinset (ℓW V) Q' A'= G (cacheS I σ l.toFinset V Q A):=by
 apply sub_eq_zero.mp; refine cache_H V (fun X=>cacheS I σ' l.toFinset (ℓW X) Q' A' - G (cacheS I σ l.toFinset X Q A)) fun X _=> ?_; let D:= l.toFinset; let L:=fun Y=> cacheS I σ' D Y Q' A'; have he:=h X; rw [Disk_version I σ' (ℓW X) A' Q' l v,Disk_version I σ X A Q l p, map_sum G] at he
 rw [sum_sub_distrib]; apply sub_eq_zero.mpr; refine Eq.trans ?_ he; change (∑ i∈X.powerset,L (ℓW i))=∑ i∈(ℓW X).powerset,L i; refine Finset.sum_bij (fun i _=>ℓW i) (fun i s=> mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp s))) (fun i _ j _ t=>map_injective _ t) (fun x u=>⟨x.map W.symm.toEmbedding,mem_powerset.mpr (?_),?_⟩) (fun _ _=> rfl)
 · have hx : ((ℓW X).map W.symm.toEmbedding)=X:=by ext; simp
   simpa only [hx] using (show x.map W.symm.toEmbedding⊆ (ℓW X).map W.symm.toEmbedding from Finset.map_subset_map.mpr (mem_powerset.mp u))
 ext; simp
#print axioms Disk_version
end MastTin
end YM.CF.XGarden
end
